use crate::params::{get_params, OptimizationType};
use crate::reduce::{bigint_to_basefield, limbs_to_bigint, Reducer};
use crate::AllocatedNonNativeFieldMulResultVar;
use ark_ff::{BigInteger, FpParameters, PrimeField};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::ToConstraintFieldGadget;
use ark_relations::r1cs::{OptimizationGoal, Result as R1CSResult};
use ark_relations::{
    ns,
    r1cs::{ConstraintSystemRef, Namespace, SynthesisError},
};
use ark_std::cmp::{max, min};
use ark_std::marker::PhantomData;
use ark_std::{borrow::Borrow, vec, vec::Vec};

/// The allocated version of `NonNativeFieldVar` (introduced below)
#[derive(Debug)]
#[must_use]
pub struct AllocatedNonNativeFieldVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// Constraint system reference
    pub cs: ConstraintSystemRef<BaseField>,
    /// The limbs, each of which is a BaseField gadget.
    pub limbs: Vec<FpVar<BaseField>>,
    /// Number of additions done over this gadget, using which the gadget decides when to reduce.
    pub num_of_additions_over_normal_form: BaseField,
    /// Whether the limb representation is the normal form (using only the bits specified in the parameters, and the representation is strictly within the range of TargetField).
    pub is_in_the_normal_form: bool,
    #[doc(hidden)]
    pub target_phantom: PhantomData<TargetField>,
}

impl<TargetField: PrimeField, BaseField: PrimeField>
    AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    /// Return cs
    pub fn cs(&self) -> ConstraintSystemRef<BaseField> {
        self.cs.clone()
    }

    /// Obtain the value of limbs
    pub fn limbs_to_value(
        limbs: Vec<BaseField>,
        optimization_type: OptimizationType,
    ) -> TargetField {
        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            optimization_type,
        );

        let mut base_repr: <TargetField as PrimeField>::BigInt = TargetField::one().into_repr();

        // Convert 2^{(params.bits_per_limb - 1)} into the TargetField and then double the base
        // This is because 2^{(params.bits_per_limb)} might indeed be larger than the target field's prime.
        base_repr.muln((params.bits_per_limb - 1) as u32);
        let mut base: TargetField = TargetField::from_repr(base_repr).unwrap();
        base = base + &base;

        let mut result = TargetField::zero();
        let mut power = TargetField::one();

        for limb in limbs.iter().rev() {
            let mut val = TargetField::zero();
            let mut cur = TargetField::one();

            for bit in limb.into_repr().to_bits_be().iter().rev() {
                if *bit {
                    val += &cur;
                }
                cur.double_in_place();
            }

            result += &(val * power);
            power *= &base;
        }

        result
    }

    /// Obtain the value of a nonnative field element
    pub fn value(&self) -> R1CSResult<TargetField> {
        let mut limbs = Vec::new();
        for limb in self.limbs.iter() {
            limbs.push(limb.value()?);
        }

        Ok(Self::limbs_to_value(limbs, self.get_optimization_type()))
    }

    /// Obtain the nonnative field element of a constant value
    pub fn constant(cs: ConstraintSystemRef<BaseField>, value: TargetField) -> R1CSResult<Self> {
        let optimization_type = match cs.optimization_goal() {
            OptimizationGoal::None => OptimizationType::Constraints,
            OptimizationGoal::Constraints => OptimizationType::Constraints,
            OptimizationGoal::Weight => OptimizationType::Weight,
        };

        let limbs_value = Self::get_limbs_representations(&value, optimization_type)?;

        let mut limbs = Vec::new();

        for limb_value in limbs_value.iter() {
            limbs.push(FpVar::<BaseField>::new_constant(
                ns!(cs, "limb"),
                limb_value,
            )?);
        }

        Ok(Self {
            cs,
            limbs,
            num_of_additions_over_normal_form: BaseField::zero(),
            is_in_the_normal_form: true,
            target_phantom: PhantomData,
        })
    }

    /// Obtain the nonnative field element of one
    pub fn one(cs: ConstraintSystemRef<BaseField>) -> R1CSResult<Self> {
        Self::constant(cs, TargetField::one())
    }

    /// Obtain the nonnative field element of zero
    pub fn zero(cs: ConstraintSystemRef<BaseField>) -> R1CSResult<Self> {
        Self::constant(cs, TargetField::zero())
    }

    /// Add a nonnative field element
    #[tracing::instrument(target = "r1cs")]
    pub fn add(&self, other: &Self) -> R1CSResult<Self> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let mut limbs = Vec::new();
        for (this_limb, other_limb) in self.limbs.iter().zip(other.limbs.iter()) {
            limbs.push(this_limb + other_limb);
        }

        let mut res = Self {
            cs: self.cs(),
            limbs,
            num_of_additions_over_normal_form: self
                .num_of_additions_over_normal_form
                .add(&other.num_of_additions_over_normal_form)
                .add(&BaseField::one()),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        Reducer::<TargetField, BaseField>::post_add_reduce(&mut res)?;
        Ok(res)
    }

    /// Add a constant
    #[tracing::instrument(target = "r1cs")]
    pub fn add_constant(&self, other: &TargetField) -> R1CSResult<Self> {
        let other_limbs = Self::get_limbs_representations(other, self.get_optimization_type())?;

        let mut limbs = Vec::new();
        for (this_limb, other_limb) in self.limbs.iter().zip(other_limbs.iter()) {
            limbs.push(this_limb + *other_limb);
        }

        let mut res = Self {
            cs: self.cs(),
            limbs,
            num_of_additions_over_normal_form: self
                .num_of_additions_over_normal_form
                .add(&BaseField::one()),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        Reducer::<TargetField, BaseField>::post_add_reduce(&mut res)?;

        Ok(res)
    }

    /// Subtract a nonnative field element, without the final reduction step
    #[tracing::instrument(target = "r1cs")]
    pub fn sub_without_reduce(&self, other: &Self) -> R1CSResult<Self> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            self.get_optimization_type(),
        );

        // Step 1: reduce the `other` if needed
        let mut surfeit = overhead!(other.num_of_additions_over_normal_form + BaseField::one()) + 1;
        let mut other = other.clone();
        if (surfeit + params.bits_per_limb > BaseField::size_in_bits() - 1)
            || (surfeit
                + (TargetField::size_in_bits() - params.bits_per_limb * (params.num_limbs - 1))
                > BaseField::size_in_bits() - 1)
        {
            Reducer::reduce(&mut other)?;
            surfeit = overhead!(other.num_of_additions_over_normal_form + BaseField::one()) + 1;
        }

        // Step 2: construct the padding
        let mut pad_non_top_limb_repr: <BaseField as PrimeField>::BigInt =
            BaseField::one().into_repr();
        let mut pad_top_limb_repr: <BaseField as PrimeField>::BigInt = pad_non_top_limb_repr;

        pad_non_top_limb_repr.muln((surfeit + params.bits_per_limb) as u32);
        let pad_non_top_limb = BaseField::from_repr(pad_non_top_limb_repr).unwrap();

        pad_top_limb_repr.muln(
            (surfeit
                + (TargetField::size_in_bits() - params.bits_per_limb * (params.num_limbs - 1)))
                as u32,
        );
        let pad_top_limb = BaseField::from_repr(pad_top_limb_repr).unwrap();

        let mut pad_limbs = Vec::new();
        pad_limbs.push(pad_top_limb);
        for _ in 0..self.limbs.len() - 1 {
            pad_limbs.push(pad_non_top_limb);
        }

        // Step 3: prepare to pad the padding to k * p for some k
        let pad_to_kp_gap = Self::limbs_to_value(pad_limbs, self.get_optimization_type()).neg();
        let pad_to_kp_limbs =
            Self::get_limbs_representations(&pad_to_kp_gap, self.get_optimization_type())?;

        // Step 4: the result is self + pad + pad_to_kp - other
        let mut limbs = Vec::new();
        for (i, ((this_limb, other_limb), pad_to_kp_limb)) in self
            .limbs
            .iter()
            .zip(other.limbs.iter())
            .zip(pad_to_kp_limbs.iter())
            .enumerate()
        {
            if i != 0 {
                limbs.push(this_limb + pad_non_top_limb + *pad_to_kp_limb - other_limb);
            } else {
                limbs.push(this_limb + pad_top_limb + *pad_to_kp_limb - other_limb);
            }
        }

        let result = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs: self.cs(),
            limbs,
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form
                + (other.num_of_additions_over_normal_form + BaseField::one())
                + (other.num_of_additions_over_normal_form + BaseField::one()),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        Ok(result)
    }

    /// Subtract a nonnative field element
    #[tracing::instrument(target = "r1cs")]
    pub fn sub(&self, other: &Self) -> R1CSResult<Self> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let mut result = self.sub_without_reduce(other)?;
        Reducer::<TargetField, BaseField>::post_add_reduce(&mut result)?;
        Ok(result)
    }

    /// Subtract a constant
    #[tracing::instrument(target = "r1cs")]
    pub fn sub_constant(&self, other: &TargetField) -> R1CSResult<Self> {
        self.sub(&Self::constant(self.cs(), *other)?)
    }

    /// Multiply a nonnative field element
    #[tracing::instrument(target = "r1cs")]
    pub fn mul(&self, other: &Self) -> R1CSResult<Self> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        self.mul_without_reduce(&other)?.reduce()
    }

    /// Multiply a constant
    pub fn mul_constant(&self, other: &TargetField) -> R1CSResult<Self> {
        self.mul(&Self::constant(self.cs(), *other)?)
    }

    /// Compute the negate of a nonnative field element
    #[tracing::instrument(target = "r1cs")]
    pub fn negate(&self) -> R1CSResult<Self> {
        Self::zero(self.cs())?.sub(self)
    }

    /// Compute the inverse of a nonnative field element
    #[tracing::instrument(target = "r1cs")]
    pub fn inverse(&self) -> R1CSResult<Self> {
        let inverse = Self::new_witness(self.cs(), || {
            Ok(self.value()?.inverse().unwrap_or_else(TargetField::zero))
        })?;

        let actual_result = self.clone().mul(&inverse)?;
        actual_result.conditional_enforce_equal(&Self::one(self.cs())?, &Boolean::TRUE)?;
        Ok(inverse)
    }

    /// Convert a `TargetField` element into limbs (not constraints)
    /// This is an internal function that would be reused by a number of other functions
    pub fn get_limbs_representations(
        elem: &TargetField,
        optimization_type: OptimizationType,
    ) -> R1CSResult<Vec<BaseField>> {
        Self::get_limbs_representations_from_big_integer(&elem.into_repr(), optimization_type)
    }

    /// Obtain the limbs directly from a big int
    pub fn get_limbs_representations_from_big_integer(
        elem: &<TargetField as PrimeField>::BigInt,
        optimization_type: OptimizationType,
    ) -> R1CSResult<Vec<BaseField>> {
        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            optimization_type,
        );

        // push the lower limbs first
        let mut limbs: Vec<BaseField> = Vec::new();
        let mut cur = *elem;
        for _ in 0..params.num_limbs {
            let cur_bits = cur.to_bits_be(); // `to_bits` is big endian
            let cur_mod_r = <BaseField as PrimeField>::BigInt::from_bits_be(
                &cur_bits[cur_bits.len() - params.bits_per_limb..],
            ); // therefore, the lowest `bits_per_non_top_limb` bits is what we want.
            limbs.push(BaseField::from_repr(cur_mod_r).unwrap());
            cur.divn(params.bits_per_limb as u32);
        }

        // then we reserve, so that the limbs are ``big limb first''
        limbs.reverse();

        Ok(limbs)
    }

    /// for advanced use, multiply and output the intermediate representations (without reduction)
    /// This intermediate representations can be added with each other, and they can later be reduced back to the `NonNativeFieldVar`.
    #[tracing::instrument(target = "r1cs")]
    pub fn mul_without_reduce(
        &self,
        other: &Self,
    ) -> R1CSResult<AllocatedNonNativeFieldMulResultVar<TargetField, BaseField>> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            self.get_optimization_type(),
        );

        // Step 1: reduce `self` and `other` if neceessary
        let mut self_reduced = self.clone();
        let mut other_reduced = other.clone();
        Reducer::<TargetField, BaseField>::pre_mul_reduce(&mut self_reduced, &mut other_reduced)?;

        let mut prod_limbs = Vec::new();
        if self.get_optimization_type() == OptimizationType::Weight {
            let zero = FpVar::<BaseField>::zero();

            for _ in 0..2 * params.num_limbs - 1 {
                prod_limbs.push(zero.clone());
            }

            for i in 0..params.num_limbs {
                for j in 0..params.num_limbs {
                    prod_limbs[i + j] =
                        &prod_limbs[i + j] + (&self_reduced.limbs[i] * &other_reduced.limbs[j]);
                }
            }
        } else {
            let cs = self.cs().or(other.cs());

            for z_index in 0..2 * params.num_limbs - 1 {
                prod_limbs.push(FpVar::new_witness(ns!(cs, "limb product"), || {
                    let mut z_i = BaseField::zero();
                    for i in 0..=min(params.num_limbs - 1, z_index) {
                        let j = z_index - i;
                        if j < params.num_limbs {
                            z_i += &self_reduced.limbs[i]
                                .value()?
                                .mul(&other_reduced.limbs[j].value()?);
                        }
                    }

                    Ok(z_i)
                })?);
            }

            for c in 0..(2 * params.num_limbs - 1) {
                let c_pows: Vec<_> = (0..(2 * params.num_limbs - 1))
                    .map(|i| BaseField::from((c + 1) as u128).pow(&vec![i as u64]))
                    .collect();

                let x = self_reduced
                    .limbs
                    .iter()
                    .zip(c_pows.iter())
                    .map(|(var, c_pow)| var * *c_pow)
                    .fold(FpVar::zero(), |sum, i| sum + i);

                let y = other_reduced
                    .limbs
                    .iter()
                    .zip(c_pows.iter())
                    .map(|(var, c_pow)| var * *c_pow)
                    .fold(FpVar::zero(), |sum, i| sum + i);

                let z = prod_limbs
                    .iter()
                    .zip(c_pows.iter())
                    .map(|(var, c_pow)| var * *c_pow)
                    .fold(FpVar::zero(), |sum, i| sum + i);

                z.enforce_equal(&(x * y))?;
            }
        }

        Ok(AllocatedNonNativeFieldMulResultVar {
            cs: self.cs(),
            limbs: prod_limbs,
            prod_of_num_of_additions: (self_reduced.num_of_additions_over_normal_form
                + BaseField::one())
                * (other_reduced.num_of_additions_over_normal_form + BaseField::one()),
            target_phantom: PhantomData,
        })
    }

    pub(crate) fn frobenius_map(&self, _power: usize) -> R1CSResult<Self> {
        Ok(self.clone())
    }

    pub(crate) fn conditional_enforce_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<BaseField>,
    ) -> R1CSResult<()> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            self.get_optimization_type(),
        );

        // Get p
        let p_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations_from_big_integer(
                &<TargetField as PrimeField>::Params::MODULUS,
                self.get_optimization_type()
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut p_gadget_limbs = Vec::new();
        for limb in p_representations.iter() {
            p_gadget_limbs.push(FpVar::<BaseField>::Constant(*limb));
        }
        let p_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs: self.cs(),
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: BaseField::one(),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        // Get delta = self - other
        let cs = self.cs().or(other.cs()).or(should_enforce.cs());
        let mut delta = self.sub_without_reduce(other)?;
        delta = should_enforce.select(&delta, &Self::zero(cs.clone())?)?;

        // Allocate k = delta / p
        let k_gadget = FpVar::<BaseField>::new_witness(ns!(cs, "k"), || {
            let mut delta_limbs_values = Vec::<BaseField>::new();
            for limb in delta.limbs.iter() {
                delta_limbs_values.push(limb.value()?);
            }

            let delta_bigint = limbs_to_bigint(params.bits_per_limb, &delta_limbs_values);

            Ok(bigint_to_basefield::<BaseField>(&(delta_bigint / p_bigint)))
        })?;

        let surfeit = overhead!(delta.num_of_additions_over_normal_form + BaseField::one()) + 1;
        Reducer::<TargetField, BaseField>::limb_to_bits(&k_gadget, surfeit)?;

        // Compute k * p
        let mut kp_gadget_limbs = Vec::new();
        for limb in p_gadget.limbs.iter() {
            kp_gadget_limbs.push(limb * &k_gadget);
        }

        // Enforce delta = kp
        Reducer::<TargetField, BaseField>::group_and_check_equality(
            surfeit,
            params.bits_per_limb,
            params.bits_per_limb,
            &delta.limbs,
            &kp_gadget_limbs,
        )?;

        Ok(())
    }

    #[tracing::instrument(target = "r1cs")]
    pub(crate) fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<BaseField>,
    ) -> R1CSResult<()> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let cs = self.cs().or(other.cs()).or(should_enforce.cs());

        let _ = should_enforce
            .select(&self.sub(other)?, &Self::one(cs)?)?
            .inverse()?;

        Ok(())
    }

    pub(crate) fn get_optimization_type(&self) -> OptimizationType {
        match self.cs().optimization_goal() {
            OptimizationGoal::None => OptimizationType::Constraints,
            OptimizationGoal::Constraints => OptimizationType::Constraints,
            OptimizationGoal::Weight => OptimizationType::Weight,
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBitsGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bits_le(&self) -> R1CSResult<Vec<Boolean<BaseField>>> {
        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            self.get_optimization_type(),
        );

        // Reduce to the normal form
        // Though, a malicious prover can make it slightly larger than p
        let mut self_normal = self.clone();
        Reducer::<TargetField, BaseField>::pre_eq_reduce(&mut self_normal)?;

        // Therefore, we convert it to bits and enforce that it is in the field
        let mut bits = Vec::<Boolean<BaseField>>::new();
        for limb in self_normal.limbs.iter() {
            bits.extend_from_slice(&Reducer::<TargetField, BaseField>::limb_to_bits(
                &limb,
                params.bits_per_limb,
            )?);
        }
        bits.reverse();

        let mut b = TargetField::characteristic().to_vec();
        assert_eq!(b[0] % 2, 1);
        b[0] -= 1; // This works, because the LSB is one, so there's no borrows.
        let run = Boolean::<BaseField>::enforce_smaller_or_equal_than_le(&bits, b)?;

        // We should always end in a "run" of zeros, because
        // the characteristic is an odd prime. So, this should
        // be empty.
        assert!(run.is_empty());

        Ok(bits)
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBytesGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bytes(&self) -> R1CSResult<Vec<UInt8<BaseField>>> {
        let mut bits = self.to_bits_le()?;

        let num_bits = TargetField::BigInt::NUM_LIMBS * 64;
        assert!(bits.len() <= num_bits);
        bits.resize_with(num_bits, || Boolean::constant(false));

        let bytes = bits.chunks(8).map(UInt8::from_bits_le).collect();
        Ok(bytes)
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> CondSelectGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    #[tracing::instrument(target = "r1cs")]
    fn conditionally_select(
        cond: &Boolean<BaseField>,
        true_value: &Self,
        false_value: &Self,
    ) -> R1CSResult<Self> {
        assert_eq!(
            true_value.get_optimization_type(),
            false_value.get_optimization_type()
        );

        let mut limbs_sel = Vec::with_capacity(true_value.limbs.len());

        for (x, y) in true_value.limbs.iter().zip(&false_value.limbs) {
            limbs_sel.push(FpVar::<BaseField>::conditionally_select(cond, x, y)?);
        }

        Ok(Self {
            cs: true_value.cs().or(false_value.cs()),
            limbs: limbs_sel,
            num_of_additions_over_normal_form: max(
                true_value.num_of_additions_over_normal_form,
                false_value.num_of_additions_over_normal_form,
            ),
            is_in_the_normal_form: true_value.is_in_the_normal_form
                && false_value.is_in_the_normal_form,
            target_phantom: PhantomData,
        })
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> TwoBitLookupGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    type TableConstant = TargetField;

    #[tracing::instrument(target = "r1cs")]
    fn two_bit_lookup(
        bits: &[Boolean<BaseField>],
        constants: &[Self::TableConstant],
    ) -> R1CSResult<Self> {
        debug_assert!(bits.len() == 2);
        debug_assert!(constants.len() == 4);

        let cs = bits.cs();

        let optimization_type = match cs.optimization_goal() {
            OptimizationGoal::None => OptimizationType::Constraints,
            OptimizationGoal::Constraints => OptimizationType::Constraints,
            OptimizationGoal::Weight => OptimizationType::Weight,
        };

        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            optimization_type,
        );
        let mut limbs_constants = Vec::new();
        for _ in 0..params.num_limbs {
            limbs_constants.push(Vec::new());
        }

        for constant in constants.iter() {
            let representations =
                AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                    constant,
                    optimization_type,
                )?;

            for (i, representation) in representations.iter().enumerate() {
                limbs_constants[i].push(*representation);
            }
        }

        let mut limbs = Vec::new();
        for limbs_constant in limbs_constants.iter() {
            limbs.push(FpVar::<BaseField>::two_bit_lookup(bits, limbs_constant)?);
        }

        Ok(AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs,
            limbs,
            num_of_additions_over_normal_form: BaseField::zero(),
            is_in_the_normal_form: true,
            target_phantom: PhantomData,
        })
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ThreeBitCondNegLookupGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    type TableConstant = TargetField;

    #[tracing::instrument(target = "r1cs")]
    fn three_bit_cond_neg_lookup(
        bits: &[Boolean<BaseField>],
        b0b1: &Boolean<BaseField>,
        constants: &[Self::TableConstant],
    ) -> R1CSResult<Self> {
        debug_assert!(bits.len() == 3);
        debug_assert!(constants.len() == 4);

        let cs = bits.cs().or(b0b1.cs());

        let optimization_type = match cs.optimization_goal() {
            OptimizationGoal::None => OptimizationType::Constraints,
            OptimizationGoal::Constraints => OptimizationType::Constraints,
            OptimizationGoal::Weight => OptimizationType::Weight,
        };

        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            optimization_type,
        );

        let mut limbs_constants = Vec::new();
        for _ in 0..params.num_limbs {
            limbs_constants.push(Vec::new());
        }

        for constant in constants.iter() {
            let representations =
                AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                    constant,
                    optimization_type,
                )?;

            for (i, representation) in representations.iter().enumerate() {
                limbs_constants[i].push(*representation);
            }
        }

        let mut limbs = Vec::new();
        for limbs_constant in limbs_constants.iter() {
            limbs.push(FpVar::<BaseField>::three_bit_cond_neg_lookup(
                bits,
                b0b1,
                limbs_constant,
            )?);
        }

        Ok(AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs,
            limbs,
            num_of_additions_over_normal_form: BaseField::zero(),
            is_in_the_normal_form: true,
            target_phantom: PhantomData,
        })
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> AllocVar<TargetField, BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    fn new_variable<T: Borrow<TargetField>>(
        cs: impl Into<Namespace<BaseField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> R1CSResult<Self> {
        let ns = cs.into();
        let cs = ns.cs();

        let optimization_type = match cs.optimization_goal() {
            OptimizationGoal::None => OptimizationType::Constraints,
            OptimizationGoal::Constraints => OptimizationType::Constraints,
            OptimizationGoal::Weight => OptimizationType::Weight,
        };

        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            optimization_type,
        );
        let zero = TargetField::zero();

        let elem = match f() {
            Ok(t) => *(t.borrow()),
            Err(_) => zero,
        };
        let elem_representations = Self::get_limbs_representations(&elem, optimization_type)?;
        let mut limbs = Vec::new();

        for limb in elem_representations.iter() {
            limbs.push(FpVar::<BaseField>::new_variable(
                ark_relations::ns!(cs, "alloc"),
                || Ok(limb),
                mode,
            )?);
        }

        let num_of_additions_over_normal_form = if mode != AllocationMode::Witness {
            BaseField::zero()
        } else {
            BaseField::one()
        };

        if mode == AllocationMode::Witness {
            for limb in limbs.iter().rev().take(params.num_limbs - 1) {
                Reducer::<TargetField, BaseField>::limb_to_bits(limb, params.bits_per_limb)?;
            }

            Reducer::<TargetField, BaseField>::limb_to_bits(
                &limbs[0],
                TargetField::size_in_bits() - (params.num_limbs - 1) * params.bits_per_limb,
            )?;
        }

        Ok(Self {
            cs,
            limbs,
            num_of_additions_over_normal_form,
            is_in_the_normal_form: mode != AllocationMode::Witness,
            target_phantom: PhantomData,
        })
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToConstraintFieldGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    fn to_constraint_field(&self) -> R1CSResult<Vec<FpVar<BaseField>>> {
        // provide a unique representation of the nonnative variable
        // step 1: convert it into a bit sequence
        let bits = self.to_bits_le()?;

        // step 2: obtain the parameters for weight-optimized (often, fewer limbs)
        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            OptimizationType::Weight,
        );

        // step 3: assemble the limbs
        let mut limbs = bits
            .chunks(params.bits_per_limb)
            .map(|chunk| {
                let mut limb = FpVar::<BaseField>::zero();
                let mut w = BaseField::one();
                for b in chunk.iter() {
                    limb += FpVar::from(b.clone()) * w;
                    w.double_in_place();
                }
                limb
            })
            .collect::<Vec<FpVar<BaseField>>>();

        limbs.reverse();

        // step 4: output the limbs
        Ok(limbs)
    }
}

/*
 * Implementation of a few traits
 */

impl<TargetField: PrimeField, BaseField: PrimeField> Clone
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    fn clone(&self) -> Self {
        AllocatedNonNativeFieldVar {
            cs: self.cs(),
            limbs: self.limbs.clone(),
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form,
            is_in_the_normal_form: self.is_in_the_normal_form,
            target_phantom: PhantomData,
        }
    }
}
