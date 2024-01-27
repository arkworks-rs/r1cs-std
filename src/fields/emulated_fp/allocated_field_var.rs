use super::{
    params::{get_params, OptimizationType},
    reduce::{bigint_to_basefield, limbs_to_bigint, Reducer},
    AllocatedMulResultVar,
};
use crate::{
    convert::{ToBitsGadget, ToBytesGadget, ToConstraintFieldGadget},
    fields::fp::FpVar,
    prelude::*,
};
use ark_ff::{BigInteger, PrimeField};
use ark_relations::{
    ns,
    r1cs::{
        ConstraintSystemRef, Namespace, OptimizationGoal, Result as R1CSResult, SynthesisError,
    },
};
use ark_std::{
    borrow::Borrow,
    cmp::{max, min},
    marker::PhantomData,
    vec,
    vec::Vec,
};

/// The allocated version of `EmulatedFpVar` (introduced below)
#[derive(Debug)]
#[must_use]
pub struct AllocatedEmulatedFpVar<TargetF: PrimeField, BaseF: PrimeField> {
    /// Constraint system reference
    pub cs: ConstraintSystemRef<BaseF>,
    /// The limbs, each of which is a BaseF gadget.
    pub limbs: Vec<FpVar<BaseF>>,
    /// Number of additions done over this gadget, using which the gadget
    /// decides when to reduce.
    pub num_of_additions_over_normal_form: BaseF,
    /// Whether the limb representation is the normal form (using only the bits
    /// specified in the parameters, and the representation is strictly within
    /// the range of TargetF).
    pub is_in_the_normal_form: bool,
    #[doc(hidden)]
    pub target_phantom: PhantomData<TargetF>,
}

impl<TargetF: PrimeField, BaseF: PrimeField> AllocatedEmulatedFpVar<TargetF, BaseF> {
    /// Return cs
    pub fn cs(&self) -> ConstraintSystemRef<BaseF> {
        self.cs.clone()
    }

    /// Obtain the value of limbs
    pub fn limbs_to_value(limbs: Vec<BaseF>, optimization_type: OptimizationType) -> TargetF {
        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            optimization_type,
        );

        // Convert 2^{(params.bits_per_limb - 1)} into the TargetF and then double
        // the base This is because 2^{(params.bits_per_limb)} might indeed be
        // larger than the target field's prime.
        let base_repr = TargetF::ONE.into_bigint() << (params.bits_per_limb - 1) as u32;

        let mut base = TargetF::from_bigint(base_repr).unwrap();
        base.double_in_place();

        let mut result = TargetF::zero();
        let mut power = TargetF::one();

        for limb in limbs.iter().rev() {
            let mut val = TargetF::zero();
            let mut cur = TargetF::one();

            for bit in limb.into_bigint().to_bits_be().iter().rev() {
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

    /// Obtain the value of a emulated field element
    pub fn value(&self) -> R1CSResult<TargetF> {
        let mut limbs = Vec::new();
        for limb in self.limbs.iter() {
            limbs.push(limb.value()?);
        }

        Ok(Self::limbs_to_value(limbs, self.get_optimization_type()))
    }

    /// Obtain the emulated field element of a constant value
    pub fn constant(cs: ConstraintSystemRef<BaseF>, value: TargetF) -> R1CSResult<Self> {
        let optimization_type = match cs.optimization_goal() {
            OptimizationGoal::None => OptimizationType::Constraints,
            OptimizationGoal::Constraints => OptimizationType::Constraints,
            OptimizationGoal::Weight => OptimizationType::Weight,
        };

        let limbs_value = Self::get_limbs_representations(&value, optimization_type)?;

        let mut limbs = Vec::new();

        for limb_value in limbs_value.iter() {
            limbs.push(FpVar::<BaseF>::new_constant(ns!(cs, "limb"), limb_value)?);
        }

        Ok(Self {
            cs,
            limbs,
            num_of_additions_over_normal_form: BaseF::zero(),
            is_in_the_normal_form: true,
            target_phantom: PhantomData,
        })
    }

    /// Obtain the emulated field element of one
    pub fn one(cs: ConstraintSystemRef<BaseF>) -> R1CSResult<Self> {
        Self::constant(cs, TargetF::one())
    }

    /// Obtain the emulated field element of zero
    pub fn zero(cs: ConstraintSystemRef<BaseF>) -> R1CSResult<Self> {
        Self::constant(cs, TargetF::zero())
    }

    /// Add a emulated field element
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
                .add(&BaseF::one()),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        Reducer::<TargetF, BaseF>::post_add_reduce(&mut res)?;
        Ok(res)
    }

    /// Add a constant
    #[tracing::instrument(target = "r1cs")]
    pub fn add_constant(&self, other: &TargetF) -> R1CSResult<Self> {
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
                .add(&BaseF::one()),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        Reducer::<TargetF, BaseF>::post_add_reduce(&mut res)?;

        Ok(res)
    }

    /// Subtract a emulated field element, without the final reduction step
    #[tracing::instrument(target = "r1cs")]
    pub fn sub_without_reduce(&self, other: &Self) -> R1CSResult<Self> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            self.get_optimization_type(),
        );

        // Step 1: reduce the `other` if needed
        let mut surfeit = overhead!(other.num_of_additions_over_normal_form + BaseF::one()) + 1;
        let mut other = other.clone();
        if (surfeit + params.bits_per_limb > BaseF::MODULUS_BIT_SIZE as usize - 1)
            || (surfeit
                + (TargetF::MODULUS_BIT_SIZE as usize
                    - params.bits_per_limb * (params.num_limbs - 1))
                > BaseF::MODULUS_BIT_SIZE as usize - 1)
        {
            Reducer::reduce(&mut other)?;
            surfeit = overhead!(other.num_of_additions_over_normal_form + BaseF::ONE) + 1;
        }

        // Step 2: construct the padding
        let mut pad_non_top_limb = BaseF::ONE.into_bigint();
        let mut pad_top_limb = pad_non_top_limb;

        pad_non_top_limb <<= (surfeit + params.bits_per_limb) as u32;
        let pad_non_top_limb = BaseF::from_bigint(pad_non_top_limb).unwrap();

        pad_top_limb <<= (surfeit + TargetF::MODULUS_BIT_SIZE as usize
            - params.bits_per_limb * (params.num_limbs - 1)) as u32;
        let pad_top_limb = BaseF::from_bigint(pad_top_limb).unwrap();

        let mut pad_limbs = Vec::with_capacity(self.limbs.len());
        pad_limbs.push(pad_top_limb);
        for _ in 0..self.limbs.len() - 1 {
            pad_limbs.push(pad_non_top_limb);
        }

        // Step 3: prepare to pad the padding to k * p for some k
        let pad_to_kp_gap = Self::limbs_to_value(pad_limbs, self.get_optimization_type()).neg();
        let pad_to_kp_limbs =
            Self::get_limbs_representations(&pad_to_kp_gap, self.get_optimization_type())?;

        // Step 4: the result is self + pad + pad_to_kp - other
        let mut limbs = Vec::with_capacity(self.limbs.len());
        for (i, ((this_limb, other_limb), pad_to_kp_limb)) in self
            .limbs
            .iter()
            .zip(&other.limbs)
            .zip(&pad_to_kp_limbs)
            .enumerate()
        {
            if i != 0 {
                limbs.push(this_limb + pad_non_top_limb + *pad_to_kp_limb - other_limb);
            } else {
                limbs.push(this_limb + pad_top_limb + *pad_to_kp_limb - other_limb);
            }
        }

        let result = AllocatedEmulatedFpVar::<TargetF, BaseF> {
            cs: self.cs(),
            limbs,
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form
                + (other.num_of_additions_over_normal_form + BaseF::one())
                + (other.num_of_additions_over_normal_form + BaseF::one()),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        Ok(result)
    }

    /// Subtract a emulated field element
    #[tracing::instrument(target = "r1cs")]
    pub fn sub(&self, other: &Self) -> R1CSResult<Self> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let mut result = self.sub_without_reduce(other)?;
        Reducer::<TargetF, BaseF>::post_add_reduce(&mut result)?;
        Ok(result)
    }

    /// Subtract a constant
    #[tracing::instrument(target = "r1cs")]
    pub fn sub_constant(&self, other: &TargetF) -> R1CSResult<Self> {
        self.sub(&Self::constant(self.cs(), *other)?)
    }

    /// Multiply a emulated field element
    #[tracing::instrument(target = "r1cs")]
    pub fn mul(&self, other: &Self) -> R1CSResult<Self> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        self.mul_without_reduce(&other)?.reduce()
    }

    /// Multiply a constant
    pub fn mul_constant(&self, other: &TargetF) -> R1CSResult<Self> {
        self.mul(&Self::constant(self.cs(), *other)?)
    }

    /// Compute the negate of a emulated field element
    #[tracing::instrument(target = "r1cs")]
    pub fn negate(&self) -> R1CSResult<Self> {
        Self::zero(self.cs())?.sub(self)
    }

    /// Compute the inverse of a emulated field element
    #[tracing::instrument(target = "r1cs")]
    pub fn inverse(&self) -> R1CSResult<Self> {
        let inverse = Self::new_witness(self.cs(), || {
            Ok(self.value()?.inverse().unwrap_or_else(TargetF::zero))
        })?;

        let actual_result = self.clone().mul(&inverse)?;
        actual_result.conditional_enforce_equal(&Self::one(self.cs())?, &Boolean::TRUE)?;
        Ok(inverse)
    }

    /// Convert a `TargetF` element into limbs (not constraints)
    /// This is an internal function that would be reused by a number of other
    /// functions
    pub fn get_limbs_representations(
        elem: &TargetF,
        optimization_type: OptimizationType,
    ) -> R1CSResult<Vec<BaseF>> {
        Self::get_limbs_representations_from_big_integer(&elem.into_bigint(), optimization_type)
    }

    /// Obtain the limbs directly from a big int
    pub fn get_limbs_representations_from_big_integer(
        elem: &<TargetF as PrimeField>::BigInt,
        optimization_type: OptimizationType,
    ) -> R1CSResult<Vec<BaseF>> {
        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            optimization_type,
        );

        // push the lower limbs first
        let mut limbs: Vec<BaseF> = Vec::new();
        let mut cur = *elem;
        for _ in 0..params.num_limbs {
            let cur_bits = cur.to_bits_be(); // `to_bits` is big endian
            let cur_mod_r = <BaseF as PrimeField>::BigInt::from_bits_be(
                &cur_bits[cur_bits.len() - params.bits_per_limb..],
            ); // therefore, the lowest `bits_per_non_top_limb` bits is what we want.
            limbs.push(BaseF::from_bigint(cur_mod_r).unwrap());
            cur >>= params.bits_per_limb as u32;
        }

        // then we reserve, so that the limbs are ``big limb first''
        limbs.reverse();

        Ok(limbs)
    }

    /// for advanced use, multiply and output the intermediate representations
    /// (without reduction) This intermediate representations can be added
    /// with each other, and they can later be reduced back to the
    /// `EmulatedFpVar`.
    #[tracing::instrument(target = "r1cs")]
    pub fn mul_without_reduce(
        &self,
        other: &Self,
    ) -> R1CSResult<AllocatedMulResultVar<TargetF, BaseF>> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            self.get_optimization_type(),
        );

        // Step 1: reduce `self` and `other` if neceessary
        let mut self_reduced = self.clone();
        let mut other_reduced = other.clone();
        Reducer::<TargetF, BaseF>::pre_mul_reduce(&mut self_reduced, &mut other_reduced)?;

        let mut prod_limbs = Vec::new();
        if self.get_optimization_type() == OptimizationType::Weight {
            let zero = FpVar::<BaseF>::zero();

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
                    let mut z_i = BaseF::zero();
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
                    .map(|i| BaseF::from((c + 1) as u128).pow(&vec![i as u64]))
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

        Ok(AllocatedMulResultVar {
            cs: self.cs(),
            limbs: prod_limbs,
            prod_of_num_of_additions: (self_reduced.num_of_additions_over_normal_form
                + BaseF::one())
                * (other_reduced.num_of_additions_over_normal_form + BaseF::one()),
            target_phantom: PhantomData,
        })
    }

    pub(crate) fn frobenius_map(&self, _power: usize) -> R1CSResult<Self> {
        Ok(self.clone())
    }

    pub(crate) fn conditional_enforce_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<BaseF>,
    ) -> R1CSResult<()> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            self.get_optimization_type(),
        );

        // Get p
        let p_representations =
            AllocatedEmulatedFpVar::<TargetF, BaseF>::get_limbs_representations_from_big_integer(
                &<TargetF as PrimeField>::MODULUS,
                self.get_optimization_type(),
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut p_gadget_limbs = Vec::new();
        for limb in p_representations.iter() {
            p_gadget_limbs.push(FpVar::<BaseF>::Constant(*limb));
        }
        let p_gadget = AllocatedEmulatedFpVar::<TargetF, BaseF> {
            cs: self.cs(),
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: BaseF::one(),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        // Get delta = self - other
        let cs = self.cs().or(other.cs()).or(should_enforce.cs());
        let mut delta = self.sub_without_reduce(other)?;
        delta = should_enforce.select(&delta, &Self::zero(cs.clone())?)?;

        // Allocate k = delta / p
        let k_gadget = FpVar::<BaseF>::new_witness(ns!(cs, "k"), || {
            let mut delta_limbs_values = Vec::<BaseF>::new();
            for limb in delta.limbs.iter() {
                delta_limbs_values.push(limb.value()?);
            }

            let delta_bigint = limbs_to_bigint(params.bits_per_limb, &delta_limbs_values);

            Ok(bigint_to_basefield::<BaseF>(&(delta_bigint / p_bigint)))
        })?;

        let surfeit = overhead!(delta.num_of_additions_over_normal_form + BaseF::one()) + 1;
        Reducer::<TargetF, BaseF>::limb_to_bits(&k_gadget, surfeit)?;

        // Compute k * p
        let mut kp_gadget_limbs = Vec::new();
        for limb in p_gadget.limbs.iter() {
            kp_gadget_limbs.push(limb * &k_gadget);
        }

        // Enforce delta = kp
        Reducer::<TargetF, BaseF>::group_and_check_equality(
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
        should_enforce: &Boolean<BaseF>,
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

    /// Allocates a new variable, but does not check that the allocation's limbs
    /// are in-range.
    fn new_variable_unchecked<T: Borrow<TargetF>>(
        cs: impl Into<Namespace<BaseF>>,
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

        let zero = TargetF::zero();

        let elem = match f() {
            Ok(t) => *(t.borrow()),
            Err(_) => zero,
        };
        let elem_representations = Self::get_limbs_representations(&elem, optimization_type)?;
        let mut limbs = Vec::new();

        for limb in elem_representations.iter() {
            limbs.push(FpVar::<BaseF>::new_variable(
                ark_relations::ns!(cs, "alloc"),
                || Ok(limb),
                mode,
            )?);
        }

        let num_of_additions_over_normal_form = if mode != AllocationMode::Witness {
            BaseF::zero()
        } else {
            BaseF::one()
        };

        Ok(Self {
            cs,
            limbs,
            num_of_additions_over_normal_form,
            is_in_the_normal_form: mode != AllocationMode::Witness,
            target_phantom: PhantomData,
        })
    }

    /// Check that this element is in-range; i.e., each limb is in-range, and
    /// the whole number is less than the modulus.
    ///
    /// Returns the bits of the element, in little-endian form
    fn enforce_in_range(&self, cs: impl Into<Namespace<BaseF>>) -> R1CSResult<Vec<Boolean<BaseF>>> {
        let ns = cs.into();
        let cs = ns.cs();
        let optimization_type = match cs.optimization_goal() {
            OptimizationGoal::None => OptimizationType::Constraints,
            OptimizationGoal::Constraints => OptimizationType::Constraints,
            OptimizationGoal::Weight => OptimizationType::Weight,
        };
        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            optimization_type,
        );
        let mut bits = Vec::new();
        for limb in self.limbs.iter().rev().take(params.num_limbs - 1) {
            bits.extend(
                Reducer::<TargetF, BaseF>::limb_to_bits(limb, params.bits_per_limb)?
                    .into_iter()
                    .rev(),
            );
        }

        bits.extend(
            Reducer::<TargetF, BaseF>::limb_to_bits(
                &self.limbs[0],
                TargetF::MODULUS_BIT_SIZE as usize - (params.num_limbs - 1) * params.bits_per_limb,
            )?
            .into_iter()
            .rev(),
        );
        Ok(bits)
    }

    /// Allocates a new non-native field witness with value given by the
    /// function `f`.  Enforces that the field element has value in `[0, modulus)`,
    /// and returns the bits of its binary representation.
    /// The bits are in little-endian (i.e., the bit at index 0 is the LSB) and the
    /// bit-vector is empty in non-witness allocation modes.
    pub fn new_witness_with_le_bits<T: Borrow<TargetF>>(
        cs: impl Into<Namespace<BaseF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
    ) -> R1CSResult<(Self, Vec<Boolean<BaseF>>)> {
        let ns = cs.into();
        let cs = ns.cs();
        let this = Self::new_variable_unchecked(ns!(cs, "alloc"), f, AllocationMode::Witness)?;
        let bits = this.enforce_in_range(ns!(cs, "bits"))?;
        Ok((this, bits))
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> ToBitsGadget<BaseF>
    for AllocatedEmulatedFpVar<TargetF, BaseF>
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bits_le(&self) -> R1CSResult<Vec<Boolean<BaseF>>> {
        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            self.get_optimization_type(),
        );

        // Reduce to the normal form
        // Though, a malicious prover can make it slightly larger than p
        let mut self_normal = self.clone();
        Reducer::<TargetF, BaseF>::pre_eq_reduce(&mut self_normal)?;

        // Therefore, we convert it to bits and enforce that it is in the field
        let mut bits = Vec::<Boolean<BaseF>>::new();
        for limb in self_normal.limbs.iter() {
            bits.extend_from_slice(&Reducer::<TargetF, BaseF>::limb_to_bits(
                &limb,
                params.bits_per_limb,
            )?);
        }
        bits.reverse();

        let mut b = TargetF::characteristic().to_vec();
        assert_eq!(b[0] % 2, 1);
        b[0] -= 1; // This works, because the LSB is one, so there's no borrows.
        let run = Boolean::<BaseF>::enforce_smaller_or_equal_than_le(&bits, b)?;

        // We should always end in a "run" of zeros, because
        // the characteristic is an odd prime. So, this should
        // be empty.
        assert!(run.is_empty());

        Ok(bits)
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> ToBytesGadget<BaseF>
    for AllocatedEmulatedFpVar<TargetF, BaseF>
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bytes_le(&self) -> R1CSResult<Vec<UInt8<BaseF>>> {
        let mut bits = self.to_bits_le()?;

        let num_bits = TargetF::BigInt::NUM_LIMBS * 64;
        assert!(bits.len() <= num_bits);
        bits.resize_with(num_bits, || Boolean::FALSE);

        let bytes = bits.chunks(8).map(UInt8::from_bits_le).collect();
        Ok(bytes)
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> CondSelectGadget<BaseF>
    for AllocatedEmulatedFpVar<TargetF, BaseF>
{
    #[tracing::instrument(target = "r1cs")]
    fn conditionally_select(
        cond: &Boolean<BaseF>,
        true_value: &Self,
        false_value: &Self,
    ) -> R1CSResult<Self> {
        assert_eq!(
            true_value.get_optimization_type(),
            false_value.get_optimization_type()
        );

        let mut limbs_sel = Vec::with_capacity(true_value.limbs.len());

        for (x, y) in true_value.limbs.iter().zip(&false_value.limbs) {
            limbs_sel.push(FpVar::<BaseF>::conditionally_select(cond, x, y)?);
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

impl<TargetF: PrimeField, BaseF: PrimeField> TwoBitLookupGadget<BaseF>
    for AllocatedEmulatedFpVar<TargetF, BaseF>
{
    type TableConstant = TargetF;

    #[tracing::instrument(target = "r1cs")]
    fn two_bit_lookup(
        bits: &[Boolean<BaseF>],
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
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            optimization_type,
        );
        let mut limbs_constants = Vec::new();
        for _ in 0..params.num_limbs {
            limbs_constants.push(Vec::new());
        }

        for constant in constants.iter() {
            let representations =
                AllocatedEmulatedFpVar::<TargetF, BaseF>::get_limbs_representations(
                    constant,
                    optimization_type,
                )?;

            for (i, representation) in representations.iter().enumerate() {
                limbs_constants[i].push(*representation);
            }
        }

        let mut limbs = Vec::new();
        for limbs_constant in limbs_constants.iter() {
            limbs.push(FpVar::<BaseF>::two_bit_lookup(bits, limbs_constant)?);
        }

        Ok(AllocatedEmulatedFpVar::<TargetF, BaseF> {
            cs,
            limbs,
            num_of_additions_over_normal_form: BaseF::zero(),
            is_in_the_normal_form: true,
            target_phantom: PhantomData,
        })
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> ThreeBitCondNegLookupGadget<BaseF>
    for AllocatedEmulatedFpVar<TargetF, BaseF>
{
    type TableConstant = TargetF;

    #[tracing::instrument(target = "r1cs")]
    fn three_bit_cond_neg_lookup(
        bits: &[Boolean<BaseF>],
        b0b1: &Boolean<BaseF>,
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
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            optimization_type,
        );

        let mut limbs_constants = Vec::new();
        for _ in 0..params.num_limbs {
            limbs_constants.push(Vec::new());
        }

        for constant in constants.iter() {
            let representations =
                AllocatedEmulatedFpVar::<TargetF, BaseF>::get_limbs_representations(
                    constant,
                    optimization_type,
                )?;

            for (i, representation) in representations.iter().enumerate() {
                limbs_constants[i].push(*representation);
            }
        }

        let mut limbs = Vec::new();
        for limbs_constant in limbs_constants.iter() {
            limbs.push(FpVar::<BaseF>::three_bit_cond_neg_lookup(
                bits,
                b0b1,
                limbs_constant,
            )?);
        }

        Ok(AllocatedEmulatedFpVar::<TargetF, BaseF> {
            cs,
            limbs,
            num_of_additions_over_normal_form: BaseF::zero(),
            is_in_the_normal_form: true,
            target_phantom: PhantomData,
        })
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> AllocVar<TargetF, BaseF>
    for AllocatedEmulatedFpVar<TargetF, BaseF>
{
    fn new_variable<T: Borrow<TargetF>>(
        cs: impl Into<Namespace<BaseF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> R1CSResult<Self> {
        let ns = cs.into();
        let cs = ns.cs();
        let this = Self::new_variable_unchecked(ns!(cs, "alloc"), f, mode)?;
        if mode == AllocationMode::Witness {
            this.enforce_in_range(ns!(cs, "bits"))?;
        }
        Ok(this)
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> ToConstraintFieldGadget<BaseF>
    for AllocatedEmulatedFpVar<TargetF, BaseF>
{
    fn to_constraint_field(&self) -> R1CSResult<Vec<FpVar<BaseF>>> {
        // provide a unique representation of the emulated variable
        // step 1: convert it into a bit sequence
        let bits = self.to_bits_le()?;

        // step 2: obtain the parameters for weight-optimized (often, fewer limbs)
        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            OptimizationType::Weight,
        );

        // step 3: assemble the limbs
        let mut limbs = bits
            .chunks(params.bits_per_limb)
            .map(|chunk| {
                let mut limb = FpVar::<BaseF>::zero();
                let mut w = BaseF::one();
                for b in chunk.iter() {
                    limb += FpVar::from(b.clone()) * w;
                    w.double_in_place();
                }
                limb
            })
            .collect::<Vec<FpVar<BaseF>>>();

        limbs.reverse();

        // step 4: output the limbs
        Ok(limbs)
    }
}

// Implementation of a few traits

impl<TargetF: PrimeField, BaseF: PrimeField> Clone for AllocatedEmulatedFpVar<TargetF, BaseF> {
    fn clone(&self) -> Self {
        AllocatedEmulatedFpVar {
            cs: self.cs(),
            limbs: self.limbs.clone(),
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form,
            is_in_the_normal_form: self.is_in_the_normal_form,
            target_phantom: PhantomData,
        }
    }
}
