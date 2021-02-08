use crate::params::get_params;
use crate::{overhead, AllocatedNonNativeFieldVar};
use ark_ff::{biginteger::BigInteger, fields::FpParameters, BitIteratorBE, One, PrimeField, Zero};
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::{alloc::AllocVar, boolean::Boolean, R1CSVar};
use ark_relations::{
    ns,
    r1cs::{ConstraintSystemRef, Result as R1CSResult},
};
use ark_std::{cmp::min, marker::PhantomData, vec, vec::Vec};
use num_bigint::BigUint;
use num_integer::Integer;

pub fn limbs_to_bigint<BaseField: PrimeField>(
    bits_per_limb: usize,
    limbs: &[BaseField],
) -> BigUint {
    let mut val = BigUint::zero();
    let mut big_cur = BigUint::one();
    let two = BigUint::from(2u32);
    for limb in limbs.iter().rev() {
        let limb_repr = limb.into_repr().to_bits_le();
        let mut small_cur = big_cur.clone();
        for limb_bit in limb_repr.iter() {
            if *limb_bit {
                val += &small_cur;
            }
            small_cur *= 2u32;
        }
        big_cur *= two.pow(bits_per_limb as u32);
    }

    val
}

pub fn bigint_to_basefield<BaseField: PrimeField>(bigint: &BigUint) -> BaseField {
    let mut val = BaseField::zero();
    let mut cur = BaseField::one();
    let bytes = bigint.to_bytes_be();

    let basefield_256 = BaseField::from_repr(<BaseField as PrimeField>::BigInt::from(256)).unwrap();

    for byte in bytes.iter().rev() {
        let bytes_basefield = BaseField::from(*byte as u128);
        val += cur * bytes_basefield;

        cur *= &basefield_256;
    }

    val
}

/// the collections of methods for reducing the presentations
pub struct Reducer<TargetField: PrimeField, BaseField: PrimeField> {
    pub target_phantom: PhantomData<TargetField>,
    pub base_phantom: PhantomData<BaseField>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> Reducer<TargetField, BaseField> {
    /// convert limbs to bits (take at most `BaseField::size_in_bits() - 1` bits)
    /// This implementation would be more efficient than the original `to_bits`
    /// or `to_non_unique_bits` since we enforce that some bits are always zero.
    #[tracing::instrument(target = "r1cs")]
    pub fn limb_to_bits(
        limb: &FpVar<BaseField>,
        num_bits: usize,
    ) -> R1CSResult<Vec<Boolean<BaseField>>> {
        let cs = limb.cs();

        let num_bits = min(BaseField::size_in_bits() - 1, num_bits);
        let mut bits_considered = Vec::with_capacity(num_bits);
        let limb_value = limb.value().unwrap_or_default();

        for b in BitIteratorBE::new(limb_value.into_repr()).skip(
            <<BaseField as PrimeField>::Params as FpParameters>::REPR_SHAVE_BITS as usize
                + (BaseField::size_in_bits() - num_bits),
        ) {
            bits_considered.push(b);
        }

        if cs == ConstraintSystemRef::None {
            let mut bits = vec![];
            for b in bits_considered {
                bits.push(Boolean::<BaseField>::Constant(b));
            }

            Ok(bits)
        } else {
            let mut bits = vec![];
            for b in bits_considered {
                bits.push(Boolean::<BaseField>::new_witness(
                    ark_relations::ns!(cs, "bit"),
                    || Ok(b),
                )?);
            }

            let mut bit_sum = FpVar::<BaseField>::zero();
            let mut coeff = BaseField::one();

            for bit in bits.iter().rev() {
                bit_sum +=
                    <FpVar<BaseField> as From<Boolean<BaseField>>>::from((*bit).clone()) * coeff;
                coeff.double_in_place();
            }

            bit_sum.enforce_equal(limb)?;

            Ok(bits)
        }
    }

    /// Reduction to the normal form
    #[tracing::instrument(target = "r1cs")]
    pub fn reduce(elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>) -> R1CSResult<()> {
        let new_elem =
            AllocatedNonNativeFieldVar::new_witness(ns!(elem.cs(), "normal_form"), || {
                Ok(elem.value().unwrap_or_default())
            })?;
        elem.conditional_enforce_equal(&new_elem, &Boolean::TRUE)?;
        *elem = new_elem;

        Ok(())
    }

    /// Reduction to be enforced after additions
    #[tracing::instrument(target = "r1cs")]
    pub fn post_add_reduce(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> R1CSResult<()> {
        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            elem.get_optimization_type(),
        );
        let surfeit = overhead!(elem.num_of_additions_over_normal_form + BaseField::one()) + 1;

        if BaseField::size_in_bits() > 2 * params.bits_per_limb + surfeit + 1 {
            Ok(())
        } else {
            Self::reduce(elem)
        }
    }

    /// Reduction used before multiplication to reduce the representations in a way that allows efficient multiplication
    #[tracing::instrument(target = "r1cs")]
    pub fn pre_mul_reduce(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
        elem_other: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> R1CSResult<()> {
        assert_eq!(
            elem.get_optimization_type(),
            elem_other.get_optimization_type()
        );

        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            elem.get_optimization_type(),
        );

        if 2 * params.bits_per_limb + ark_std::log2(params.num_limbs) as usize
            > BaseField::size_in_bits() - 1
        {
            panic!("The current limb parameters do not support multiplication.");
        }

        loop {
            let prod_of_num_of_additions = (elem.num_of_additions_over_normal_form
                + BaseField::one())
                * (elem_other.num_of_additions_over_normal_form + BaseField::one());
            let overhead_limb = overhead!(prod_of_num_of_additions.mul(
                &BaseField::from_repr(<BaseField as PrimeField>::BigInt::from(
                    (params.num_limbs) as u64
                ))
                .unwrap()
            ));
            let bits_per_mulresult_limb = 2 * (params.bits_per_limb + 1) + overhead_limb;

            if bits_per_mulresult_limb < BaseField::size_in_bits() {
                break;
            }

            if elem.num_of_additions_over_normal_form
                >= elem_other.num_of_additions_over_normal_form
            {
                Self::reduce(elem)?;
            } else {
                Self::reduce(elem_other)?;
            }
        }

        Ok(())
    }

    /// Reduction to the normal form
    #[tracing::instrument(target = "r1cs")]
    pub fn pre_eq_reduce(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> R1CSResult<()> {
        if elem.is_in_the_normal_form {
            return Ok(());
        }

        Self::reduce(elem)
    }

    /// Group and check equality
    #[tracing::instrument(target = "r1cs")]
    pub fn group_and_check_equality(
        surfeit: usize,
        bits_per_limb: usize,
        shift_per_limb: usize,
        left: &[FpVar<BaseField>],
        right: &[FpVar<BaseField>],
    ) -> R1CSResult<()> {
        let cs = left.cs().or(right.cs());
        let zero = FpVar::<BaseField>::zero();

        let mut limb_pairs = Vec::<(FpVar<BaseField>, FpVar<BaseField>)>::new();
        let num_limb_in_a_group = (BaseField::size_in_bits()
            - 1
            - surfeit
            - 1
            - 1
            - 1
            - (bits_per_limb - shift_per_limb))
            / shift_per_limb;

        let shift_array = {
            let mut array = Vec::new();
            let mut cur = BaseField::one().into_repr();
            for _ in 0..num_limb_in_a_group {
                array.push(BaseField::from_repr(cur).unwrap());
                cur.muln(shift_per_limb as u32);
            }

            array
        };

        for (left_limb, right_limb) in left.iter().zip(right.iter()).rev() {
            // note: the `rev` operation is here, so that the first limb (and the first groupped limb) will be the least significant limb.
            limb_pairs.push((left_limb.clone(), right_limb.clone()));
        }

        let mut groupped_limb_pairs = Vec::<(FpVar<BaseField>, FpVar<BaseField>, usize)>::new();

        for limb_pairs_in_a_group in limb_pairs.chunks(num_limb_in_a_group) {
            let mut left_total_limb = zero.clone();
            let mut right_total_limb = zero.clone();

            for ((left_limb, right_limb), shift) in
                limb_pairs_in_a_group.iter().zip(shift_array.iter())
            {
                left_total_limb += &(left_limb * *shift);
                right_total_limb += &(right_limb * *shift);
            }

            groupped_limb_pairs.push((
                left_total_limb,
                right_total_limb,
                limb_pairs_in_a_group.len(),
            ));
        }

        // This part we mostly use the techniques in bellman-bignat
        // The following code is adapted from https://github.com/alex-ozdemir/bellman-bignat/blob/master/src/mp/bignat.rs#L567
        let mut carry_in = zero;
        let mut carry_in_value = BaseField::zero();
        let mut accumulated_extra = BigUint::zero();
        for (group_id, (left_total_limb, right_total_limb, num_limb_in_this_group)) in
            groupped_limb_pairs.iter().enumerate()
        {
            let mut pad_limb_repr: <BaseField as PrimeField>::BigInt = BaseField::one().into_repr();

            pad_limb_repr.muln(
                (surfeit
                    + (bits_per_limb - shift_per_limb)
                    + shift_per_limb * num_limb_in_this_group
                    + 1
                    + 1) as u32,
            );
            let pad_limb = BaseField::from_repr(pad_limb_repr).unwrap();

            let left_total_limb_value = left_total_limb.value().unwrap_or_default();
            let right_total_limb_value = right_total_limb.value().unwrap_or_default();

            let mut carry_value =
                left_total_limb_value + carry_in_value + pad_limb - right_total_limb_value;

            let mut carry_repr = carry_value.into_repr();
            carry_repr.divn((shift_per_limb * num_limb_in_this_group) as u32);

            carry_value = BaseField::from_repr(carry_repr).unwrap();

            let carry = FpVar::<BaseField>::new_witness(cs.clone(), || Ok(carry_value))?;

            accumulated_extra += limbs_to_bigint(bits_per_limb, &[pad_limb]);

            let (new_accumulated_extra, remainder) = accumulated_extra.div_rem(
                &BigUint::from(2u64).pow((shift_per_limb * num_limb_in_this_group) as u32),
            );
            let remainder_limb = bigint_to_basefield::<BaseField>(&remainder);

            // Now check
            //      left_total_limb + pad_limb + carry_in - right_total_limb
            //   =  carry shift by (shift_per_limb * num_limb_in_this_group) + remainder

            let eqn_left = left_total_limb + pad_limb + &carry_in - right_total_limb;

            let eqn_right = &carry
                * BaseField::from(2u64).pow(&[(shift_per_limb * num_limb_in_this_group) as u64])
                + remainder_limb;

            eqn_left.conditional_enforce_equal(&eqn_right, &Boolean::<BaseField>::TRUE)?;

            accumulated_extra = new_accumulated_extra;
            carry_in = carry.clone();
            carry_in_value = carry_value;

            if group_id == groupped_limb_pairs.len() - 1 {
                carry.enforce_equal(&FpVar::<BaseField>::Constant(bigint_to_basefield(
                    &accumulated_extra,
                )))?;
            } else {
                Reducer::<TargetField, BaseField>::limb_to_bits(&carry, surfeit + bits_per_limb)?;
            }
        }

        Ok(())
    }
}
