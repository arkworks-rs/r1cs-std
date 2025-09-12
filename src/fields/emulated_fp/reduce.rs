use super::{overhead, params::get_params, AllocatedEmulatedFpVar};
use crate::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    GR1CSVar,
};
use ark_ff::{biginteger::BigInteger, BitIteratorBE, One, PrimeField, Zero};
use ark_relations::{
    gr1cs::{ConstraintSystemRef, Result as R1CSResult},
    ns,
};
use ark_std::{cmp::min, marker::PhantomData, vec, vec::Vec};
use num_bigint::BigUint;
use num_integer::Integer;

pub fn limbs_to_bigint<BaseF: PrimeField>(bits_per_limb: usize, limbs: &[BaseF]) -> BigUint {
    let mut val = BigUint::zero();
    let mut big_cur = BigUint::one();
    let two = BigUint::from(2u32);
    for limb in limbs.iter().rev() {
        let limb_repr = limb.into_bigint().to_bits_le();
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

pub fn bigint_to_basefield<BaseF: PrimeField>(bigint: &BigUint) -> BaseF {
    let mut val = BaseF::zero();
    let mut cur = BaseF::one();
    let bytes = bigint.to_bytes_be();

    let basefield_256 = BaseF::from_bigint(<BaseF as PrimeField>::BigInt::from(256u64)).unwrap();

    for byte in bytes.iter().rev() {
        let bytes_basefield = BaseF::from(*byte as u128);
        val += cur * bytes_basefield;

        cur *= &basefield_256;
    }

    val
}

/// the collections of methods for reducing the presentations
pub struct Reducer<TargetF: PrimeField, BaseF: PrimeField> {
    pub target_phantom: PhantomData<TargetF>,
    pub base_phantom: PhantomData<BaseF>,
}

impl<TargetF: PrimeField, BaseF: PrimeField> Reducer<TargetF, BaseF> {
    /// convert limbs to bits (take at most `BaseF::MODULUS_BIT_SIZE as
    /// usize - 1` bits) This implementation would be more efficient than
    /// the original `to_bits` or `to_non_unique_bits` since we enforce that
    /// some bits are always zero.
    #[tracing::instrument(target = "gr1cs")]
    pub fn limb_to_bits(limb: &FpVar<BaseF>, num_bits: usize) -> R1CSResult<Vec<Boolean<BaseF>>> {
        let cs = limb.cs();

        let num_bits = min(BaseF::MODULUS_BIT_SIZE as usize - 1, num_bits);
        let mut bits_considered = Vec::with_capacity(num_bits);
        let limb_value = limb.value().unwrap_or_default();

        let num_bits_to_shave = BaseF::BigInt::NUM_LIMBS * 64 - (BaseF::MODULUS_BIT_SIZE as usize);

        for b in BitIteratorBE::new(limb_value.into_bigint())
            .skip(num_bits_to_shave + (BaseF::MODULUS_BIT_SIZE as usize - num_bits))
        {
            bits_considered.push(b);
        }

        if cs == ConstraintSystemRef::None {
            let mut bits = vec![];
            for b in bits_considered {
                bits.push(Boolean::<BaseF>::Constant(b));
            }

            Ok(bits)
        } else {
            let mut bits = vec![];
            for b in bits_considered {
                bits.push(Boolean::<BaseF>::new_witness(
                    ark_relations::ns!(cs, "bit"),
                    || Ok(b),
                )?);
            }

            let mut bit_sum = FpVar::<BaseF>::zero();
            let mut coeff = BaseF::one();

            for bit in bits.iter().rev() {
                bit_sum += <FpVar<BaseF> as From<Boolean<BaseF>>>::from((*bit).clone()) * coeff;
                coeff.double_in_place();
            }

            bit_sum.enforce_equal(limb)?;

            Ok(bits)
        }
    }

    /// Reduction to the normal form
    #[tracing::instrument(target = "gr1cs")]
    pub fn reduce(elem: &mut AllocatedEmulatedFpVar<TargetF, BaseF>) -> R1CSResult<()> {
        let new_elem = AllocatedEmulatedFpVar::new_witness(ns!(elem.cs(), "normal_form"), || {
            Ok(elem.value().unwrap_or_default())
        })?;
        elem.conditional_enforce_equal(&new_elem, &Boolean::TRUE)?;
        *elem = new_elem;

        Ok(())
    }

    /// Reduction to be enforced after additions
    #[tracing::instrument(target = "gr1cs")]
    pub fn post_add_reduce(elem: &mut AllocatedEmulatedFpVar<TargetF, BaseF>) -> R1CSResult<()> {
        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            elem.get_optimization_type(),
        );
        let surfeit = overhead!(elem.num_of_additions_over_normal_form + BaseF::one()) + 1;

        if BaseF::MODULUS_BIT_SIZE as usize > 2 * params.bits_per_limb + surfeit + 1 {
            Ok(())
        } else {
            Self::reduce(elem)
        }
    }

    /// Reduction used before multiplication to reduce the representations in a
    /// way that allows efficient multiplication
    #[tracing::instrument(target = "gr1cs")]
    pub fn pre_mul_reduce(
        elem: &mut AllocatedEmulatedFpVar<TargetF, BaseF>,
        elem_other: &mut AllocatedEmulatedFpVar<TargetF, BaseF>,
    ) -> R1CSResult<()> {
        assert_eq!(
            elem.get_optimization_type(),
            elem_other.get_optimization_type()
        );

        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            elem.get_optimization_type(),
        );

        // `2 * params.bits_per_limb + ark_std::log2(params.num_limbs + 1)` needs to be `<= BaseF::MODULUS_BIT_SIZE as usize - 4`
        // - see `group_and_check_equality` for more details
        if 2 * params.bits_per_limb + ark_std::log2(params.num_limbs + 1) as usize
            >= BaseF::MODULUS_BIT_SIZE as usize - 3
        {
            panic!("The current limb parameters do not support multiplication.");
        }

        loop {
            // this needs to be adjusted if we modify `prod_of_num_of_additions` for `AllocatedMulResultVar`
            // - see `mul_without_reduce` in `src/fields/emulated_fp/allocated_field_var.rs`
            let prod_of_num_of_additions = (elem.num_of_additions_over_normal_form + BaseF::one())
                * (elem_other.num_of_additions_over_normal_form + BaseF::one());
            let overhead_limb = overhead!(
                BaseF::one()
                    + prod_of_num_of_additions.mul(
                        &BaseF::from_bigint(<BaseF as PrimeField>::BigInt::from(
                            (params.num_limbs) as u64
                        ))
                        .unwrap()
                    )
            );

            let bits_per_mulresult_limb = 2 * params.bits_per_limb + overhead_limb;

            // we need `bits_per_mulresult_limb <= MODULUS_BIT_SIZE - 4`
            // - see `group_and_check_equality` for more details
            if bits_per_mulresult_limb < (BaseF::MODULUS_BIT_SIZE - 3) as usize {
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
    #[tracing::instrument(target = "gr1cs")]
    pub fn pre_eq_reduce(elem: &mut AllocatedEmulatedFpVar<TargetF, BaseF>) -> R1CSResult<()> {
        if elem.is_in_the_normal_form {
            return Ok(());
        }

        Self::reduce(elem)
    }

    /// Group and check equality
    #[tracing::instrument(target = "gr1cs")]
    pub fn group_and_check_equality(
        surfeit: usize,
        bits_per_limb: usize,
        shift_per_limb: usize,
        left: &[FpVar<BaseF>],
        right: &[FpVar<BaseF>],
    ) -> R1CSResult<()> {
        let cs = left.cs().or(right.cs());
        let zero = FpVar::<BaseF>::zero();

        let mut limb_pairs = Vec::<(FpVar<BaseF>, FpVar<BaseF>)>::new();

        // this size is closely related to the grouped limb size, padding size, pre_mul_reduce and post_add_reduce
        //
        // it should be carefully chosen so that 1) no overflow/underflow can happen in this function and 2) num_limb_in_a_group
        // is always >=1.
        //
        // 1. for this function
        // - pad_limb has bit size BaseF::MODULUS_BIT_SIZE - 1
        // - left/right_total_limb has bit size BaseF::MODULUS_BIT_SIZE - 3
        // - carry has even smaller size
        // - so, their sum has bit size <= BaseF::MODULUS_BIT_SIZE - 1
        //
        // 2. for pre_mul_reduce
        // - it enforces `2 * bits_per_limb + surfeit <= BaseF::MODULUS_BIT_SIZE - 4`
        //   - 2 * bits_per_limb in that function == 2 * (bits_per_limb - shift_per_limb) == shift_per_limb
        // - so, num_limb_in_a_group is >= 1 for mul
        let num_limb_in_a_group = (BaseF::MODULUS_BIT_SIZE as usize
            - 1
            - surfeit
            - 1
            - 1
            - 1
            - (bits_per_limb - shift_per_limb))
            / shift_per_limb;

        let shift_array = {
            let mut array = Vec::new();
            let mut cur = BaseF::one().into_bigint();
            for _ in 0..num_limb_in_a_group {
                array.push(BaseF::from_bigint(cur).unwrap());
                cur <<= shift_per_limb as u32;
            }

            array
        };

        for (left_limb, right_limb) in left.iter().zip(right.iter()).rev() {
            // note: the `rev` operation is here, so that the first limb (and the first
            // groupped limb) will be the least significant limb.
            limb_pairs.push((left_limb.clone(), right_limb.clone()));
        }

        let mut groupped_limb_pairs = Vec::<(FpVar<BaseF>, FpVar<BaseF>, usize)>::new();

        for limb_pairs_in_a_group in limb_pairs.chunks(num_limb_in_a_group) {
            // bit size = num_limb_in_a_group * shift_per_limb + bits_per_limb + true surfeit + 1
            //     <= BaseF::MODULUS_BIT_SIZE - 3
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
        let mut carry_in_value = BaseF::zero();
        let mut accumulated_extra = BigUint::zero();
        for (group_id, (left_total_limb, right_total_limb, num_limb_in_this_group)) in
            groupped_limb_pairs.iter().enumerate()
        {
            let mut pad_limb_repr = BaseF::ONE.into_bigint();

            // use padding to avoid underflow
            //
            // bit size = BaseF::MODULUS_BIT_SIZE - 1
            pad_limb_repr <<= (surfeit
                + (bits_per_limb - shift_per_limb)
                + shift_per_limb * num_limb_in_this_group
                + 1
                + 1) as u32;
            let pad_limb = BaseF::from_bigint(pad_limb_repr).unwrap();

            let left_total_limb_value = left_total_limb.value().unwrap_or_default();
            let right_total_limb_value = right_total_limb.value().unwrap_or_default();

            let mut carry_value =
                left_total_limb_value + carry_in_value + pad_limb - right_total_limb_value;

            let carry_repr =
                carry_value.into_bigint() >> (shift_per_limb * num_limb_in_this_group) as u32;

            carry_value = BaseF::from_bigint(carry_repr).unwrap();

            let carry = FpVar::new_witness(cs.clone(), || Ok(carry_value))?;

            accumulated_extra += limbs_to_bigint(bits_per_limb, &[pad_limb]);

            let (new_accumulated_extra, remainder) = accumulated_extra.div_rem(
                &BigUint::from(2u64).pow((shift_per_limb * num_limb_in_this_group) as u32),
            );
            let remainder_limb = bigint_to_basefield::<BaseF>(&remainder);

            // Now check
            //      left_total_limb + pad_limb + carry_in - right_total_limb
            //   =  carry shift by (shift_per_limb * num_limb_in_this_group) + remainder

            let eqn_left = left_total_limb + pad_limb + &carry_in - right_total_limb;

            let eqn_right = &carry
                * BaseF::from(2u64).pow(&[(shift_per_limb * num_limb_in_this_group) as u64])
                + remainder_limb;

            eqn_left.conditional_enforce_equal(&eqn_right, &Boolean::<BaseF>::TRUE)?;

            accumulated_extra = new_accumulated_extra;
            carry_in = carry.clone();
            carry_in_value = carry_value;

            if group_id == groupped_limb_pairs.len() - 1 {
                carry.enforce_equal(&FpVar::<BaseF>::Constant(bigint_to_basefield(
                    &accumulated_extra,
                )))?;
            } else {
                Reducer::<TargetF, BaseF>::limb_to_bits(&carry, surfeit + bits_per_limb)?;
            }
        }

        Ok(())
    }
}
