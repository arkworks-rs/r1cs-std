use crate::params::get_params;
use crate::{overhead, AllocatedNonNativeFieldVar};
use ark_ff::{biginteger::BigInteger, fields::FpParameters, BitIteratorBE};
use ark_ff::{One, PrimeField, Zero};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::AllocatedFp;
use ark_r1cs_std::{
    boolean::{AllocatedBit, Boolean},
    R1CSVar,
};
use ark_relations::{
    lc,
    r1cs::{LinearCombination, SynthesisError},
};
use ark_std::{
    cmp::{max, min},
    marker::PhantomData,
    vec,
    vec::Vec,
};
use num_bigint::BigUint;

/// the collections of methods for reducing the presentations
pub struct Reducer<TargetField: PrimeField, BaseField: PrimeField> {
    pub target_phantom: PhantomData<TargetField>,
    pub base_phantom: PhantomData<BaseField>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> Reducer<TargetField, BaseField> {
    /// an internal method for checking whether a push operation can be completed for the current gadget;
    /// if not, `reduce_all_limbs`, which reduces without using a push, is used.
    /// this is part of the post-add reduction.
    pub fn can_safely_push(elem: &AllocatedNonNativeFieldVar<TargetField, BaseField>) -> bool {
        let params = get_params::<TargetField, BaseField>(&elem.cs);

        let log = overhead!(elem.num_of_additions_over_normal_form + &BaseField::one()) + 1;
        BaseField::size_in_bits() > params.bits_per_non_top_limb + log + 1
    }

    /// an internal method for checking whether the current two elements are ready to multiply;
    /// if not, they would be reduced. This is part of the pre-mul reduction.
    pub fn can_safely_mul(
        elem: &AllocatedNonNativeFieldVar<TargetField, BaseField>,
        other: &AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> bool {
        let params = get_params::<TargetField, BaseField>(&elem.cs);

        let prod_of_num_of_additions = (elem.num_of_additions_over_normal_form.clone()
            + &BaseField::one())
            * &(other.num_of_additions_over_normal_form.clone() + &BaseField::one());

        let bits_per_top_limb = params.bits_per_top_limb;
        let bits_per_non_top_limb = params.bits_per_non_top_limb;

        let log_top_limb = overhead!(prod_of_num_of_additions);
        let log_sub_top_limb = overhead!(prod_of_num_of_additions.double());
        let log_other_limbs_upper_bound = overhead!(prod_of_num_of_additions.mul(
            &BaseField::from_repr(<BaseField as PrimeField>::BigInt::from(
                (params.num_limbs) as u64
            ))
            .unwrap()
        ));

        let bits_per_unreduced_top_limb = max(
            2 * (bits_per_top_limb + 1) + log_top_limb + bits_per_non_top_limb + 1,
            2 * (bits_per_non_top_limb + 1) + log_sub_top_limb + 1,
        );
        let bits_per_unreduced_non_top_limb =
            2 * (bits_per_non_top_limb + 1) + log_other_limbs_upper_bound;

        max(bits_per_unreduced_top_limb, bits_per_unreduced_non_top_limb)
            < BaseField::size_in_bits()
    }

    /// convert limbs to bits (take at most BaseField::size_in_bits() - 1 bits)
    /// This implementation would be more efficient than the original to_bits or to_non_unique_bits since we enforce that some bits are always zero.
    pub fn limb_to_bits(
        limb: &AllocatedFp<BaseField>,
        num_bits: usize,
    ) -> Result<Vec<Boolean<BaseField>>, SynthesisError> {
        let cs = limb.cs.clone();

        let num_bits = min(BaseField::size_in_bits() - 1, num_bits);
        let mut bits_considered = Vec::with_capacity(num_bits);
        let limb_value = limb.value().unwrap_or_default();

        for b in BitIteratorBE::new(limb_value.into_repr()).skip(
            <<BaseField as PrimeField>::Params as FpParameters>::REPR_SHAVE_BITS as usize
                + (BaseField::size_in_bits() - num_bits),
        ) {
            bits_considered.push(b);
        }

        let mut bits = vec![];
        for b in bits_considered.into_iter() {
            bits.push(AllocatedBit::new_witness(
                ark_relations::ns!(cs, "bit"),
                || Ok(b),
            )?);
        }

        let mut lc = LinearCombination::zero();
        let mut coeff = BaseField::one();

        for bit in bits.iter().rev() {
            lc += (coeff, bit.variable());
            coeff.double_in_place();
        }

        let limb_lc = LinearCombination::from((BaseField::one(), limb.variable));

        limb.cs.enforce_constraint(lc!(), lc!(), limb_lc - lc)?;

        Ok(bits.into_iter().map(Boolean::from).collect())
    }

    /// Use the `sum of resides` method to reduce the representations, without firstly pushing it to the top
    pub fn reduce_all_limbs(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<(), SynthesisError> {
        let cs = elem.cs.clone();
        let params = get_params::<TargetField, BaseField>(&cs);

        // almost only used for mandatory reduce, since the values are not pushed first (pushing first provides better efficiency)
        let mut limb_bits = Vec::new();
        let surfeit = overhead!(elem.num_of_additions_over_normal_form + &BaseField::one()) + 1;
        for (i, limb) in elem.limbs.iter().enumerate() {
            if i == 0 {
                // the top limb
                limb_bits.push(Self::limb_to_bits(
                    limb,
                    params.bits_per_top_limb + surfeit,
                )?);
            } else {
                // the non-top limbs
                limb_bits.push(Self::limb_to_bits(
                    limb,
                    params.bits_per_non_top_limb + surfeit,
                )?);
            }
        }

        // compute the powers of 2 mod p that might be used
        let mut powers_of_2_mod_p = Vec::new();
        let mut cur = TargetField::one();
        for _ in 0..(params.num_limbs - 1) * params.bits_per_non_top_limb
            + params.bits_per_top_limb
            + surfeit
        {
            powers_of_2_mod_p.push(
                AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                    &cur,
                    Some(&cs),
                )
                .unwrap(),
            );
            cur.double_in_place();
        }

        // start with those bits that are within the weakly canonical representation
        let mut limbs_value = Vec::<BaseField>::new();
        let mut limbs_lc = Vec::<LinearCombination<BaseField>>::new();

        for (i, limb) in limb_bits.iter().enumerate() {
            let mut value = BaseField::zero();
            let mut lc = LinearCombination::zero();
            let mut coeff = BaseField::one();

            let mut limb_rev = limb.clone();
            limb_rev.reverse();

            let num_bits_in_weakly_canonical = if i == 0 {
                params.bits_per_top_limb
            } else {
                params.bits_per_non_top_limb
            };

            for (_, bit) in limb_rev
                .iter()
                .enumerate()
                .take(num_bits_in_weakly_canonical)
            {
                if bit.value().unwrap_or_default() {
                    value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            limbs_value.push(value);
            limbs_lc.push(lc);
        }

        let mut additions = BaseField::zero();
        for (i, limb) in limb_bits.iter().enumerate() {
            let mut limb_rev = limb.clone();
            limb_rev.reverse();

            let num_bits_in_weakly_canonical = if i == 0 {
                params.bits_per_top_limb
            } else {
                params.bits_per_non_top_limb
            };

            for (j, bit) in limb_rev
                .iter()
                .enumerate()
                .skip(num_bits_in_weakly_canonical)
            {
                additions += &BaseField::one();
                let num_of_limbs_lower = params.num_limbs - i - 1;
                let power_of_2 =
                    &powers_of_2_mod_p[num_of_limbs_lower * params.bits_per_non_top_limb + j];

                if bit.value().unwrap_or_default() {
                    for (k, power_of_2_limb) in power_of_2.iter().enumerate() {
                        limbs_value[k] += power_of_2_limb;
                    }
                }

                for (k, power_of_2_coeff) in power_of_2.iter().enumerate() {
                    limbs_lc[k] = &limbs_lc[k] + &(bit.lc() * power_of_2_coeff.clone());
                }
            }
        }

        let mut new_limbs_gadget = Vec::<AllocatedFp<BaseField>>::new();
        for (value, lc) in limbs_value.iter().zip(limbs_lc.iter()) {
            let value_gadget =
                AllocatedFp::<BaseField>::new_witness(elem.cs.clone(), || Ok(value))?;

            let value_lc = LinearCombination::from((BaseField::one(), value_gadget.variable));

            cs.enforce_constraint(lc!(), lc!(), value_lc - lc).unwrap();

            new_limbs_gadget.push(value_gadget.clone());
        }

        elem.limbs = new_limbs_gadget;
        elem.num_of_additions_over_normal_form = additions;

        Ok(())
    }

    /// A subprocedure of the common reduction, which firstly pushes the representations to the top
    pub fn push_to_the_top(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<
        (
            Vec<Boolean<BaseField>>,
            Vec<BaseField>,
            Vec<LinearCombination<BaseField>>,
        ),
        SynthesisError,
    > {
        let cs = elem.cs.clone();
        let params = get_params::<TargetField, BaseField>(&cs);

        let surfeit = overhead!(elem.num_of_additions_over_normal_form + &BaseField::one()) + 1;
        let surfeit_plus_one = surfeit + 1; // one more bit is added as a result of pushing

        let mut limbs_value = Vec::<BaseField>::new();
        let mut limbs_lc = Vec::<LinearCombination<BaseField>>::new();
        let mut add: AllocatedFp<BaseField> =
            AllocatedFp::<BaseField>::new_constant(cs.clone(), &BaseField::zero())?;

        // non-top limbs
        for (i, limb) in elem
            .limbs
            .iter()
            .rev()
            .enumerate()
            .take(params.num_limbs - 1)
        {
            let limb_added = if i != 0 { limb.add(&add) } else { limb.clone() };

            let mut value = BaseField::zero();
            let mut lc = LinearCombination::<BaseField>::zero();
            let mut coeff = BaseField::one();

            let surfeit_cur = if i != 0 { surfeit_plus_one } else { surfeit };

            let limbs_bits =
                Self::limb_to_bits(&limb_added, params.bits_per_non_top_limb + surfeit_cur)?;

            for (_, bit) in limbs_bits
                .iter()
                .rev()
                .enumerate()
                .take(params.bits_per_non_top_limb)
            {
                if bit.value().unwrap_or_default() {
                    value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            limbs_value.push(value);
            limbs_lc.push(lc);

            coeff = BaseField::one();

            let mut add_value = BaseField::zero();
            lc = LinearCombination::<BaseField>::zero();
            for (_, bit) in limbs_bits
                .iter()
                .rev()
                .enumerate()
                .skip(params.bits_per_non_top_limb)
            {
                if bit.value().unwrap_or_default() {
                    add_value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            add =
                AllocatedFp::<BaseField>::new_witness(ark_relations::ns!(cs, "alloc_add"), || {
                    Ok(add_value)
                })?;

            let add_lc = LinearCombination::from((BaseField::one(), add.variable));

            cs.enforce_constraint(lc!(), lc!(), add_lc - lc)?;
        }

        let mut overhead_bits = Vec::<Boolean<BaseField>>::new();

        // top limb
        {
            let top_limb = &elem.limbs[0];
            let top_limb_added = top_limb.add(&add);

            let mut value = BaseField::zero();
            let mut lc = LinearCombination::<BaseField>::zero();
            let mut coeff = BaseField::one();

            let top_limbs_bits =
                Self::limb_to_bits(&top_limb_added, params.bits_per_top_limb + surfeit_plus_one)?;

            for (_, bit) in top_limbs_bits
                .iter()
                .rev()
                .enumerate()
                .take(params.bits_per_top_limb)
            {
                if bit.value().unwrap_or_default() {
                    value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            limbs_value.push(value);
            limbs_lc.push(lc);

            for bit in top_limbs_bits.iter().rev().skip(params.bits_per_top_limb) {
                overhead_bits.push((*bit).clone());
            }
        }

        limbs_value.reverse();
        limbs_lc.reverse();

        Ok((overhead_bits, limbs_value, limbs_lc))
    }

    /// A subprocedure of the common reduction, which pushes the representations to the top and keeps the new top unreduced.
    pub fn push_to_the_top_keep_top(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<(Vec<BaseField>, Vec<LinearCombination<BaseField>>), SynthesisError> {
        let cs = elem.cs.clone();
        let params = get_params::<TargetField, BaseField>(&cs);

        let surfeit = overhead!(elem.num_of_additions_over_normal_form + &BaseField::one()) + 1;
        let surfeit_plus_one = surfeit + 1; // one more bit is added as a result of pushing

        let mut limbs_value = Vec::<BaseField>::new();
        let mut limbs_lc = Vec::<LinearCombination<BaseField>>::new();
        let mut add: AllocatedFp<BaseField> =
            AllocatedFp::<BaseField>::new_constant(cs.clone(), &BaseField::zero())?;

        // non-top limbs
        for (i, limb) in elem
            .limbs
            .iter()
            .rev()
            .enumerate()
            .take(params.num_limbs - 1)
        {
            let limb_added = if i != 0 { limb.add(&add) } else { limb.clone() };

            let mut value = BaseField::zero();
            let mut lc = LinearCombination::<BaseField>::zero();
            let mut coeff = BaseField::one();

            let surfeit_cur = if i != 0 { surfeit_plus_one } else { surfeit };

            let limbs_bits =
                Self::limb_to_bits(&limb_added, params.bits_per_non_top_limb + surfeit_cur)?;

            for (_, bit) in limbs_bits
                .iter()
                .rev()
                .enumerate()
                .take(params.bits_per_non_top_limb)
            {
                if bit.value().unwrap_or_default() {
                    value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            limbs_value.push(value);
            limbs_lc.push(lc);

            coeff = BaseField::one();

            let mut add_value = BaseField::zero();
            lc = LinearCombination::<BaseField>::zero();
            for (_, bit) in limbs_bits
                .iter()
                .rev()
                .enumerate()
                .skip(params.bits_per_non_top_limb)
            {
                if bit.value().unwrap_or_default() {
                    add_value += &coeff;
                }
                lc = &lc + bit.lc() * coeff;
                coeff.double_in_place();
            }

            add = AllocatedFp::<BaseField>::new_witness(cs.clone(), || Ok(add_value))?;

            let add_lc = LinearCombination::from((BaseField::one(), add.variable));
            cs.enforce_constraint(lc!(), lc!(), add_lc - lc)?;
        }

        // top limb
        {
            let top_limb = &elem.limbs[0];
            let top_limb_added = top_limb.add(&add);

            let lc = LinearCombination::from((BaseField::one(), top_limb_added.variable));

            limbs_value.push(top_limb_added.value().unwrap_or_default());
            limbs_lc.push(lc);
        }

        limbs_value.reverse();
        limbs_lc.reverse();

        Ok((limbs_value, limbs_lc))
    }

    /// A full reduction procedure, which pushes the representations to the top first and then reduces it
    pub fn push_and_reduce_the_top(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<(), SynthesisError> {
        let surfeit = overhead!(elem.num_of_additions_over_normal_form + &BaseField::one()) + 1;
        let cs = elem.cs.clone();

        let params = get_params::<TargetField, BaseField>(&cs);

        // push
        let (overhead_bits, mut limbs_value, mut limbs_lc) = Self::push_to_the_top(elem)?;

        // reduce
        let mut powers_of_2_mod_p = Vec::new();
        let mut cur = TargetField::one();
        for _ in 0..(params.num_limbs - 1) * params.bits_per_non_top_limb
            + params.bits_per_top_limb
            + surfeit
            + 1
        {
            powers_of_2_mod_p.push(
                AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                    &cur,
                    Some(&cs),
                )
                .unwrap(),
            );
            cur.double_in_place();
        }

        let mut additions = BaseField::zero();
        for (i, bit) in overhead_bits.iter().enumerate() {
            additions += &BaseField::one();
            let power_of_2 = &powers_of_2_mod_p[(params.num_limbs - 1)
                * params.bits_per_non_top_limb
                + params.bits_per_top_limb
                + i];

            if bit.value().unwrap_or_default() {
                for (j, power_of_2_limb) in power_of_2.iter().enumerate() {
                    limbs_value[j] += power_of_2_limb;
                }
            }

            for (j, power_of_2_coeff) in power_of_2.iter().enumerate() {
                limbs_lc[j] = &limbs_lc[j] + &(bit.lc() * power_of_2_coeff.clone());
            }
        }

        let mut new_limbs_gadget = Vec::<AllocatedFp<BaseField>>::new();
        for (value, lc) in limbs_value.iter().zip(limbs_lc.iter()) {
            let value_gadget = AllocatedFp::<BaseField>::new_witness(
                ark_relations::ns!(cs, "limb_initial_value_alloc"),
                || Ok(value),
            )?;

            let value_lc = (BaseField::one(), value_gadget.variable);

            let final_lc = LinearCombination::from(value_lc) - lc.clone();

            cs.enforce_constraint(lc!(), lc!(), final_lc).unwrap();

            new_limbs_gadget.push(value_gadget.clone());
        }

        elem.limbs = new_limbs_gadget;
        elem.num_of_additions_over_normal_form = additions;

        Ok(())
    }

    /// Reduction to be enforced after additions
    pub fn post_add_reduce(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<(), SynthesisError> {
        if Self::can_safely_push(elem) {
            Ok(())
        } else {
            Self::reduce_all_limbs(elem)
        }
    }

    /// Reduction used before multiplication to reduce the representations in a way that allows efficient multiplication
    pub fn pre_mul_reduce(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
        elem_other: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<(), SynthesisError> {
        let params = get_params::<TargetField, BaseField>(&elem.cs);

        if (2 * params.bits_per_top_limb + params.bits_per_non_top_limb + 1
            > BaseField::size_in_bits() - 1)
            || (2 * params.bits_per_non_top_limb
                + f64::from(params.num_limbs as u32).log2().ceil() as usize
                > BaseField::size_in_bits() - 1)
        {
            panic!("The current limb parameters do not support multiplication.");
        }

        while !Self::can_safely_mul(elem, elem_other) {
            if elem.num_of_additions_over_normal_form
                >= elem_other.num_of_additions_over_normal_form
            {
                Self::push_and_reduce_the_top(elem)?;
            } else {
                Self::push_and_reduce_the_top(elem_other)?;
            }
        }

        Ok(())
    }

    /// Reduction to the normal form
    pub fn pre_eq_reduce(
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<(), SynthesisError> {
        let cs = elem.cs.clone();
        let params = get_params::<TargetField, BaseField>(&cs);

        if elem.is_in_the_normal_form {
            return Ok(());
        }

        let value = elem.value().unwrap_or_default();
        let normal_form_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                &value,
                Some(&cs),
            )?;
        let normal_form_gadget =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::new_witness(cs.clone(), || {
                Ok(value)
            })?;

        let p_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations_from_big_int(
                &<TargetField as PrimeField>::Params::MODULUS,
                Some(&cs),
            )?;
        let mut p_gadget_limbs = Vec::new();
        for limb in p_representations.iter() {
            p_gadget_limbs.push(AllocatedFp::<BaseField>::new_constant(cs.clone(), limb)?);
        }
        let p_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs: cs.clone(),
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: BaseField::one(),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        let (elem_pushed_to_the_top_limbs_value, elem_pushed_to_the_top_limbs_lc) =
            Self::push_to_the_top_keep_top(elem)?;

        let limbs_to_bigint = |limbs: Vec<BaseField>| {
            let mut val = BigUint::zero();
            let mut big_cur = BigUint::one();
            let two = BigUint::from(2u32);
            for limb in limbs.iter().rev() {
                let limb_repr = limb.into_repr().to_bits();
                let mut small_cur = big_cur.clone();
                for limb_bit in limb_repr.iter().rev() {
                    if *limb_bit == true {
                        val = val + &small_cur;
                    }
                    small_cur *= 2u32;
                }
                big_cur *= two.pow(params.bits_per_non_top_limb as u32);
            }

            val
        };

        let bigint_to_basefield = |bigint: BigUint| {
            let mut val = BaseField::zero();
            let mut cur = BaseField::one();
            let bytes = bigint.to_bytes_be();

            let basefield_256 =
                BaseField::from_repr(<BaseField as PrimeField>::BigInt::from(256)).unwrap();

            for byte in bytes.iter().rev() {
                let bytes_basefield =
                    BaseField::from_repr(<BaseField as PrimeField>::BigInt::from(*byte as u64))
                        .unwrap();
                val = val + &(cur * &bytes_basefield);

                cur *= &basefield_256;
            }

            val
        };

        let elem_bigint = limbs_to_bigint(elem_pushed_to_the_top_limbs_value);
        let normal_bigint = limbs_to_bigint(normal_form_representations);
        let p_bigint = limbs_to_bigint(p_representations);

        let k = bigint_to_basefield((elem_bigint - normal_bigint) / p_bigint);
        let k_gadget = AllocatedFp::<BaseField>::new_witness(cs.clone(), || Ok(k))?;

        // k should be smaller than 2^ ((BaseField::size_in_bits() - 1) - max(bits_per_top_limb, bits_per_non_top_limb) - 1)
        // aka, k only has at most (BaseField::size_in_bits() - 1) - max(bits_per_top_limb, bits_per_non_top_limb) - 1 bits.
        Self::limb_to_bits(
            &k_gadget,
            (BaseField::size_in_bits() - 1)
                - max(params.bits_per_top_limb, params.bits_per_non_top_limb)
                - 1,
        )?;

        let mut kp_gadget_limbs = Vec::new();
        for limb in p_gadget.limbs.iter() {
            kp_gadget_limbs.push(limb.mul(&k_gadget));
        }
        let kp_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs: elem.cs.clone(),
            limbs: kp_gadget_limbs,
            num_of_additions_over_normal_form: elem.num_of_additions_over_normal_form.clone(),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        let mut normal_form_plus_kp_gadget = normal_form_gadget.add(&kp_gadget)?;
        let (_, normal_form_plus_kp_limbs_lc) =
            Self::push_to_the_top_keep_top(&mut normal_form_plus_kp_gadget)?;

        for (left, right) in elem_pushed_to_the_top_limbs_lc
            .iter()
            .zip(normal_form_plus_kp_limbs_lc.iter())
        {
            let final_lc = left - right.clone();
            cs.enforce_constraint(lc!(), lc!(), final_lc)?;
        }

        elem.limbs = normal_form_gadget.limbs;
        elem.num_of_additions_over_normal_form = BaseField::zero();
        elem.is_in_the_normal_form = true;
        Ok(())
    }
}
