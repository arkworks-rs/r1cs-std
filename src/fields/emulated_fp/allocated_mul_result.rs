use super::{
    params::{get_params, OptimizationType},
    reduce::{bigint_to_basefield, limbs_to_bigint, Reducer},
    AllocatedEmulatedFpVar,
};
use crate::{fields::fp::FpVar, prelude::*};
use ark_ff::PrimeField;
use ark_relations::{
    ns,
    r1cs::{ConstraintSystemRef, OptimizationGoal, Result as R1CSResult},
};
use ark_std::{marker::PhantomData, vec::Vec};
use num_bigint::BigUint;

/// The allocated form of `MulResultVar` (introduced below)
#[derive(Debug)]
#[must_use]
pub struct AllocatedMulResultVar<TargetF: PrimeField, BaseF: PrimeField> {
    /// Constraint system reference
    pub cs: ConstraintSystemRef<BaseF>,
    /// Limbs of the intermediate representations
    pub limbs: Vec<FpVar<BaseF>>,
    /// The cumulative num of additions
    pub prod_of_num_of_additions: BaseF,
    #[doc(hidden)]
    pub target_phantom: PhantomData<TargetF>,
}

impl<TargetF: PrimeField, BaseF: PrimeField> From<&AllocatedEmulatedFpVar<TargetF, BaseF>>
    for AllocatedMulResultVar<TargetF, BaseF>
{
    fn from(src: &AllocatedEmulatedFpVar<TargetF, BaseF>) -> Self {
        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            src.get_optimization_type(),
        );

        let mut limbs = src.limbs.clone();
        limbs.reverse();
        limbs.resize(2 * params.num_limbs - 1, FpVar::<BaseF>::zero());
        limbs.reverse();

        let prod_of_num_of_additions = src.num_of_additions_over_normal_form + &BaseF::one();

        Self {
            cs: src.cs(),
            limbs,
            prod_of_num_of_additions,
            target_phantom: PhantomData,
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> AllocatedMulResultVar<TargetF, BaseF> {
    /// Get the CS
    pub fn cs(&self) -> ConstraintSystemRef<BaseF> {
        self.cs.clone()
    }

    /// Get the value of the multiplication result
    pub fn value(&self) -> R1CSResult<TargetF> {
        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            self.get_optimization_type(),
        );

        let p_representations =
            AllocatedEmulatedFpVar::<TargetF, BaseF>::get_limbs_representations_from_big_integer(
                &<TargetF as PrimeField>::MODULUS,
                self.get_optimization_type(),
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut limbs_values = Vec::<BaseF>::new();
        for limb in self.limbs.iter() {
            limbs_values.push(limb.value().unwrap_or_default());
        }
        let value_bigint = limbs_to_bigint(params.bits_per_limb, &limbs_values);

        let res = bigint_to_basefield::<TargetF>(&(value_bigint % p_bigint));
        Ok(res)
    }

    /// Constraints for reducing the result of a multiplication mod p, to get an
    /// original representation.
    pub fn reduce(&self) -> R1CSResult<AllocatedEmulatedFpVar<TargetF, BaseF>> {
        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            self.get_optimization_type(),
        );

        // Step 1: get p
        let p_representations =
            AllocatedEmulatedFpVar::<TargetF, BaseF>::get_limbs_representations_from_big_integer(
                &<TargetF as PrimeField>::MODULUS,
                self.get_optimization_type(),
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut p_gadget_limbs = Vec::new();
        for limb in p_representations.iter() {
            p_gadget_limbs.push(FpVar::<BaseF>::new_constant(self.cs(), limb)?);
        }
        let p_gadget = AllocatedEmulatedFpVar::<TargetF, BaseF> {
            cs: self.cs(),
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: BaseF::one(),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        // Step 2: compute surfeit
        let surfeit = overhead!(self.prod_of_num_of_additions + BaseF::one()) + 1 + 1;

        // Step 3: allocate k
        let k_bits = {
            let mut res = Vec::new();

            let mut limbs_values = Vec::<BaseF>::new();
            for limb in self.limbs.iter() {
                limbs_values.push(limb.value().unwrap_or_default());
            }

            let value_bigint = limbs_to_bigint(params.bits_per_limb, &limbs_values);
            let mut k_cur = value_bigint / p_bigint;

            let total_len = TargetF::MODULUS_BIT_SIZE as usize + surfeit;

            for _ in 0..total_len {
                res.push(Boolean::<BaseF>::new_witness(self.cs(), || {
                    Ok(&k_cur % 2u64 == BigUint::from(1u64))
                })?);
                k_cur /= 2u64;
            }
            res
        };

        let k_limbs = {
            let zero = FpVar::Constant(BaseF::zero());
            let mut limbs = Vec::new();

            let mut k_bits_cur = k_bits.clone();

            for i in 0..params.num_limbs {
                let this_limb_size = if i != params.num_limbs - 1 {
                    params.bits_per_limb
                } else {
                    k_bits.len() - (params.num_limbs - 1) * params.bits_per_limb
                };

                let this_limb_bits = k_bits_cur[0..this_limb_size].to_vec();
                k_bits_cur = k_bits_cur[this_limb_size..].to_vec();

                let mut limb = zero.clone();
                let mut cur = BaseF::one();

                for bit in this_limb_bits.iter() {
                    limb += &(FpVar::<BaseF>::from(bit.clone()) * cur);
                    cur.double_in_place();
                }
                limbs.push(limb);
            }

            limbs.reverse();
            limbs
        };

        let k_gadget = AllocatedEmulatedFpVar::<TargetF, BaseF> {
            cs: self.cs(),
            limbs: k_limbs,
            num_of_additions_over_normal_form: self.prod_of_num_of_additions,
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        let cs = self.cs();

        let r_gadget = AllocatedEmulatedFpVar::<TargetF, BaseF>::new_witness(ns!(cs, "r"), || {
            Ok(self.value()?)
        })?;

        let params = get_params(
            TargetF::MODULUS_BIT_SIZE as usize,
            BaseF::MODULUS_BIT_SIZE as usize,
            self.get_optimization_type(),
        );

        // Step 1: reduce `self` and `other` if neceessary
        let mut prod_limbs = Vec::new();
        let zero = FpVar::<BaseF>::zero();

        for _ in 0..2 * params.num_limbs - 1 {
            prod_limbs.push(zero.clone());
        }

        for i in 0..params.num_limbs {
            for j in 0..params.num_limbs {
                prod_limbs[i + j] = &prod_limbs[i + j] + (&p_gadget.limbs[i] * &k_gadget.limbs[j]);
            }
        }

        let mut kp_plus_r_gadget = Self {
            cs,
            limbs: prod_limbs,
            prod_of_num_of_additions: (p_gadget.num_of_additions_over_normal_form + BaseF::one())
                * (k_gadget.num_of_additions_over_normal_form + BaseF::one()),
            target_phantom: PhantomData,
        };

        let kp_plus_r_limbs_len = kp_plus_r_gadget.limbs.len();
        for (i, limb) in r_gadget.limbs.iter().rev().enumerate() {
            kp_plus_r_gadget.limbs[kp_plus_r_limbs_len - 1 - i] += limb;
        }

        Reducer::<TargetF, BaseF>::group_and_check_equality(
            surfeit,
            2 * params.bits_per_limb,
            params.bits_per_limb,
            &self.limbs,
            &kp_plus_r_gadget.limbs,
        )?;

        Ok(r_gadget)
    }

    /// Add unreduced elements.
    #[tracing::instrument(target = "r1cs")]
    pub fn add(&self, other: &Self) -> R1CSResult<Self> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let mut new_limbs = Vec::new();

        for (l1, l2) in self.limbs.iter().zip(other.limbs.iter()) {
            let new_limb = l1 + l2;
            new_limbs.push(new_limb);
        }

        Ok(Self {
            cs: self.cs(),
            limbs: new_limbs,
            prod_of_num_of_additions: self.prod_of_num_of_additions
                + other.prod_of_num_of_additions,
            target_phantom: PhantomData,
        })
    }

    /// Add native constant elem
    #[tracing::instrument(target = "r1cs")]
    pub fn add_constant(&self, other: &TargetF) -> R1CSResult<Self> {
        let mut other_limbs = AllocatedEmulatedFpVar::<TargetF, BaseF>::get_limbs_representations(
            other,
            self.get_optimization_type(),
        )?;
        other_limbs.reverse();

        let mut new_limbs = Vec::new();

        for (i, limb) in self.limbs.iter().rev().enumerate() {
            if i < other_limbs.len() {
                new_limbs.push(limb + other_limbs[i]);
            } else {
                new_limbs.push((*limb).clone());
            }
        }

        new_limbs.reverse();

        Ok(Self {
            cs: self.cs(),
            limbs: new_limbs,
            prod_of_num_of_additions: self.prod_of_num_of_additions + BaseF::one(),
            target_phantom: PhantomData,
        })
    }

    pub(crate) fn get_optimization_type(&self) -> OptimizationType {
        match self.cs().optimization_goal() {
            OptimizationGoal::None => OptimizationType::Constraints,
            OptimizationGoal::Constraints => OptimizationType::Constraints,
            OptimizationGoal::Weight => OptimizationType::Weight,
        }
    }
}
