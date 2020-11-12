use crate::NonNativeFieldParams;
use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_std::{any::TypeId, boxed::Box, collections::BTreeMap};

/// The type for a cache map for parameters
pub type ParamsMap = BTreeMap<(usize, usize), NonNativeFieldParams>;

/// Obtain the parameters from a `ConstraintSystem`'s cache or generate a new one
#[must_use]
pub fn get_params<TargetField: PrimeField, BaseField: PrimeField>(
    cs: &ConstraintSystemRef<BaseField>,
) -> NonNativeFieldParams {
    match cs {
        ConstraintSystemRef::None => {
            gen_params(TargetField::size_in_bits(), BaseField::size_in_bits())
        }
        ConstraintSystemRef::CS(v) => {
            let cs_sys = v.borrow_mut();
            let mut big_map = cs_sys.cache_map.borrow_mut();
            let small_map = big_map.get(&TypeId::of::<ParamsMap>());

            if let Some(small_map) = small_map {
                if let Some(map) = small_map.downcast_ref::<ParamsMap>() {
                    let params = map.get(&(BaseField::size_in_bits(), TargetField::size_in_bits()));
                    if let Some(params) = params {
                        params.clone()
                    } else {
                        let params =
                            gen_params(TargetField::size_in_bits(), BaseField::size_in_bits());

                        let mut small_map = (*map).clone();
                        small_map.insert(
                            (BaseField::size_in_bits(), TargetField::size_in_bits()),
                            params.clone(),
                        );
                        big_map.insert(TypeId::of::<ParamsMap>(), Box::new(small_map));
                        params
                    }
                } else {
                    let params = gen_params(TargetField::size_in_bits(), BaseField::size_in_bits());

                    let mut small_map = ParamsMap::new();
                    small_map.insert(
                        (BaseField::size_in_bits(), TargetField::size_in_bits()),
                        params.clone(),
                    );

                    big_map.insert(TypeId::of::<ParamsMap>(), Box::new(small_map));
                    params
                }
            } else {
                let params = gen_params(TargetField::size_in_bits(), BaseField::size_in_bits());

                let mut small_map = ParamsMap::new();
                small_map.insert(
                    (BaseField::size_in_bits(), TargetField::size_in_bits()),
                    params.clone(),
                );

                big_map.insert(TypeId::of::<ParamsMap>(), Box::new(small_map));
                params
            }
        }
    }
}

/// Generate the new params
#[must_use]
pub const fn gen_params(target_field_size: usize, base_field_size: usize) -> NonNativeFieldParams {
    let optimization_type = if cfg!(feature = "density-optimized") {
        OptimizationType::Density
    } else {
        OptimizationType::Constraints
    };

    let (num_of_limbs, limb_size) =
        find_parameters(base_field_size, target_field_size, optimization_type);
    NonNativeFieldParams {
        num_limbs: num_of_limbs,
        bits_per_limb: limb_size,
    }
}

#[derive(Clone, Copy, Debug)]
/// The type of optimization target for the parameters searching
pub enum OptimizationType {
    /// Optimized for constraints
    Constraints,
    /// Optimized for density
    Density,
}

/// A function to search for parameters for nonnative field gadgets
pub const fn find_parameters(
    base_field_prime_length: usize,
    target_field_prime_bit_length: usize,
    optimization_type: OptimizationType,
) -> (usize, usize) {
    let mut found = false;
    let mut min_cost = 0usize;
    let mut min_cost_limb_size = 0usize;
    let mut min_cost_num_of_limbs = 0usize;

    let surfeit = 10;

    let max_limb_size = (base_field_prime_length - 1 - surfeit - 1) / 2 - 1;

    let mut limb_size = 1;

    while limb_size <= max_limb_size {
        let num_of_limbs = (target_field_prime_bit_length + limb_size - 1) / limb_size;

        let group_size =
            (base_field_prime_length - 1 - surfeit - 1 - 1 - limb_size + limb_size - 1) / limb_size;
        let num_of_groups = (2 * num_of_limbs - 1 + group_size - 1) / group_size;

        let mut this_cost = 0;

        match optimization_type {
            OptimizationType::Constraints => {
                this_cost += 2 * num_of_limbs - 1;
            }
            OptimizationType::Density => {
                this_cost += 6 * num_of_limbs * num_of_limbs;
            }
        };

        match optimization_type {
            OptimizationType::Constraints => {
                this_cost += target_field_prime_bit_length; // allocation of k
                this_cost += target_field_prime_bit_length + num_of_limbs; // allocation of r
                this_cost += num_of_groups + (num_of_groups - 1) * (limb_size * 2 + surfeit) + 1;
                // equality check
            }
            OptimizationType::Density => {
                this_cost += target_field_prime_bit_length * 3 + target_field_prime_bit_length; // allocation of k
                this_cost += target_field_prime_bit_length * 3
                    + target_field_prime_bit_length
                    + num_of_limbs; // allocation of r
                this_cost += num_of_limbs * num_of_limbs + 2 * (2 * num_of_limbs - 1); // compute kp
                this_cost += num_of_limbs
                    + num_of_groups
                    + 6 * num_of_groups
                    + (num_of_groups - 1) * (2 * limb_size + surfeit) * 4
                    + 2; // equality check
            }
        };

        if !found || this_cost < min_cost {
            found = true;
            min_cost = this_cost;
            min_cost_limb_size = limb_size;
            min_cost_num_of_limbs = num_of_limbs;
        }

        limb_size += 1;
    }

    (min_cost_num_of_limbs, min_cost_limb_size)
}
