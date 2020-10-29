use crate::NonNativeFieldParams;
use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_std::{
    any::{Any, TypeId},
    boxed::Box,
    cmp::min,
    collections::BTreeMap,
};

/// The type for a cache map for parameters
pub type ParamsMap = BTreeMap<(usize, usize), NonNativeFieldParams>;
#[derive(Clone)]
/// Statistics for hit rate of cache
pub struct HitRate {
    /// Number of hits
    hit: usize,
    /// Number of misses
    miss: usize,
}

impl HitRate {
    /// Initialize and activate the statistics
    pub fn init<BaseField: PrimeField>(cs: &ConstraintSystemRef<BaseField>) {
        match cs {
            ConstraintSystemRef::None => (),
            ConstraintSystemRef::CS(v) => {
                let cs_sys = v.borrow_mut();
                let mut big_map = cs_sys.cache_map.borrow_mut();
                big_map.insert(
                    TypeId::of::<HitRate>(),
                    Box::new(HitRate { hit: 0, miss: 0 }),
                );
            }
        }
    }

    /// Add to the statistics
    pub fn update(pmap: &mut BTreeMap<TypeId, Box<dyn Any>>, hit: bool) {
        let hit_rate = pmap.get(&TypeId::of::<HitRate>());

        if let Some(stat) = hit_rate.and_then(|rate| rate.downcast_ref::<HitRate>()) {
            let mut hit_rate = (*stat).clone();
            if hit {
                hit_rate.hit += 1;
            } else {
                hit_rate.miss += 1;
            }
            pmap.insert(TypeId::of::<HitRate>(), Box::new(hit_rate));
        }
    }

    /// Print out the statistics
    #[cfg(feature = "std")]
    pub fn print<BaseField: PrimeField>(cs: &ConstraintSystemRef<BaseField>) {
        match cs {
            ConstraintSystemRef::None => (),
            ConstraintSystemRef::CS(v) => {
                let cs_sys = v.borrow();
                let big_map = cs_sys.cache_map.borrow();
                let hit_rate = big_map.get(&TypeId::of::<HitRate>());

                if hit_rate.is_some() {
                    match hit_rate.unwrap().downcast_ref::<HitRate>() {
                        Some(stat) => {
                            let hit_rate = (*stat).clone();
                            println!(
                                "Hit: {}, Miss: {}, Hit Rate = {}",
                                hit_rate.hit,
                                hit_rate.miss,
                                (hit_rate.hit as f64) / ((hit_rate.hit + hit_rate.miss) as f64)
                            );
                        }
                        None => (),
                    }
                }
            }
        }
    }
}

/// Obtain the parameters from a ConstraintSystem's cache or generate a new one
pub fn get_params<TargetField: PrimeField, BaseField: PrimeField>(
    cs: &ConstraintSystemRef<BaseField>,
) -> NonNativeFieldParams {
    match cs {
        ConstraintSystemRef::None => gen_params::<TargetField, BaseField>(),
        ConstraintSystemRef::CS(v) => {
            let cs_sys = v.borrow_mut();
            let mut big_map = cs_sys.cache_map.borrow_mut();
            let small_map = big_map.get(&TypeId::of::<ParamsMap>());

            if small_map.is_some() {
                match small_map.unwrap().downcast_ref::<ParamsMap>() {
                    Some(map) => {
                        let params =
                            map.get(&(BaseField::size_in_bits(), TargetField::size_in_bits()));
                        if let Some(params) = params {
                            let params = params.clone();
                            HitRate::update(&mut *big_map, true);
                            params
                        } else {
                            let params = gen_params::<TargetField, BaseField>();

                            let mut small_map = (*map).clone();
                            small_map.insert(
                                (BaseField::size_in_bits(), TargetField::size_in_bits()),
                                params.clone(),
                            );
                            big_map.insert(TypeId::of::<ParamsMap>(), Box::new(small_map));

                            HitRate::update(&mut *big_map, false);
                            params
                        }
                    }
                    None => {
                        let params = gen_params::<TargetField, BaseField>();

                        let mut small_map = ParamsMap::new();
                        small_map.insert(
                            (BaseField::size_in_bits(), TargetField::size_in_bits()),
                            params.clone(),
                        );

                        big_map.insert(TypeId::of::<ParamsMap>(), Box::new(small_map));
                        HitRate::update(&mut *big_map, false);
                        params
                    }
                }
            } else {
                let params = gen_params::<TargetField, BaseField>();

                let mut small_map = ParamsMap::new();
                small_map.insert(
                    (BaseField::size_in_bits(), TargetField::size_in_bits()),
                    params.clone(),
                );

                big_map.insert(TypeId::of::<ParamsMap>(), Box::new(small_map));
                HitRate::update(&mut *big_map, false);
                params
            }
        }
    }
}

/// Generate the new params
pub fn gen_params<TargetField: PrimeField, BaseField: PrimeField>() -> NonNativeFieldParams {
    let mut problem = ParamsSearching::new(BaseField::size_in_bits(), TargetField::size_in_bits());
    problem.solve();

    NonNativeFieldParams {
        num_limbs: problem.num_of_limbs,
        bits_per_top_limb: problem.top_limb_size.unwrap(),
        bits_per_non_top_limb: problem.non_top_limb_size.unwrap(),
    }
}

/// A search instance for parameters for nonnative field gadgets
#[derive(Clone)]
pub struct ParamsSearching {
    // Problem
    /// Prime length of the base field
    pub base_field_prime_length: usize,
    /// Prime length of the target field
    pub target_field_prime_bit_length: usize,

    // Solution
    /// Number of additions as a result of multiplying
    pub num_of_additions_after_mul: usize,
    /// Number of limbs
    pub num_of_limbs: usize,
    /// Size of the top limb
    pub top_limb_size: Option<usize>,
    /// Size of a non-top limb
    pub non_top_limb_size: Option<usize>,
}

impl ParamsSearching {
    /// Create the search problem
    pub fn new(base_field_prime_length: usize, target_field_prime_bit_length: usize) -> Self {
        Self {
            base_field_prime_length,
            target_field_prime_bit_length,
            num_of_additions_after_mul: 1,
            num_of_limbs: 2,
            top_limb_size: None,
            non_top_limb_size: None,
        }
    }

    /// Solve the search problem
    pub fn solve(&mut self) {
        loop {
            let Self {
                base_field_prime_length,
                target_field_prime_bit_length,
                num_of_additions_after_mul,
                num_of_limbs,
                ..
            } = self.clone();

            let mut min_overhead =
                ((2 * num_of_limbs - 3) * (4 + ark_std::log2(num_of_limbs) as usize)) + 5;
            if min_overhead > target_field_prime_bit_length {
                min_overhead -= target_field_prime_bit_length;
                min_overhead = ((2 * num_of_limbs - 3)
                    * (4 + (ark_std::log2(num_of_limbs * min_overhead * min_overhead) as usize)))
                    + 5;

                if min_overhead > target_field_prime_bit_length {
                    min_overhead -= target_field_prime_bit_length;

                    if (ark_std::log2(num_of_limbs * min_overhead * min_overhead) as usize) + 3
                        >= base_field_prime_length
                    {
                        #[cfg(feature = "std")]
                        dbg!(format!("The program has tested up to {} limbs; at this point, we can conclude that no suitable parameters exist", num_of_limbs));
                        self.top_limb_size = None;
                        self.non_top_limb_size = None;
                        return;
                    }
                }
            }

            let top_limb = 1 + (num_of_additions_after_mul + 1) * (num_of_additions_after_mul + 1);
            let log_top_limb = ark_std::log2(top_limb) as usize;
            let log_sub_top_limb = ark_std::log2(top_limb * 2) as usize;
            let log_other_limbs_upper_bound = ark_std::log2(top_limb * num_of_limbs) as usize;

            let mut flag = false;
            let mut cost = 0usize;
            let mut current_top_limb_size = None;
            let mut current_non_top_limb_size = None;

            for top_limb_size in 0..min(base_field_prime_length, target_field_prime_bit_length) {
                let non_top_limb_size =
                    (target_field_prime_bit_length - top_limb_size + self.num_of_limbs - 1 - 1)
                        / (self.num_of_limbs - 1);

                // top limb must be smaller; otherwise, the top limb is too long
                if !(top_limb_size <= non_top_limb_size) {
                    break;
                }

                // post-add reduce must succeed; otherwise, the top limb is too long
                if !(2 * (top_limb_size + 5) < base_field_prime_length) {
                    break;
                }
                if !(2 * (non_top_limb_size + 5) < base_field_prime_length) {
                    continue;
                }

                // computation on the top limb works
                if 2 * (top_limb_size + 1) + log_top_limb + non_top_limb_size + 1
                    >= 2 * (non_top_limb_size + 1) + log_sub_top_limb + 1
                {
                    if !(2 * (top_limb_size + 1) + log_top_limb + non_top_limb_size
                        < base_field_prime_length - 1)
                    {
                        continue;
                    }
                } else if !(2 * (non_top_limb_size + 1) + log_sub_top_limb
                    < base_field_prime_length - 1)
                {
                    continue;
                }

                // computation on the non-top limb works
                if !(2 * non_top_limb_size + log_other_limbs_upper_bound
                    <= base_field_prime_length - 1)
                {
                    continue;
                }

                let this_cost = 2 * (top_limb_size + 1)
                    + log_top_limb
                    + non_top_limb_size
                    + 1
                    + (2 * num_of_limbs - 3)
                        * (2 * (non_top_limb_size + 1) + log_other_limbs_upper_bound)
                    - target_field_prime_bit_length;

                if flag == false || this_cost < cost {
                    flag = true;
                    cost = this_cost;
                    current_top_limb_size = Some(top_limb_size);
                    current_non_top_limb_size = Some(non_top_limb_size);
                }
            }

            if flag == false {
                self.num_of_limbs += 1;
                self.num_of_additions_after_mul = 1;
                continue;
            }

            if cost > num_of_additions_after_mul {
                self.num_of_additions_after_mul = cost;
                continue;
            }

            self.top_limb_size = current_top_limb_size;
            self.non_top_limb_size = current_non_top_limb_size;
            break;
        }
    }
}
