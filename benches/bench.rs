use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::{emulated_fp::EmulatedFpVar, FieldVar},
};
use ark_relations::{
    gr1cs::{ConstraintSystem, ConstraintSystemRef, OptimizationGoal},
    ns,
};
use ark_std::rand::RngCore;

const NUM_REPETITIONS: usize = 1;

fn get_density<BaseField: PrimeField>(cs: &ConstraintSystemRef<BaseField>) -> usize {
    match cs {
        ConstraintSystemRef::None => panic!("Constraint system is none."),
        ConstraintSystemRef::CS(r) => {
            let mut cs_bak = r.borrow().clone();

            cs_bak.finalize();
            let matrices_map = cs_bak.to_matrices().unwrap();
            match matrices_map.get(ark_relations::gr1cs::R1CS_PREDICATE_LABEL) {
                None => 0,
                Some(matrices) => {
                    let a = &matrices[0];
                    let b = &matrices[1];
                    let c = &matrices[2];
                    let a_num_non_zero: usize = a.iter().map(|lc| lc.len()).sum();
                    let b_num_non_zero: usize = b.iter().map(|lc| lc.len()).sum();
                    let c_num_non_zero: usize = c.iter().map(|lc| lc.len()).sum();

                    a_num_non_zero + b_num_non_zero + c_num_non_zero
                },
            }
        },
    }
}

fn allocation<TargetF: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) -> (usize, usize) {
    let a_native = TargetF::rand(rng);

    let constraints_before = cs.num_constraints();
    let nonzeros_before = get_density(&cs);

    // There will be a check that ensures it has the reasonable number of bits
    let _ = EmulatedFpVar::<TargetF, BaseField>::new_witness(ns!(cs, "alloc a"), || Ok(a_native))
        .unwrap();

    let constraints_after = cs.num_constraints();
    let nonzeros_after = get_density(&cs);

    return (
        constraints_after - constraints_before,
        nonzeros_after - nonzeros_before,
    );
}

fn addition<TargetF: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) -> (usize, usize) {
    let a_native = TargetF::rand(rng);
    let a = EmulatedFpVar::<TargetF, BaseField>::new_witness(ns!(cs, "alloc a"), || Ok(a_native))
        .unwrap();

    let b_native = TargetF::rand(rng);
    let b = EmulatedFpVar::<TargetF, BaseField>::new_witness(ns!(cs, "alloc b"), || Ok(b_native))
        .unwrap();

    let constraints_before = cs.num_constraints();
    let nonzeros_before = get_density(&cs);

    let _ = &a + &b;

    let constraints_after = cs.num_constraints();
    let nonzeros_after = get_density(&cs);

    return (
        constraints_after - constraints_before,
        nonzeros_after - nonzeros_before,
    );
}

fn equality<TargetF: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) -> (usize, usize) {
    let a_native = TargetF::rand(rng);
    let a1 = EmulatedFpVar::<TargetF, BaseField>::new_witness(ns!(cs, "alloc a1"), || Ok(a_native))
        .unwrap();
    let a2 = EmulatedFpVar::<TargetF, BaseField>::new_witness(ns!(cs, "alloc a2"), || Ok(a_native))
        .unwrap();

    let constraints_before = cs.num_constraints();
    let nonzeros_before = get_density(&cs);

    a1.enforce_equal(&a2).unwrap();

    let constraints_after = cs.num_constraints();
    let nonzeros_after = get_density(&cs);

    return (
        constraints_after - constraints_before,
        nonzeros_after - nonzeros_before,
    );
}

fn multiplication<TargetF: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) -> (usize, usize) {
    let a_native = TargetF::rand(rng);
    let a = EmulatedFpVar::<TargetF, BaseField>::new_witness(ns!(cs, "initial a"), || Ok(a_native))
        .unwrap();

    let b_native = TargetF::rand(rng);
    let b = EmulatedFpVar::<TargetF, BaseField>::new_witness(ns!(cs, "initial b"), || Ok(b_native))
        .unwrap();

    let constraints_before = cs.num_constraints();
    let nonzeros_before = get_density(&cs);

    let _ = &a * &b;

    let constraints_after = cs.num_constraints();
    let nonzeros_after = get_density(&cs);

    return (
        constraints_after - constraints_before,
        nonzeros_after - nonzeros_before,
    );
}

fn inverse<TargetF: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) -> (usize, usize) {
    let num_native = TargetF::rand(rng);
    let num = EmulatedFpVar::<TargetF, BaseField>::new_witness(ns!(cs, "alloc"), || Ok(num_native))
        .unwrap();

    let constraints_before = cs.num_constraints();
    let nonzeros_before = get_density(&cs);

    let _ = num.inverse().unwrap();

    let constraints_after = cs.num_constraints();
    let nonzeros_after = get_density(&cs);

    return (
        constraints_after - constraints_before,
        nonzeros_after - nonzeros_before,
    );
}

macro_rules! nonnative_bench_individual {
    ($bench_method:ident, $bench_name:ident, $bench_target_field:ty, $bench_base_field:ty) => {
        let rng = &mut ark_std::test_rng();
        let mut num_constraints = 0;
        let mut num_nonzeros = 0;
        for _ in 0..NUM_REPETITIONS {
            let cs_sys = ConstraintSystem::<$bench_base_field>::new();
            let cs = ConstraintSystemRef::new(cs_sys);
            cs.set_optimization_goal(OptimizationGoal::Constraints);

            let (cur_constraints, cur_nonzeros) =
                $bench_method::<$bench_target_field, $bench_base_field, _>(cs.clone(), rng);

            num_constraints += cur_constraints;
            num_nonzeros += cur_nonzeros;

            assert!(cs.is_satisfied().unwrap());
        }
        let average_constraints = num_constraints / NUM_REPETITIONS;
        let average_nonzeros = num_nonzeros / NUM_REPETITIONS;
        println!(
            "{} takes: {} constraints, {} non-zeros",
            stringify!($bench_method),
            average_constraints,
            average_nonzeros,
        );
    };
}

macro_rules! nonnative_bench {
    ($bench_name:ident, $bench_target_field:ty, $bench_base_field:ty) => {
        println!(
            "For {} to simulate {}",
            stringify!($bench_base_field),
            stringify!($bench_target_field),
        );
        nonnative_bench_individual!(
            allocation,
            $bench_name,
            $bench_target_field,
            $bench_base_field
        );
        nonnative_bench_individual!(
            addition,
            $bench_name,
            $bench_target_field,
            $bench_base_field
        );
        nonnative_bench_individual!(
            multiplication,
            $bench_name,
            $bench_target_field,
            $bench_base_field
        );
        nonnative_bench_individual!(
            equality,
            $bench_name,
            $bench_target_field,
            $bench_base_field
        );
        nonnative_bench_individual!(inverse, $bench_name, $bench_target_field, $bench_base_field);
        println!("----------------------")
    };
}

fn main() {
    nonnative_bench!(MNT46Small, ark_mnt4_298::Fr, ark_mnt6_298::Fr);
    nonnative_bench!(MNT64Small, ark_mnt6_298::Fr, ark_mnt4_298::Fr);
    nonnative_bench!(MNT46Big, ark_mnt4_753::Fr, ark_mnt6_753::Fr);
    nonnative_bench!(MNT64Big, ark_mnt6_753::Fr, ark_mnt4_753::Fr);
    nonnative_bench!(BLS12MNT4Small, ark_bls12_381::Fr, ark_mnt4_298::Fr);
    nonnative_bench!(BLS12, ark_bls12_381::Fq, ark_bls12_381::Fr);
    nonnative_bench!(MNT6BigMNT4Small, ark_mnt6_753::Fr, ark_mnt4_298::Fr);
}
