use crate::NonNativeFieldVar;
use ark_ff::PrimeField;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::FieldVar;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef};
use curves::{bls12_381, mnt4_298, mnt4_753, mnt6_298, mnt6_753};
use rand::thread_rng;
use rand_core::RngCore;

const NUM_REPETITIONS: usize = 100;

fn allocation<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) -> usize {
    let a_native = TargetField::rand(rng);

    let before = cs.num_constraints();
    // there will be a check that ensures it has the reasonable number of bits
    NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "alloc a"),
        || Ok(a_native),
    )
    .unwrap();
    let after = cs.num_constraints();

    return after - before;
}

fn addition<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) -> usize {
    let a_native = TargetField::rand(rng);
    let a = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "alloc a"),
        || Ok(a_native),
    )
    .unwrap();

    let b_native = TargetField::rand(rng);
    let b = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "alloc b"),
        || Ok(b_native),
    )
    .unwrap();

    let before = cs.num_constraints();
    let _ = &a + &b;
    let after = cs.num_constraints();

    return after - before;
}

fn equality<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) -> usize {
    let a_native = TargetField::rand(rng);
    let a1 = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "alloc a1"),
        || Ok(a_native),
    )
    .unwrap();
    let a2 = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "alloc a2"),
        || Ok(a_native),
    )
    .unwrap();

    let before = cs.num_constraints();
    a1.enforce_equal(&a2).unwrap();
    let after = cs.num_constraints();

    return after - before;
}

fn multiplication<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) -> usize {
    let a_native = TargetField::rand(rng);
    let a = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "initial a"),
        || Ok(a_native),
    )
    .unwrap();

    let b_native = TargetField::rand(rng);
    let b = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "initial b"),
        || Ok(b_native),
    )
    .unwrap();

    let before = cs.num_constraints();
    let _ = &a * &b;
    let after = cs.num_constraints();

    return after - before;
}

fn inverse<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) -> usize {
    let num_native = TargetField::rand(rng);
    let num = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "alloc"),
        || Ok(num_native),
    )
    .unwrap();

    let before = cs.num_constraints();
    num.inverse().unwrap();
    let after = cs.num_constraints();

    return after - before;
}

macro_rules! nonnative_bench_individual {
    ($bench_method:ident, $bench_name:ident, $bench_target_field:ty, $bench_base_field:ty) => {
        let rng = &mut thread_rng();
        let mut num_constraints = 0;
        for _ in 0..NUM_REPETITIONS {
            let cs = ConstraintSystem::<$bench_base_field>::new();
            let cs_ref = ConstraintSystemRef::new(cs);
            num_constraints +=
                $bench_method::<$bench_target_field, $bench_base_field, _>(cs_ref.clone(), rng);
            assert!(cs_ref.is_satisfied().unwrap());
        }
        let average = num_constraints / NUM_REPETITIONS;
        println!(
            "{} takes {} constraints doing {} over {}",
            stringify!($bench_base_field),
            average,
            stringify!($bench_method),
            stringify!($bench_target_field),
        );
    };
}

macro_rules! nonnative_bench {
    ($bench_name:ident, $bench_target_field:ty, $bench_base_field:ty) => {
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

        println!("---------");
    };
}

fn main() {
    nonnative_bench!(MNT46Small, mnt4_298::Fr, mnt6_298::Fr);
    nonnative_bench!(MNT64Small, mnt6_298::Fr, mnt4_298::Fr);
    nonnative_bench!(MNT46Big, mnt4_753::Fr, mnt6_753::Fr);
    nonnative_bench!(MNT64Big, mnt6_753::Fr, mnt4_753::Fr);
    nonnative_bench!(BLS12MNT4Small, bls12_381::Fr, mnt4_298::Fr);
    nonnative_bench!(BLS12, bls12_381::Fq, bls12_381::Fr);
    nonnative_bench!(MNT6BigMNT4Small, mnt6_753::Fr, mnt4_298::Fr);
}
