use ark_bls12_381::Bls12_381;
use ark_ec::PairingEngine;
use ark_ff::{BigInteger, PrimeField};
use ark_mnt4_298::MNT4_298;
use ark_mnt4_753::MNT4_753;
use ark_mnt6_298::MNT6_298;
use ark_mnt6_753::MNT6_753;

use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::{
        nonnative::{AllocatedNonNativeFieldVar, NonNativeFieldVar},
        FieldVar,
    },
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef};
use ark_std::rand::RngCore;

#[cfg(not(ci))]
const NUM_REPETITIONS: usize = 100;
#[cfg(ci)]
const NUM_REPETITIONS: usize = 1;

#[cfg(not(ci))]
const TEST_COUNT: usize = 100;
#[cfg(ci)]
const TEST_COUNT: usize = 1;

fn allocation_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let a_native = TargetField::rand(rng);
    let a = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "alloc a"),
        || Ok(a_native),
    )
    .unwrap();

    let a_actual = a.value().unwrap();
    let a_expected = a_native;
    assert!(
        a_actual.eq(&a_expected),
        "allocated value does not equal the expected value"
    );

    let (_a, a_bits) =
        AllocatedNonNativeFieldVar::<TargetField, BaseField>::new_witness_with_le_bits(
            ark_relations::ns!(cs, "alloc a2"),
            || Ok(a_native),
        )
        .unwrap();

    let a_bits_actual: Vec<bool> = a_bits.into_iter().map(|b| b.value().unwrap()).collect();
    let mut a_bits_expected = a_native.into_bigint().to_bits_le();
    a_bits_expected.truncate(TargetField::MODULUS_BIT_SIZE as usize);
    assert_eq!(
        a_bits_actual, a_bits_expected,
        "allocated bits does not equal the expected bits"
    );
}

fn addition_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
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

    let a_plus_b = a + &b;

    let a_plus_b_actual = a_plus_b.value().unwrap();
    let a_plus_b_expected = a_native + &b_native;
    assert!(a_plus_b_actual.eq(&a_plus_b_expected), "a + b failed");
}

fn multiplication_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
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

    let a_times_b = a * &b;

    let a_times_b_actual = a_times_b.value().unwrap();
    let a_times_b_expected = a_native * &b_native;

    assert!(
        a_times_b_actual.eq(&a_times_b_expected),
        "a_times_b = {:?}, a_times_b_actual = {:?}, a_times_b_expected = {:?}",
        a_times_b,
        a_times_b_actual.into_bigint().as_ref(),
        a_times_b_expected.into_bigint().as_ref()
    );
}

fn equality_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
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

    let a_times_b = a * &b;

    let a_times_b_expected = a_native * &b_native;
    let a_times_b_expected_gadget = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "alloc a * b"),
        || Ok(a_times_b_expected),
    )
    .unwrap();

    a_times_b.enforce_equal(&a_times_b_expected_gadget).unwrap();
}

fn edge_cases_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let zero_native = TargetField::zero();
    let zero = NonNativeFieldVar::<TargetField, BaseField>::zero();
    let one = NonNativeFieldVar::<TargetField, BaseField>::one();

    let a_native = TargetField::rand(rng);
    let minus_a_native = TargetField::zero() - &a_native;
    let a = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "alloc a"),
        || Ok(a_native),
    )
    .unwrap();

    let a_plus_zero = &a + &zero;
    let a_minus_zero = &a - &zero;
    let zero_minus_a = &zero - &a;
    let a_times_zero = &a * &zero;

    let zero_plus_a = &zero + &a;
    let zero_times_a = &zero * &a;

    let a_times_one = &a * &one;
    let one_times_a = &one * &a;

    let a_plus_zero_native = a_plus_zero.value().unwrap();
    let a_minus_zero_native = a_minus_zero.value().unwrap();
    let zero_minus_a_native = zero_minus_a.value().unwrap();
    let a_times_zero_native = a_times_zero.value().unwrap();
    let zero_plus_a_native = zero_plus_a.value().unwrap();
    let zero_times_a_native = zero_times_a.value().unwrap();
    let a_times_one_native = a_times_one.value().unwrap();
    let one_times_a_native = one_times_a.value().unwrap();

    assert!(
        a_plus_zero_native.eq(&a_native),
        "a_plus_zero = {:?}, a = {:?}",
        a_plus_zero_native.into_bigint().as_ref(),
        a_native.into_bigint().as_ref()
    );
    assert!(
        a_minus_zero_native.eq(&a_native),
        "a_minus_zero = {:?}, a = {:?}",
        a_minus_zero_native.into_bigint().as_ref(),
        a_native.into_bigint().as_ref()
    );
    assert!(
        zero_minus_a_native.eq(&minus_a_native),
        "zero_minus_a = {:?}, minus_a = {:?}",
        zero_minus_a_native.into_bigint().as_ref(),
        minus_a_native.into_bigint().as_ref()
    );
    assert!(
        a_times_zero_native.eq(&zero_native),
        "a_times_zero = {:?}, zero = {:?}",
        a_times_zero_native.into_bigint().as_ref(),
        zero_native.into_bigint().as_ref()
    );
    assert!(
        zero_plus_a_native.eq(&a_native),
        "zero_plus_a = {:?}, a = {:?}",
        zero_plus_a_native.into_bigint().as_ref(),
        a_native.into_bigint().as_ref()
    );
    assert!(
        zero_times_a_native.eq(&zero_native),
        "zero_times_a = {:?}, zero = {:?}",
        zero_times_a_native.into_bigint().as_ref(),
        zero_native.into_bigint().as_ref()
    );
    assert!(
        a_times_one_native.eq(&a_native),
        "a_times_one = {:?}, a = {:?}",
        a_times_one_native.into_bigint().as_ref(),
        a_native.into_bigint().as_ref()
    );
    assert!(
        one_times_a_native.eq(&a_native),
        "one_times_a = {:?}, a = {:?}",
        one_times_a_native.into_bigint().as_ref(),
        a_native.into_bigint().as_ref()
    );
}

fn distribution_law_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let a_native = TargetField::rand(rng);
    let b_native = TargetField::rand(rng);
    let c_native = TargetField::rand(rng);

    let a_plus_b_native = a_native.clone() + &b_native;
    let a_times_c_native = a_native.clone() * &c_native;
    let b_times_c_native = b_native.clone() * &c_native;
    let a_plus_b_times_c_native = a_plus_b_native.clone() * &c_native;
    let a_times_c_plus_b_times_c_native = a_times_c_native + &b_times_c_native;

    assert!(
        a_plus_b_times_c_native.eq(&a_times_c_plus_b_times_c_native),
        "(a + b) * c doesn't equal (a * c) + (b * c)"
    );

    let a = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "a"),
        || Ok(a_native),
    )
    .unwrap();
    let b = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "b"),
        || Ok(b_native),
    )
    .unwrap();
    let c = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "c"),
        || Ok(c_native),
    )
    .unwrap();

    let a_plus_b = &a + &b;
    let a_times_c = &a * &c;
    let b_times_c = &b * &c;
    let a_plus_b_times_c = &a_plus_b * &c;
    let a_times_c_plus_b_times_c = &a_times_c + &b_times_c;

    assert!(
        a_plus_b.value().unwrap().eq(&a_plus_b_native),
        "a + b doesn't match"
    );
    assert!(
        a_times_c.value().unwrap().eq(&a_times_c_native),
        "a * c doesn't match"
    );
    assert!(
        b_times_c.value().unwrap().eq(&b_times_c_native),
        "b * c doesn't match"
    );
    assert!(
        a_plus_b_times_c
            .value()
            .unwrap()
            .eq(&a_plus_b_times_c_native),
        "(a + b) * c doesn't match"
    );
    assert!(
        a_times_c_plus_b_times_c
            .value()
            .unwrap()
            .eq(&a_times_c_plus_b_times_c_native),
        "(a * c) + (b * c) doesn't match"
    );
    assert!(
        a_plus_b_times_c_native.eq(&a_times_c_plus_b_times_c_native),
        "(a + b) * c != (a * c) + (b * c)"
    );
}

fn randomized_arithmetic_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let mut operations: Vec<u32> = Vec::new();
    for _ in 0..TEST_COUNT {
        operations.push(rng.next_u32() % 3);
    }

    let mut num_native = TargetField::rand(rng);
    let mut num = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "initial num"),
        || Ok(num_native),
    )
    .unwrap();
    for op in operations.iter() {
        let next_native = TargetField::rand(rng);
        let next = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
            ark_relations::ns!(cs, "next num for repetition"),
            || Ok(next_native),
        )
        .unwrap();
        match op {
            0 => {
                num_native += &next_native;
                num += &next;
            },
            1 => {
                num_native *= &next_native;
                num *= &next;
            },
            2 => {
                num_native -= &next_native;
                num -= &next;
            },
            _ => (),
        };

        assert!(
            num.value().unwrap().eq(&num_native),
            "randomized arithmetic failed:"
        );
    }
}

fn addition_stress_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num =
        NonNativeFieldVar::new_witness(ark_relations::ns!(cs, "initial num"), || Ok(num_native))
            .unwrap();
    for _ in 0..TEST_COUNT {
        let next_native = TargetField::rand(rng);
        let next = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
            ark_relations::ns!(cs, "next num for repetition"),
            || Ok(next_native),
        )
        .unwrap();
        num_native += &next_native;
        num += &next;

        assert!(num.value().unwrap().eq(&num_native));
    }
}

fn multiplication_stress_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "initial num"),
        || Ok(num_native),
    )
    .unwrap();
    for _ in 0..TEST_COUNT {
        let next_native = TargetField::rand(rng);
        let next = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
            ark_relations::ns!(cs, "next num for repetition"),
            || Ok(next_native),
        )
        .unwrap();
        num_native *= &next_native;
        num *= &next;

        assert!(num.value().unwrap().eq(&num_native));
    }
}

fn mul_and_add_stress_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "initial num"),
        || Ok(num_native),
    )
    .unwrap();
    for _ in 0..TEST_COUNT {
        let next_add_native = TargetField::rand(rng);
        let next_add = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
            ark_relations::ns!(cs, "next to add num for repetition"),
            || Ok(next_add_native),
        )
        .unwrap();
        let next_mul_native = TargetField::rand(rng);
        let next_mul = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
            ark_relations::ns!(cs, "next to mul num for repetition"),
            || Ok(next_mul_native),
        )
        .unwrap();

        num_native = num_native * &next_mul_native + &next_add_native;
        num = num * &next_mul + &next_add;

        assert!(num.value().unwrap().eq(&num_native));
    }
}

fn square_mul_add_stress_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "initial num"),
        || Ok(num_native),
    )
    .unwrap();
    for _ in 0..TEST_COUNT {
        let next_add_native = TargetField::rand(rng);
        let next_add = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
            ark_relations::ns!(cs, "next to add num for repetition"),
            || Ok(next_add_native),
        )
        .unwrap();
        let next_mul_native = TargetField::rand(rng);
        let next_mul = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
            ark_relations::ns!(cs, "next to mul num for repetition"),
            || Ok(next_mul_native),
        )
        .unwrap();

        num_native = num_native * &num_native * &next_mul_native + &next_add_native;
        num = &num * &num * &next_mul + &next_add;

        assert!(num.value().unwrap().eq(&num_native));
    }
}

fn double_stress_test_1<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "initial num"),
        || Ok(num_native),
    )
    .unwrap();
    // Add to at least BaseField::size_in_bits() to ensure that we teat the
    // overflowing
    for _ in 0..TEST_COUNT + BaseField::MODULUS_BIT_SIZE as usize {
        // double
        num_native = num_native + &num_native;
        num = &num + &num;

        assert!(num.value().unwrap().eq(&num_native), "result incorrect");
    }
}

fn double_stress_test_2<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "initial num"),
        || Ok(num_native),
    )
    .unwrap();
    for _ in 0..TEST_COUNT {
        // double
        num_native = num_native + &num_native;
        num = &num + &num;

        assert!(num.value().unwrap().eq(&num_native));

        // square
        let num_square_native = num_native * &num_native;
        let num_square = &num * &num;
        assert!(num_square.value().unwrap().eq(&num_square_native));
    }
}

fn double_stress_test_3<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    let mut num_native = TargetField::rand(rng);
    let mut num = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
        ark_relations::ns!(cs, "initial num"),
        || Ok(num_native),
    )
    .unwrap();
    for _ in 0..TEST_COUNT {
        // double
        num_native = num_native + &num_native;
        num = &num + &num;

        assert!(num.value().unwrap().eq(&num_native));

        // square
        let num_square_native = num_native * &num_native;
        let num_square = &num * &num;
        let num_square_native_gadget = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
            ark_relations::ns!(cs, "repetition: alloc_native num"),
            || Ok(num_square_native),
        )
        .unwrap();

        num_square.enforce_equal(&num_square_native_gadget).unwrap();
    }
}

fn inverse_stress_test<TargetField: PrimeField, BaseField: PrimeField, R: RngCore>(
    cs: ConstraintSystemRef<BaseField>,
    rng: &mut R,
) {
    for _ in 0..TEST_COUNT {
        let num_native = TargetField::rand(rng);
        let num = NonNativeFieldVar::<TargetField, BaseField>::new_witness(
            ark_relations::ns!(cs, "num"),
            || Ok(num_native),
        )
        .unwrap();

        if num_native == TargetField::zero() {
            continue;
        }

        let num_native_inverse = num_native.inverse().unwrap();
        let num_inverse = num.inverse().unwrap();

        assert!(num_inverse.value().unwrap().eq(&num_native_inverse));
    }
}

macro_rules! nonnative_test_individual {
    ($test_method:ident, $test_name:ident, $test_target_field:ty, $test_base_field:ty) => {
        paste::item! {
            #[test]
            fn [<$test_method _ $test_name:lower>]() {
                let rng = &mut ark_std::test_rng();

                for _ in 0..NUM_REPETITIONS {
                    let cs = ConstraintSystem::<$test_base_field>::new_ref();
                    $test_method::<$test_target_field, $test_base_field, _>(cs.clone(), rng);
                    assert!(cs.is_satisfied().unwrap());
                }
            }
        }
    };
}

macro_rules! nonnative_test {
    ($test_name:ident, $test_target_field:ty, $test_base_field:ty) => {
        nonnative_test_individual!(
            allocation_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            addition_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            multiplication_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            equality_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            edge_cases_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            distribution_law_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            addition_stress_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            double_stress_test_1,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            double_stress_test_2,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            double_stress_test_3,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            randomized_arithmetic_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            multiplication_stress_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            mul_and_add_stress_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            square_mul_add_stress_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
        nonnative_test_individual!(
            inverse_stress_test,
            $test_name,
            $test_target_field,
            $test_base_field
        );
    };
}

nonnative_test!(
    MNT46Small,
    <MNT4_298 as PairingEngine>::Fr,
    <MNT6_298 as PairingEngine>::Fr
);
nonnative_test!(
    MNT64Small,
    <MNT6_298 as PairingEngine>::Fr,
    <MNT4_298 as PairingEngine>::Fr
);
nonnative_test!(
    MNT46Big,
    <MNT4_753 as PairingEngine>::Fr,
    <MNT6_753 as PairingEngine>::Fr
);
nonnative_test!(
    MNT64Big,
    <MNT6_753 as PairingEngine>::Fr,
    <MNT4_753 as PairingEngine>::Fr
);
nonnative_test!(
    BLS12MNT4Small,
    <Bls12_381 as PairingEngine>::Fr,
    <MNT4_298 as PairingEngine>::Fr
);
nonnative_test!(
    BLS12,
    <Bls12_381 as PairingEngine>::Fq,
    <Bls12_381 as PairingEngine>::Fr
);
#[cfg(not(ci))]
nonnative_test!(
    MNT6BigMNT4Small,
    <MNT6_753 as PairingEngine>::Fr,
    <MNT4_298 as PairingEngine>::Fr
);
nonnative_test!(
    PallasFrMNT6Fr,
    ark_pallas::Fr,
    <MNT6_753 as PairingEngine>::Fr
);
nonnative_test!(
    MNT6FrPallasFr,
    <MNT6_753 as PairingEngine>::Fr,
    ark_pallas::Fr
);
nonnative_test!(PallasFqFr, ark_pallas::Fq, ark_pallas::Fr);
nonnative_test!(PallasFrFq, ark_pallas::Fr, ark_pallas::Fq);
