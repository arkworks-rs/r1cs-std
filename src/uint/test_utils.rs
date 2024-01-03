use ark_relations::r1cs::{ConstraintSystem, SynthesisError};
use std::ops::RangeInclusive;

use crate::test_utils::{self, modes};

use super::*;

pub(crate) fn test_unary_op<T: PrimUInt, const N: usize, F: PrimeField>(
    a: T,
    mode: AllocationMode,
    test: impl FnOnce(UInt<N, T, F>) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError> {
    let cs = ConstraintSystem::<F>::new_ref();
    let a = UInt::<N, T, F>::new_variable(cs.clone(), || Ok(a), mode)?;
    test(a)
}

pub(crate) fn test_binary_op<T: PrimUInt, const N: usize, F: PrimeField>(
    a: T,
    b: T,
    mode_a: AllocationMode,
    mode_b: AllocationMode,
    test: impl FnOnce(UInt<N, T, F>, UInt<N, T, F>) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError> {
    let cs = ConstraintSystem::<F>::new_ref();
    let a = UInt::<N, T, F>::new_variable(cs.clone(), || Ok(a), mode_a)?;
    let b = UInt::<N, T, F>::new_variable(cs.clone(), || Ok(b), mode_b)?;
    test(a, b)
}

pub(crate) fn test_binary_op_with_native<T: PrimUInt, const N: usize, F: PrimeField>(
    a: T,
    b: T,
    mode_a: AllocationMode,
    test: impl FnOnce(UInt<N, T, F>, T) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError> {
    let cs = ConstraintSystem::<F>::new_ref();
    let a = UInt::<N, T, F>::new_variable(cs.clone(), || Ok(a), mode_a)?;
    test(a, b)
}

pub(crate) fn run_binary_random_both<const ITERATIONS: usize, const N: usize, T, F>(
    test: impl Fn(UInt<N, T, F>, UInt<N, T, F>) -> Result<(), SynthesisError> + Copy,
    test_native: impl Fn(UInt<N, T, F>, T) -> Result<(), SynthesisError> + Copy,
) -> Result<(), SynthesisError>
where
    T: PrimUInt,
    F: PrimeField,
{
    let mut rng = ark_std::test_rng();

    for _ in 0..ITERATIONS {
        for mode_a in modes() {
            let a = T::rand(&mut rng);
            for mode_b in modes() {
                let b = T::rand(&mut rng);
                test_binary_op(a, b, mode_a, mode_b, test)?;
                test_binary_op_with_native(a, b, mode_a, test_native)?;
            }
        }
    }
    Ok(())
}

pub(crate) fn run_binary_random<const ITERATIONS: usize, const N: usize, T, F>(
    test: impl Fn(UInt<N, T, F>, UInt<N, T, F>) -> Result<(), SynthesisError> + Copy,
) -> Result<(), SynthesisError>
where
    T: PrimUInt,
    F: PrimeField,
{
    let mut rng = ark_std::test_rng();

    for _ in 0..ITERATIONS {
        for mode_a in modes() {
            let a = T::rand(&mut rng);
            for mode_b in modes() {
                let b = T::rand(&mut rng);
                test_binary_op(a, b, mode_a, mode_b, test)?;
            }
        }
    }
    Ok(())
}

pub(crate) fn run_binary_exhaustive<const N: usize, T, F>(
    test: impl Fn(UInt<N, T, F>, UInt<N, T, F>) -> Result<(), SynthesisError> + Copy,
) -> Result<(), SynthesisError>
where
    T: PrimUInt,
    F: PrimeField,
    RangeInclusive<T>: Iterator<Item = T>,
{
    for (mode_a, a) in test_utils::combination(T::min_value()..=T::max_value()) {
        for (mode_b, b) in test_utils::combination(T::min_value()..=T::max_value()) {
            test_binary_op(a, b, mode_a, mode_b, test)?;
        }
    }
    Ok(())
}

pub(crate) fn run_binary_exhaustive_both<const N: usize, T, F>(
    test: impl Fn(UInt<N, T, F>, UInt<N, T, F>) -> Result<(), SynthesisError> + Copy,
    test_native: impl Fn(UInt<N, T, F>, T) -> Result<(), SynthesisError> + Copy,
) -> Result<(), SynthesisError>
where
    T: PrimUInt,
    F: PrimeField,
    RangeInclusive<T>: Iterator<Item = T>,
{
    for (mode_a, a) in test_utils::combination(T::min_value()..=T::max_value()) {
        for (mode_b, b) in test_utils::combination(T::min_value()..=T::max_value()) {
            test_binary_op(a, b, mode_a, mode_b, test)?;
            test_binary_op_with_native(a, b, mode_a, test_native)?;
        }
    }
    Ok(())
}

pub(crate) fn run_binary_random_native_only<const ITERATIONS: usize, const N: usize, T, F>(
    test: impl Fn(UInt<N, T, F>, T) -> Result<(), SynthesisError> + Copy,
) -> Result<(), SynthesisError>
where
    T: PrimUInt,
    F: PrimeField,
{
    let mut rng = ark_std::test_rng();

    for _ in 0..ITERATIONS {
        for mode_a in modes() {
            let a = T::rand(&mut rng);
            let b = T::rand(&mut rng);
            test_binary_op_with_native(a, b, mode_a, test)?;
        }
    }
    Ok(())
}

pub(crate) fn run_binary_exhaustive_native_only<const N: usize, T, F>(
    test: impl Fn(UInt<N, T, F>, T) -> Result<(), SynthesisError> + Copy,
) -> Result<(), SynthesisError>
where
    T: PrimUInt,
    F: PrimeField,
    RangeInclusive<T>: Iterator<Item = T>,
{
    for (mode_a, a) in test_utils::combination(T::min_value()..=T::max_value()) {
        for b in T::min_value()..=T::max_value() {
            test_binary_op_with_native(a, b, mode_a, test)?;
        }
    }
    Ok(())
}

pub(crate) fn run_unary_random<const ITERATIONS: usize, const N: usize, T, F>(
    test: impl Fn(UInt<N, T, F>) -> Result<(), SynthesisError> + Copy,
) -> Result<(), SynthesisError>
where
    T: PrimUInt,
    F: PrimeField,
{
    let mut rng = ark_std::test_rng();

    for _ in 0..ITERATIONS {
        for mode_a in modes() {
            let a = T::rand(&mut rng);
            test_unary_op(a, mode_a, test)?;
        }
    }
    Ok(())
}

pub(crate) fn run_unary_exhaustive<const N: usize, T, F>(
    test: impl Fn(UInt<N, T, F>) -> Result<(), SynthesisError> + Copy,
) -> Result<(), SynthesisError>
where
    T: PrimUInt,
    F: PrimeField,
    RangeInclusive<T>: Iterator<Item = T>,
{
    for (mode, a) in test_utils::combination(T::min_value()..=T::max_value()) {
        test_unary_op(a, mode, test)?;
    }
    Ok(())
}
