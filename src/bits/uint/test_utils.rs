use crate::test_utils::modes;

use super::*;
use ark_relations::r1cs::SynthesisError;
use ark_std::UniformRand;
use num_traits::PrimInt;

use std::ops::RangeInclusive;

pub(crate) fn test_unary_op<T: PrimInt + Debug, const N: usize, F: PrimeField>(
    a: T,
    mode: AllocationMode,
    test: impl FnOnce(UInt<N, T, F>) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError> {
    let cs = ConstraintSystem::<F>::new_ref();
    let b = UInt::<N, T, F>::new_variable(cs.clone(), mode_b, || Ok(b));
    test(a)
}

pub(crate) fn test_binary_op<T: PrimInt + Debug, const N: usize, F: PrimeField>(
    a: T,
    b: T,
    mode_a: AllocationMode,
    mode_b: AllocationMode,
    test: impl FnOnce(UInt<N, T, F>) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError> {
    let cs = ConstraintSystem::<F>::new_ref();
    let a = UInt::<N, T, F>::new_variable(cs.clone(), mode_a, || Ok(a));
    let b = UInt::<N, T, F>::new_variable(cs.clone(), mode_b, || Ok(b));
    test(a, b)
}

pub(crate) fn run_binary_random<const ITERATIONS: usize, const N: usize, T, F>(
    test: impl FnOnce(UInt<N, T, F>, UInt<N, T, F>) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError>
where
    T: PrimInt + Debug + UniformRand,
    F: PrimeField,
{
    let mut rng = ark_std::test_rng();

    for i in 0..ITERATIONS {
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
    test: impl FnOnce(UInt<N, T, F>, UInt<N, T, F>) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError>
where
    T: PrimInt + Debug + UniformRand,
    F: PrimeField,
    RangeInclusive<T>: Iterator<Item = T>,
{
    for (a, mode_a) in test_utils::combination(T::min_value()..=T::max_value()) {
        for (b, mode_b) in test_utils::combination(T::min_value()..=T::max_value()) {
            test_binary_op(a, b, mode_a, mode_b, test)?;
        }
    }
    Ok(())
}

pub(crate) fn run_unary_random<const ITERATIONS: usize, const N: usize, T, F>(
    test: impl FnOnce(UInt<N, T, F>) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError>
where
    T: PrimInt + Debug + UniformRand,
    F: PrimeField,
{
    let mut rng = ark_std::test_rng();

    for i in 0..ITERATIONS {
        for mode_a in modes() {
            let a = T::rand(&mut rng);
            for mode_b in modes() {
                let b = T::rand(&mut rng);
                test_unary_op(a, mode_a, test)?;
            }
        }
    }
    Ok(())
}

fn run_unary_exhaustive<const N: usize, T, F>(
    test: impl FnOnce(UInt<N, T, F>) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError>
where
    T: PrimInt + Debug + UniformRand,
    F: PrimeField,
    RangeInclusive<T>: Iterator<Item = T>,
{
    for (a, mode_a) in test_utils::combination(T::min_value()..=T::max_value()) {
        for (b, mode_b) in test_utils::combination(T::min_value()..=T::max_value()) {
            test_unary_op(a, mode_a, test)?;
        }
    }
    Ok(())
}
