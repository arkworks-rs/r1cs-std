use crate::test_utils;

use super::*;
use ark_relations::r1cs::{ConstraintSystem, SynthesisError};

pub(crate) fn test_unary_op<F: Field>(
    a: bool,
    mode: AllocationMode,
    test: impl FnOnce(Boolean<F>) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError> {
    let cs = ConstraintSystem::<F>::new_ref();
    let a = Boolean::<F>::new_variable(cs.clone(), || Ok(a), mode)?;
    test(a)
}

pub(crate) fn test_binary_op<F: Field>(
    a: bool,
    b: bool,
    mode_a: AllocationMode,
    mode_b: AllocationMode,
    test: impl FnOnce(Boolean<F>, Boolean<F>) -> Result<(), SynthesisError>,
) -> Result<(), SynthesisError> {
    let cs = ConstraintSystem::<F>::new_ref();
    let a = Boolean::<F>::new_variable(cs.clone(), || Ok(a), mode_a)?;
    let b = Boolean::<F>::new_variable(cs.clone(), || Ok(b), mode_b)?;
    test(a, b)
}

pub(crate) fn run_binary_exhaustive<F: Field>(
    test: impl Fn(Boolean<F>, Boolean<F>) -> Result<(), SynthesisError> + Copy,
) -> Result<(), SynthesisError> {
    for (mode_a, a) in test_utils::combination([false, true].into_iter()) {
        for (mode_b, b) in test_utils::combination([false, true].into_iter()) {
            test_binary_op(a, b, mode_a, mode_b, test)?;
        }
    }
    Ok(())
}

pub(crate) fn run_unary_exhaustive<F: Field>(
    test: impl Fn(Boolean<F>) -> Result<(), SynthesisError> + Copy,
) -> Result<(), SynthesisError> {
    for (mode, a) in test_utils::combination([false, true].into_iter()) {
        test_unary_op(a, mode, test)?;
    }
    Ok(())
}
