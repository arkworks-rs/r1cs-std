use crate::alloc::{AllocVar, AllocationMode};
use crate::boolean::Boolean;
use crate::eq::EqGadget;
use crate::fields::fp::FpVar;
use crate::fields::FieldVar;
use crate::GR1CSVar;
use ark_ff::{BigInteger, PrimeField};
use ark_relations::gr1cs::SynthesisError;

/// Enforces that `value` is in the range [0, 2^BITS) (exclusive). This is done by
/// introducing `BITS` new boolean variables and reconstructing the value from them.
///
/// Cost: `BITS` new variables and `BITS + 1` new R1Cs.
pub fn enforce_bit_bound<F: PrimeField, const BITS: usize>(
    value: &FpVar<F>,
) -> Result<(), SynthesisError> {
    assert_bits_fit::<F, BITS>();
    let bit_decomposition = to_bits::<_, BITS>(value)?;
    let reconstruction = Boolean::le_bits_to_fp(&bit_decomposition)?;
    reconstruction.enforce_equal(value)
}

/// Given a field element, get its `N` least significant bits as a vector of `Boolean`s in the
/// little-endian order.
pub fn to_bits<F: PrimeField, const BITS: usize>(
    value: &FpVar<F>,
) -> Result<[Boolean<F>; BITS], SynthesisError> {
    assert_bits_fit::<F, BITS>();
    let mut bits = [Boolean::FALSE; BITS];
    if !value.cs().is_in_setup_mode() {
        for (i, bit) in bits.iter_mut().enumerate() {
            *bit = Boolean::new_variable(
                value.cs(),
                || Ok(value.value()?.into_bigint().get_bit(i)),
                result_allocation_mode(&value, &value),
            )?;
        }
    }
    Ok(bits)
}

/// Computes the minimum of two field elements `a` and `b`.
///
/// This is done using slack variables to ensure that the result is correct without directly
/// comparing the two values.
///
/// # Requirements
///
/// 1. `a` and `b` MUST be in the range [0, 1 << `BITS`): this is ASSUMED, not enforced.
/// 2. `BITS` must be strictly less than the floor of log2 of the field's modulus (to avoid overflow).
pub fn min<F: PrimeField, const BITS: usize>(
    a: &FpVar<F>,
    b: &FpVar<F>,
) -> Result<FpVar<F>, SynthesisError> {
    assert_bits_fit_for_sum::<F, BITS>();
    let (_, a_over_b) = get_slacks_checked::<F, BITS>(a, b)?;
    Ok(a - a_over_b)
}

/// Computes the maximum of two field elements `a` and `b`.
///
/// This is done using slack variables to ensure that the result is correct without directly
/// comparing the two values.
///
/// # Requirements
///
/// 1. `a` and `b` MUST be in the range [0, 1 << `BITS`): this is ASSUMED, not enforced.
/// 2. `BITS` must be strictly less than the floor of log2 of the field's modulus (to avoid overflow).
pub fn max<F: PrimeField, const BITS: usize>(
    a: &FpVar<F>,
    b: &FpVar<F>,
) -> Result<FpVar<F>, SynthesisError> {
    assert_bits_fit_for_sum::<F, BITS>();
    let (b_over_a, _) = get_slacks_checked::<F, BITS>(a, b)?;
    Ok(a + b_over_a)
}

fn assert_bits_fit<F: PrimeField, const BITS: usize>() {
    assert!(
        BITS < F::MODULUS_BIT_SIZE as usize,
        "BITS must be less than the field's modulus bit size to avoid overflow"
    );
}

fn assert_bits_fit_for_sum<F: PrimeField, const BITS: usize>() {
    assert!(
        BITS + 1 < F::MODULUS_BIT_SIZE as usize,
        "BITS + 1 must be less than the field's modulus bit size to avoid overflow during addition"
    );
}

fn get_slacks_checked<F: PrimeField, const BITS: usize>(
    a: &FpVar<F>,
    b: &FpVar<F>,
) -> Result<(FpVar<F>, FpVar<F>), SynthesisError> {
    let lt_slack = get_slack(a, b)?;
    let gt_slack = get_slack(b, a)?;

    // (1) Ensure that `lt_slack` and `gt_slack` are within [0, 1 << BITS)
    enforce_bit_bound::<_, BITS>(&lt_slack)?;
    enforce_bit_bound::<_, BITS>(&gt_slack)?;

    // (2) Ensure that `lt_slack` and `gt_slack` are mutually exclusive
    lt_slack.mul_equals(&gt_slack, &FpVar::zero())?;

    // (3) Check the balance condition
    (a + &lt_slack).enforce_equal(&(b + &gt_slack))?;

    Ok((lt_slack, gt_slack))
}

/// Return the difference between `to` and `from` if `from < to`, otherwise return zero.
///
/// Warning: the value is not constrained in any way!
fn get_slack<F: PrimeField>(from: &FpVar<F>, to: &FpVar<F>) -> Result<FpVar<F>, SynthesisError> {
    FpVar::new_variable(
        from.cs().or(to.cs()),
        || {
            let (from, to) = (from.value()?, to.value()?);
            if from < to {
                Ok(to - from)
            } else {
                Ok(F::zero())
            }
        },
        result_allocation_mode(&from, &to),
    )
}

/// Determines the allocation mode for the result based on whether `a` and `b` are constants or not.
fn result_allocation_mode<F: PrimeField>(a: &FpVar<F>, b: &FpVar<F>) -> AllocationMode {
    match a.is_constant() && b.is_constant() {
        true => AllocationMode::Constant,
        false => AllocationMode::Witness,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fields::fp::FpVar;
    use crate::test_utils::modes;
    use crate::uint::PrimUInt;
    use crate::{test_utils, GR1CSVar};
    use ark_bls12_381::Fr;
    use ark_ff::PrimeField;
    use ark_relations::gr1cs::{ConstraintSystem, ConstraintSystemRef, SynthesisError};
    use std::ops::RangeInclusive;

    fn check_min_max<T: PrimUInt, F: PrimeField + From<T>, const BITS: usize>(
        a: T,
        b: T,
        mode_a: AllocationMode,
        mode_b: AllocationMode,
    ) -> Result<(), SynthesisError> {
        // 1) Prepare R1CS
        let cs = ConstraintSystem::<F>::new_ref();

        // 2) Allocate input variables
        let a_var = FpVar::<F>::new_variable(cs.clone(), || Ok(F::from(a)), mode_a)?;
        let b_var = FpVar::<F>::new_variable(cs.clone(), || Ok(F::from(b)), mode_b)?;

        // 3) Run `min` gadget and check increase in constraints and variables
        let min_result = run_and_check_cs_growth::<_, _, BITS>(cs.clone(), mode_a, mode_b, || {
            min::<F, BITS>(&a_var, &b_var)
        })?;

        // 4) Validate the result both in R1CS and in native Rust
        let expected_min = FpVar::new_constant(cs.clone(), F::from(a.min(b)))?;
        min_result.enforce_equal(&expected_min)?;
        assert_eq!(min_result.value(), expected_min.value());

        // 5) Run `max` gadget and check increase in constraints and variables
        let max_result = run_and_check_cs_growth::<_, _, BITS>(cs.clone(), mode_a, mode_b, || {
            max::<F, BITS>(&a_var, &b_var)
        })?;

        // 6) Validate the result both in R1CS and in native Rust
        let expected_max = FpVar::new_constant(cs.clone(), F::from(a.max(b)))?;
        max_result.enforce_equal(&expected_max)?;
        assert_eq!(max_result.value(), expected_max.value());

        // 7) Ensure that the constraint system is satisfied
        if !cs.is_none() && !cs.is_in_setup_mode() {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    fn run_and_check_cs_growth<F: PrimeField, T, const BITS: usize>(
        cs: ConstraintSystemRef<F>,
        mode_a: AllocationMode,
        mode_b: AllocationMode,
        action: impl Fn() -> Result<T, SynthesisError>,
    ) -> Result<T, SynthesisError> {
        let n_constraints = cs.num_constraints();
        let n_variables = cs.num_variables();

        let result = action()?;

        match (mode_a, mode_b) {
            (AllocationMode::Constant, AllocationMode::Constant) => {},
            _ => {
                assert_eq!(cs.num_constraints(), n_constraints + 2 * BITS + 4);
                assert_eq!(cs.num_variables(), n_variables + 2 * BITS + 2);
            },
        };

        Ok(result)
    }

    fn run_exhaustive<T: PrimUInt, F: PrimeField + From<T>, const BITS: usize>(
    ) -> Result<(), SynthesisError>
    where
        RangeInclusive<T>: Iterator<Item = T>,
    {
        for (mode_a, a) in test_utils::combination(T::min_value()..=T::max_value()) {
            for (mode_b, b) in test_utils::combination(T::min_value()..=T::max_value()) {
                check_min_max::<T, F, BITS>(a, b, mode_a, mode_b)?;
            }
        }
        Ok(())
    }

    fn run_random<
        T: PrimUInt,
        F: PrimeField + From<T>,
        const BITS: usize,
        const ITERATIONS: usize,
    >() -> Result<(), SynthesisError> {
        let mut rng = ark_std::test_rng();

        for _ in 0..ITERATIONS {
            for mode_a in modes() {
                let a = T::rand(&mut rng);
                for mode_b in modes() {
                    let b = T::rand(&mut rng);
                    check_min_max::<T, F, BITS>(a, b, mode_a, mode_b)?;
                }
            }
        }

        Ok(())
    }

    #[test]
    fn u8() {
        run_exhaustive::<u8, Fr, 8>().unwrap()
    }

    #[test]
    fn u16() {
        run_random::<u16, Fr, 16, 1000>().unwrap()
    }

    #[test]
    fn u32() {
        run_random::<u16, Fr, 16, 1000>().unwrap()
    }

    #[test]
    fn u64() {
        run_random::<u16, Fr, 16, 1000>().unwrap()
    }

    #[test]
    fn u128() {
        run_random::<u16, Fr, 16, 1000>().unwrap()
    }
}
