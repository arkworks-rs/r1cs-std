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
    for (i, bit) in bits.iter_mut().enumerate() {
        *bit = Boolean::new_witness(value.cs(), || Ok(value.value()?.into_bigint().get_bit(i)))?;
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
    let expected_mode = match from.is_constant() && to.is_constant() {
        true => AllocationMode::Constant,
        false => AllocationMode::Witness,
    };

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
        expected_mode,
    )
}
