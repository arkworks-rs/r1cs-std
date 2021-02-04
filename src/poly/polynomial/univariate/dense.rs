use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;

use crate::fields::fp::FpVar;
use crate::fields::FieldVar;
use ark_std::vec::Vec;

/// Stores a polynomial in coefficient form, where coeffcient is represented by a list of `Fpvar<F>`.
pub struct DensePolynomialVar<F: PrimeField> {
    /// The coefficient of `x^i` is stored at location `i` in `self.coeffs`.
    pub coeffs: Vec<FpVar<F>>,
}

impl<F: PrimeField> DensePolynomialVar<F> {
    /// Constructs a new polynomial from a list of coefficients.
    pub fn from_coefficients_slice(coeffs: &[FpVar<F>]) -> Self {
        Self::from_coefficients_vec(coeffs.to_vec())
    }

    /// Constructs a new polynomial from a list of coefficients.
    pub fn from_coefficients_vec(coeffs: Vec<FpVar<F>>) -> Self {
        Self { coeffs }
    }

    /// Evaluates `self` at the given `point` and just gives you the gadget for the result.
    /// Caution for use in holographic lincheck: The output has 2 entries in one matrix
    pub fn evaluate(&self, point: &FpVar<F>) -> Result<FpVar<F>, SynthesisError> {
        let mut result: FpVar<F> = FpVar::zero();
        // current power of point
        let mut curr_pow_x: FpVar<F> = FpVar::one();
        for i in 0..self.coeffs.len() {
            let term = &curr_pow_x * &self.coeffs[i];
            result += &term;
            curr_pow_x *= point;
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_evaluate() {
        // todo
    }
}
