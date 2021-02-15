use crate::fields::fp::FpVar;
use crate::fields::FieldVar;
use ark_ff::{Field, PrimeField};
use ark_relations::r1cs::SynthesisError;

/// Struct describing vanishing polynomial for a multiplicative coset H where |H| is a power of 2.
/// As H is a coset, every element can be described as h*g^i and therefore
/// has vanishing polynomial Z_H(x) = x^|H| - h^|H|
#[derive(Clone)]
pub struct VanishingPolynomial<F: Field> {
    /// h^|H|
    pub constant_term: F,
    /// log_2(|H|)
    pub dim_h: u64,
    /// |H|
    pub order_h: u64,
}

impl<F: PrimeField> VanishingPolynomial<F> {
    /// returns a VanishingPolynomial of coset `H = h<g>`.
    pub fn new(offset: F, dim_h: u64) -> Self {
        let order_h = 1 << dim_h;
        let vp = VanishingPolynomial {
            constant_term: offset.pow([order_h]),
            dim_h,
            order_h,
        };
        vp
    }

    /// todo: doc
    pub fn evaluate(&self, x: &F) -> F {
        let mut result = x.pow([self.order_h]);
        result -= &self.constant_term;
        result
    }

    /// todo: doc
    pub fn evaluate_constraints(&self, x: &FpVar<F>) -> Result<FpVar<F>, SynthesisError> {
        if self.dim_h == 1 {
            let result = x - x;
            return Ok(result);
        }

        let mut cur = x.square()?;
        for _ in 1..self.dim_h {
            cur.square_in_place()?;
        }
        cur -= &FpVar::Constant(self.constant_term);
        Ok(cur)
    }
}
