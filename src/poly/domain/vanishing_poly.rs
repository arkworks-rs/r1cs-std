use crate::fields::{fp::FpVar, FieldVar};
use ark_ff::{Field, PrimeField};
use ark_relations::r1cs::SynthesisError;
use ark_std::ops::Sub;

/// Struct describing vanishing polynomial for a multiplicative coset H where
/// |H| is a power of 2. As H is a coset, every element can be described as
/// h*g^i and therefore has vanishing polynomial Z_H(x) = x^|H| - h^|H|
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

    /// Evaluates the vanishing polynomial without generating the constraints.
    pub fn evaluate(&self, x: &F) -> F {
        let mut result = x.pow([self.order_h]);
        result -= &self.constant_term;
        result
    }

    /// Evaluates the constraints and just gives you the gadget for the result.
    /// Caution for use in holographic lincheck: The output has 2 entries in one
    /// matrix
    pub fn evaluate_constraints(&self, x: &FpVar<F>) -> Result<FpVar<F>, SynthesisError> {
        if self.dim_h == 1 {
            let result = x.sub(x);
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

#[cfg(test)]
mod tests {
    use crate::{
        alloc::AllocVar, fields::fp::FpVar, poly::domain::vanishing_poly::VanishingPolynomial,
        R1CSVar,
    };
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn constraints_test() {
        let mut rng = test_rng();
        let offset = Fr::rand(&mut rng);
        let cs = ConstraintSystem::new_ref();
        let x = Fr::rand(&mut rng);
        let x_var = FpVar::new_witness(ns!(cs, "x_var"), || Ok(x)).unwrap();
        let vp = VanishingPolynomial::new(offset, 12);
        let native = vp.evaluate(&x);
        let result_var = vp.evaluate_constraints(&x_var).unwrap();
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(result_var.value().unwrap(), native);
    }
}
