mod lagrange_interpolator;

use crate::alloc::AllocVar;
use crate::fields::fp::FpVar;
use crate::fields::FieldVar;
use crate::poly::domain::EvaluationDomain;
use crate::poly::evaluations::univariate::lagrange_interpolator::LagrangeInterpolator;
use crate::R1CSVar;
use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use ark_std::vec::Vec;
#[derive(Clone)]
/// Stores a UV polynomial in evaluation form.
pub struct EvaluationsVar<F: PrimeField> {
    /// Evaluations of univariate polynomial over domain
    pub evals: Vec<FpVar<F>>,
    /// Optional Lagrange Interpolator. Useful for lagrange interpolation.
    pub lagrange_interpolator: Option<LagrangeInterpolator<F>>,
    domain: EvaluationDomain<F>,
}

impl<F: PrimeField> EvaluationsVar<F> {
    /// Construct `Self` from evaluations and a domain.
    /// `interpolate` indicates if user wants to interpolate this polynomial
    /// using lagrange interpolation.
    pub fn from_vec_and_domain(
        evaluations: Vec<FpVar<F>>,
        domain: EvaluationDomain<F>,
        interpolate: bool,
    ) -> Self {
        assert_eq!(
            evaluations.len(),
            1 << domain.dim,
            "evaluations and domain has different dimensions"
        );

        let mut ev = Self {
            evals: evaluations,
            lagrange_interpolator: None,
            domain,
        };
        if interpolate {
            ev.generate_lagrange_interpolator();
        }
        ev
    }

    fn generate_lagrange_interpolator(&mut self) {
        let poly_evaluations_val: Vec<_> = self.evals.iter().map(|v| v.value().unwrap()).collect();
        let domain = &self.domain;
        let lagrange_interpolator =
            LagrangeInterpolator::new(domain.offset, domain.gen, domain.dim, poly_evaluations_val);
        self.lagrange_interpolator = Some(lagrange_interpolator)
    }

    fn compute_lagrange_coefficients(
        &self,
        interpolation_point: &FpVar<F>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let cs = interpolation_point.cs();
        let t = interpolation_point;
        let lagrange_interpolator = self
            .lagrange_interpolator
            .as_ref()
            .expect("lagrange interpolator has not been initialized. ");
        let lagrange_coeffs =
            lagrange_interpolator.compute_lagrange_coefficients(t.value().unwrap());
        let mut lagrange_coeffs_field_gadgat = Vec::new();
        // Now we convert these lagrange coefficients to gadgets, and then constrain them.
        // The i-th lagrange coefficients constraint is:
        // (v_inv[i] * t - v_inv[i] * domain_elem[i]) * (coeff) = 1/Z_I(t)
        let vp_t = lagrange_interpolator.domain_vp.evaluate_constraints(t)?;
        let inv_vp_t = vp_t.inverse()?;
        for i in 0..lagrange_interpolator.domain_order {
            let constant: F =
                (-lagrange_interpolator.all_domain_elems[i]) * lagrange_interpolator.v_inv_elems[i];
            let mut a_element: FpVar<F> =
                t * &FpVar::constant(lagrange_interpolator.v_inv_elems[i]);
            a_element += FpVar::constant(constant);

            let lag_coeff: FpVar<F> =
                FpVar::new_witness(ns!(cs, "generate lagrange coefficient"), || {
                    Ok(lagrange_coeffs[i])
                })?;
            lagrange_coeffs_field_gadgat.push(lag_coeff);
            // Enforce the actual constraint (A_element) * (lagrange_coeff) = 1/Z_I(t)
            a_element.mul_equals(&lagrange_coeffs_field_gadgat[i], &inv_vp_t)?;
        }
        Ok(lagrange_coeffs_field_gadgat)
    }

    /// Returns constraints for Interpolating and evaluating at `interpolation_point`
    pub fn interpolate_and_evaluate(
        &self,
        interpolation_point: &FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let lagrange_interpolator = self
            .lagrange_interpolator
            .as_ref()
            .expect("lagrange interpolator has not been initialized. ");
        let lagrange_coeffs = self.compute_lagrange_coefficients(interpolation_point)?;
        let mut interpolation: FpVar<F> = FpVar::zero();
        for i in 0..lagrange_interpolator.domain_order {
            let intermediate = &lagrange_coeffs[i] * &self.evals[i];
            interpolation += &intermediate
        }

        Ok(interpolation)
    }
}

#[cfg(test)]
mod tests {
    use crate::alloc::AllocVar;
    use crate::fields::fp::FpVar;
    use crate::poly::domain::EvaluationDomain;
    use crate::poly::evaluations::univariate::EvaluationsVar;
    use crate::R1CSVar;
    use ark_ff::{FftField, One, UniformRand};
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly::{Polynomial, UVPolynomial};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::test_rng;
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn test_interpolate() {
        let mut rng = test_rng();
        let poly = DensePolynomial::rand(15, &mut rng);
        let gen = Fr::get_root_of_unity(1 << 4).unwrap();
        let domain = EvaluationDomain {
            gen,
            offset: Fr::multiplicative_generator(),
            dim: 4, // 2^4 = 16
        };
        let mut coset_point = Fr::one();
        let mut evaluations = Vec::new();
        for _ in 0..(1 << 4) {
            evaluations.push(coset_point);
            coset_point *= gen;
        }
        let cs = ConstraintSystem::new_ref();
        let evaluations_fp: Vec<_> = evaluations
            .iter()
            .map(|x| FpVar::new_input(ns!(cs, "evaluations"), || Ok(x)).unwrap())
            .collect();
        let evaluations_var = EvaluationsVar::from_vec_and_domain(evaluations_fp, domain, true);

        let interpolate_point = Fr::rand(&mut rng);
        let interpolate_point_fp =
            FpVar::new_input(ns!(cs, "interpolate point"), || Ok(interpolate_point)).unwrap();

        let expected = poly.evaluate(&interpolate_point);

        let actual = evaluations_var
            .interpolate_and_evaluate(&interpolate_point_fp)
            .unwrap()
            .value()
            .unwrap();

        assert!(cs.is_satisfied().unwrap());
        assert_eq!(actual, expected);
    }
}
