mod lagrange_interpolator;

use crate::alloc::AllocVar;
use crate::fields::fp::FpVar;
use crate::fields::FieldVar;
use crate::poly::domain::EvaluationDomain;
use crate::poly::evaluations::univariate::lagrange_interpolator::LagrangeInterpolator;
use crate::R1CSVar;
use ark_ff::{batch_inversion, PrimeField};
use ark_relations::r1cs::SynthesisError;
use ark_std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
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

    /// Generate lagrange interpolator and mark it ready to interpolate
    pub fn generate_lagrange_interpolator(&mut self) {
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
        // ref: https://github.com/alexchmit/perfect-constraints/blob/79692f2652a95a57f2c7187f5b5276345e680230/fractal/src/algebra/lagrange_interpolation.rs#L159
        let cs = interpolation_point.cs();
        let t = interpolation_point;
        let lagrange_interpolator = self
            .lagrange_interpolator
            .as_ref()
            .expect("lagrange interpolator has not been initialized. \
            Call `self.generate_lagrange_interpolator` first or set `interpolate` to true in constructor. ");
        let lagrange_coeffs =
            lagrange_interpolator.compute_lagrange_coefficients(t.value().unwrap());
        let mut lagrange_coeffs_fg = Vec::new();
        // Now we convert these lagrange coefficients to gadgets, and then constrain them.
        // The i-th lagrange coefficients constraint is:
        // (v_inv[i] * t - v_inv[i] * domain_elem[i]) * (coeff) = 1/Z_I(t)
        let vp_t = lagrange_interpolator.domain_vp.evaluate_constraints(t)?;
        // let inv_vp_t = vp_t.inverse()?;
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
            // Enforce the actual constraint (A_element) * (lagrange_coeff) = 1/Z_I(t)
            assert_eq!(
                (lagrange_interpolator.v_inv_elems[i] * t.value().unwrap()
                    - lagrange_interpolator.v_inv_elems[i]
                        * lagrange_interpolator.all_domain_elems[i])
                    * lagrange_coeffs[i],
                vp_t.value().unwrap()
            );
            a_element.mul_equals(&lag_coeff, &vp_t)?;
            lagrange_coeffs_fg.push(lag_coeff);
        }
        Ok(lagrange_coeffs_fg)
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

impl<'a, 'b, F: PrimeField> Add<&'a EvaluationsVar<F>> for &'b EvaluationsVar<F> {
    type Output = EvaluationsVar<F>;

    fn add(self, rhs: &'a EvaluationsVar<F>) -> Self::Output {
        let mut result = self.clone();
        result += rhs;
        result
    }
}

impl<'a, F: PrimeField> AddAssign<&'a EvaluationsVar<F>> for EvaluationsVar<F> {
    fn add_assign(&mut self, other: &'a EvaluationsVar<F>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");

        self.lagrange_interpolator = None;
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a = &*a + b)
    }
}

impl<'a, 'b, F: PrimeField> Sub<&'a EvaluationsVar<F>> for &'b EvaluationsVar<F> {
    type Output = EvaluationsVar<F>;

    fn sub(self, rhs: &'a EvaluationsVar<F>) -> Self::Output {
        let mut result = self.clone();
        result -= rhs;
        result
    }
}

impl<'a, F: PrimeField> SubAssign<&'a EvaluationsVar<F>> for EvaluationsVar<F> {
    fn sub_assign(&mut self, other: &'a EvaluationsVar<F>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");

        self.lagrange_interpolator = None;
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a = &*a - b)
    }
}

impl<'a, 'b, F: PrimeField> Mul<&'a EvaluationsVar<F>> for &'b EvaluationsVar<F> {
    type Output = EvaluationsVar<F>;

    fn mul(self, rhs: &'a EvaluationsVar<F>) -> Self::Output {
        let mut result = self.clone();
        result *= rhs;
        result
    }
}

impl<'a, F: PrimeField> MulAssign<&'a EvaluationsVar<F>> for EvaluationsVar<F> {
    fn mul_assign(&mut self, other: &'a EvaluationsVar<F>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");

        self.lagrange_interpolator = None;
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a = &*a * b)
    }
}

impl<'a, 'b, F: PrimeField> Div<&'a EvaluationsVar<F>> for &'b EvaluationsVar<F> {
    type Output = EvaluationsVar<F>;

    fn div(self, rhs: &'a EvaluationsVar<F>) -> Self::Output {
        let mut result = self.clone();
        result /= rhs;
        result
    }
}

impl<'a, F: PrimeField> DivAssign<&'a EvaluationsVar<F>> for EvaluationsVar<F> {
    fn div_assign(&mut self, other: &'a EvaluationsVar<F>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");
        let cs = self.evals[0].cs();
        // the prover can generate result = (1 / other) * self offline
        let mut result_val: Vec<_> = other.evals.iter().map(|x| x.value().unwrap()).collect();
        batch_inversion(&mut result_val);
        result_val
            .iter_mut()
            .zip(&self.evals)
            .for_each(|(a, self_var)| *a *= self_var.value().unwrap());
        let result_var: Vec<_> = result_val
            .iter()
            .map(|x| FpVar::new_witness(ns!(cs, "div result"), || Ok(*x)).unwrap())
            .collect();
        // enforce constraint
        for i in 0..result_var.len() {
            result_var[i]
                .mul_equals(&other.evals[i], &self.evals[i])
                .unwrap();
        }

        self.lagrange_interpolator = None;
        self.evals = result_var
    }
}

#[cfg(test)]
mod tests {
    use crate::alloc::AllocVar;
    use crate::fields::fp::FpVar;
    use crate::poly::domain::EvaluationDomain;
    use crate::poly::evaluations::univariate::EvaluationsVar;
    use crate::R1CSVar;
    use ark_ff::{FftField, Field, One, UniformRand};
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
        assert_eq!(gen.pow(&[1 << 4]), Fr::one());
        let domain = EvaluationDomain {
            gen,
            offset: Fr::multiplicative_generator(),
            dim: 4, // 2^4 = 16
        };
        let mut coset_point = domain.offset;
        let mut oracle_evals = Vec::new();
        for _ in 0..(1 << 4) {
            oracle_evals.push(poly.evaluate(&coset_point));
            coset_point *= gen;
        }
        let cs = ConstraintSystem::new_ref();
        let evaluations_fp: Vec<_> = oracle_evals
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

        assert_eq!(actual, expected);
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_division() {
        let mut rng = test_rng();
        let gen = Fr::get_root_of_unity(1 << 4).unwrap();
        assert_eq!(gen.pow(&[1 << 4]), Fr::one());
        let domain = EvaluationDomain {
            gen,
            offset: Fr::multiplicative_generator(),
            dim: 4, // 2^4 = 16
        };

        let cs = ConstraintSystem::new_ref();

        let ev_a = EvaluationsVar::from_vec_and_domain(
            (0..16)
                .map(|_| FpVar::new_input(ns!(cs, "poly_a"), || Ok(Fr::rand(&mut rng))).unwrap())
                .collect(),
            domain.clone(),
            false,
        );
        let ev_b = EvaluationsVar::from_vec_and_domain(
            (0..16)
                .map(|_| FpVar::new_input(ns!(cs, "poly_a"), || Ok(Fr::rand(&mut rng))).unwrap())
                .collect(),
            domain.clone(),
            false,
        );

        let a_div_b = (&ev_a) / (&ev_b);
        assert!(cs.is_satisfied().unwrap());
        let b_div_a = (&ev_b) / (&ev_a);

        let one = &a_div_b * &b_div_a;
        for ev in one.evals.iter() {
            assert!(Fr::is_one(&ev.value().unwrap()))
        }

        assert!(cs.is_satisfied().unwrap());
    }
}
