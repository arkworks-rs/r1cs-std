pub mod lagrange_interpolator;

use crate::alloc::AllocVar;
use crate::fields::fp::FpVar;
use crate::fields::FieldVar;
use crate::poly::domain::Radix2DomainVar;
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
    domain: Radix2DomainVar<F>,
    /// Contains all domain elements of `domain.base_domain`.
    ///
    /// This is a cache for lagrange interpolation when offset is non-constant. Will be `None` if offset is constant
    /// or `interpolate` is set to `false`.
    subgroup_points: Option<Vec<F>>,
}

impl<F: PrimeField> EvaluationsVar<F> {
    /// Construct `Self` from evaluations and a domain.
    /// `interpolate` indicates if user wants to interpolate this polynomial
    /// using lagrange interpolation.
    pub fn from_vec_and_domain(
        evaluations: Vec<FpVar<F>>,
        domain: Radix2DomainVar<F>,
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
            subgroup_points: None,
        };
        if interpolate {
            ev.generate_interpolation_cache();
        }
        ev
    }

    /// Precompute necessary calculation for lagrange interpolation and mark it ready to interpolate
    pub fn generate_interpolation_cache(&mut self) {
        if self.domain.offset.is_constant() {
            let poly_evaluations_val: Vec<_> =
                self.evals.iter().map(|v| v.value().unwrap()).collect();
            let domain = &self.domain;
            let lagrange_interpolator = if let FpVar::Constant(x) = domain.offset {
                LagrangeInterpolator::new(x, domain.gen, domain.dim, poly_evaluations_val)
            } else {
                panic!("Domain offset needs to be constant.")
            };
            self.lagrange_interpolator = Some(lagrange_interpolator)
        } else {
            // calculate all elements of base subgroup so that in later part we don't need to calculate the exponents again
            let mut subgroup_points = Vec::with_capacity(self.domain.size() as usize);
            subgroup_points.push(F::one());
            for i in 1..self.domain.size() as usize {
                subgroup_points.push(subgroup_points[i - 1] * self.domain.gen)
            }
            self.subgroup_points = Some(subgroup_points)
        }
    }

    /// Compute lagrange coefficients for each evaluation, given `interpolation_point`.
    /// Only valid if the domain offset is constant.
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
            Call `self.generate_interpolation_cache` first or set `interpolate` to true in constructor. ");
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
        // specialize: if domain offset is constant, we can optimize to have fewer constraints
        if self.domain.offset.is_constant() {
            self.lagrange_interpolate_with_constant_offset(interpolation_point)
        } else {
            // if domain offset is not constant, then we use standard lagrange interpolation code
            self.lagrange_interpolate_with_non_constant_offset(interpolation_point)
        }
    }

    fn lagrange_interpolate_with_constant_offset(
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

    /// Generate interpolation constraints. We assume at compile time we know the base coset (i.e. `gen`) but not know `offset`.
    fn lagrange_interpolate_with_non_constant_offset(
        &self,
        interpolation_point: &FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        // first, make sure `subgroup_points` is made
        let subgroup_points = self.subgroup_points.as_ref()
            .expect("lagrange interpolator has not been initialized. \
            Call `self.generate_interpolation_cache` first or set `interpolate` to true in constructor. ");
        // Let denote interpolation_point as alpha.
        // Lagrange polynomial for coset element `a` is
        // \frac{1}{size * offset ^ size} * \frac{alpha^size - offset^size}{alpha * a^{-1} - 1}
        // Notice that a = (offset * a') where a' is the corresponding element of base coset

        // let `lhs` become \frac{alpha^size - offset^size}{size * offset ^ size}. This part is shared by all lagrange polynomials
        let coset_offset_to_size = self.domain.offset.pow_by_constant(&[self.domain.size()])?; // offset^size
        let alpha_to_s = interpolation_point.pow_by_constant(&[self.domain.size()])?;
        let lhs_numerator = &alpha_to_s - &coset_offset_to_size;
        let lhs_denominator = &coset_offset_to_size * FpVar::constant(F::from(self.domain.size()));

        let lhs = lhs_numerator.mul_by_inverse(&lhs_denominator)?;

        // `rhs` for coset element `a` is \frac{1}{alpha * a^{-1} - 1} = \frac{1}{alpha * offset^{-1} * a'^{-1} - 1}
        let alpha_coset_offset_inv = interpolation_point.mul_by_inverse(&self.domain.offset)?;

        // `res` stores the sum of all lagrange polynomials evaluated at alpha
        let mut res = FpVar::<F>::zero();

        let domain_size = self.domain.size() as usize;
        for i in 0..domain_size {
            // a'^{-1} where a is the base coset element
            let subgroup_point_inv = subgroup_points[(domain_size - i) % domain_size];
            debug_assert_eq!(subgroup_points[i] * subgroup_point_inv, F::one());
            // alpha * offset^{-1} * a'^{-1} - 1
            let lag_donom = &alpha_coset_offset_inv * subgroup_point_inv - F::one();
            let lag_coeff = lhs.mul_by_inverse(&lag_donom)?;

            let lag_interpoland = &self.evals[i] * lag_coeff;
            res += lag_interpoland
        }

        Ok(res)
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
    /// Performs the `+=` operations, assuming `domain.offset` is equal.
    fn add_assign(&mut self, other: &'a EvaluationsVar<F>) {
        // offset might be unknown at compile time, so we assume offset is equal
        assert!(
            self.domain.gen == other.domain.gen && self.domain.dim == other.domain.dim,
            "domains are unequal"
        );

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
    /// Performs the `-=` operations, assuming `domain.offset` is equal.
    fn sub_assign(&mut self, other: &'a EvaluationsVar<F>) {
        // offset might be unknown at compile time, so we assume offset is equal
        assert!(
            self.domain.gen == other.domain.gen && self.domain.dim == other.domain.dim,
            "domains are unequal"
        );

        self.lagrange_interpolator = None;
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a = &*a - b)
    }
}

impl<'a, 'b, F: PrimeField> Mul<&'a EvaluationsVar<F>> for &'b EvaluationsVar<F> {
    type Output = EvaluationsVar<F>;

    /// Performs the `*` operations, assuming `domain.offset` is equal.
    fn mul(self, rhs: &'a EvaluationsVar<F>) -> Self::Output {
        let mut result = self.clone();
        result *= rhs;
        result
    }
}

impl<'a, F: PrimeField> MulAssign<&'a EvaluationsVar<F>> for EvaluationsVar<F> {
    /// Performs the `*=` operations, assuming `domain.offset` is equal.
    fn mul_assign(&mut self, other: &'a EvaluationsVar<F>) {
        // offset might be unknown at compile time, so we assume offset is equal
        assert!(
            self.domain.gen == other.domain.gen && self.domain.dim == other.domain.dim,
            "domains are unequal"
        );

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
    /// Performs the `/=` operations, assuming `domain.offset` is equal.
    fn div_assign(&mut self, other: &'a EvaluationsVar<F>) {
        // offset might be unknown at compile time, so we assume offset is equal
        assert!(
            self.domain.gen == other.domain.gen && self.domain.dim == other.domain.dim,
            "domains are unequal"
        );
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
    use crate::fields::FieldVar;
    use crate::poly::domain::Radix2DomainVar;
    use crate::poly::evaluations::univariate::EvaluationsVar;
    use crate::R1CSVar;
    use ark_ff::{FftField, Field, One, UniformRand};
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly::{Polynomial, UVPolynomial};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::test_rng;
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn test_interpolate_constant_offset() {
        let mut rng = test_rng();
        let poly = DensePolynomial::rand(15, &mut rng);
        let gen = Fr::get_root_of_unity(1 << 4).unwrap();
        assert_eq!(gen.pow(&[1 << 4]), Fr::one());
        let domain = Radix2DomainVar {
            gen,
            offset: FpVar::constant(Fr::rand(&mut rng)),
            dim: 4, // 2^4 = 16
        };
        let mut coset_point = domain.offset.value().unwrap();
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
        println!("number of constraints: {}", cs.num_constraints())
    }

    #[test]
    fn test_interpolate_non_constant_offset() {
        let mut rng = test_rng();
        let poly = DensePolynomial::rand(15, &mut rng);
        let gen = Fr::get_root_of_unity(1 << 4).unwrap();
        assert_eq!(gen.pow(&[1 << 4]), Fr::one());
        let cs = ConstraintSystem::new_ref();
        let domain = Radix2DomainVar {
            gen,
            offset: FpVar::new_witness(ns!(cs, "offset"), || Ok(Fr::rand(&mut rng))).unwrap(),
            dim: 4, // 2^4 = 16
        };
        let mut coset_point = domain.offset.value().unwrap();
        let mut oracle_evals = Vec::new();
        for _ in 0..(1 << 4) {
            oracle_evals.push(poly.evaluate(&coset_point));
            coset_point *= gen;
        }

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
        println!("number of constraints: {}", cs.num_constraints())
    }

    #[test]
    fn test_division() {
        let mut rng = test_rng();
        let gen = Fr::get_root_of_unity(1 << 4).unwrap();
        assert_eq!(gen.pow(&[1 << 4]), Fr::one());
        let domain = Radix2DomainVar {
            gen,
            offset: FpVar::constant(Fr::multiplicative_generator()),
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
