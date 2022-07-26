use crate::poly::domain::vanishing_poly::VanishingPolynomial;
use ark_ff::{batch_inversion_and_mul, PrimeField};
use ark_std::vec::Vec;
/// Struct describing Lagrange interpolation for a multiplicative coset I,
/// with |I| a power of 2.
/// TODO: Pull in lagrange poly explanation from libiop
#[derive(Clone)]
pub struct LagrangeInterpolator<F: PrimeField> {
    pub(crate) domain_order: usize,
    pub(crate) all_domain_elems: Vec<F>,
    pub(crate) v_inv_elems: Vec<F>,
    pub(crate) domain_vp: VanishingPolynomial<F>,
    poly_evaluations: Vec<F>,
}

impl<F: PrimeField> LagrangeInterpolator<F> {
    /// Returns a lagrange interpolator, given the domain specification.
    pub fn new(
        domain_offset: F,
        domain_generator: F,
        domain_dim: u64,
        poly_evaluations: Vec<F>,
    ) -> Self {
        let domain_order = 1 << domain_dim;
        assert_eq!(poly_evaluations.len(), domain_order);
        let mut cur_elem = domain_offset;
        let mut all_domain_elems = vec![domain_offset];
        let mut v_inv_elems: Vec<F> = Vec::new();
        // Cache all elements in the domain
        for _ in 1..domain_order {
            cur_elem *= domain_generator;
            all_domain_elems.push(cur_elem);
        }
        // By computing the following elements as constants,
        // we can further reduce the interpolation costs.
        //
        // m = order of the interpolation domain
        // v_inv[i] = prod_{j != i} h(g^i - g^j)
        // We use the following facts to compute this:
        // v_inv[0] = m*h^{m-1}
        // v_inv[i] = g^{-1} * v_inv[i-1]
        // TODO: Include proof of the above two points
        let g_inv = domain_generator.inverse().unwrap();
        let m = F::from((1 << domain_dim) as u128);
        let mut v_inv_i = m * domain_offset.pow([(domain_order - 1) as u64]);
        for _ in 0..domain_order {
            v_inv_elems.push(v_inv_i);
            v_inv_i *= g_inv;
        }

        // TODO: Cache the intermediate terms with Z_H(x) evaluations.
        let vp = VanishingPolynomial::new(domain_offset, domain_dim);

        let lagrange_interpolation: LagrangeInterpolator<F> = LagrangeInterpolator {
            domain_order,
            all_domain_elems,
            v_inv_elems,
            domain_vp: vp,
            poly_evaluations,
        };
        lagrange_interpolation
    }

    pub(crate) fn compute_lagrange_coefficients(&self, interpolation_point: F) -> Vec<F> {
        // Let t be the interpolation point, H be the multiplicative coset, with
        // elements of the form h*g^i. Compute each L_{i,H}(t) as Z_{H}(t) * v_i
        // / (t- h g^i) where:
        // - Z_{H}(t) = \prod_{j} (t-h*g^j) = (t^m-h^m), and
        // - v_{i} = 1 / \prod_{j \neq i} h(g^i-g^j).
        // Below we use the fact that v_{0} = 1/(m * h^(m-1)) and v_{i+1} = g * v_{i}.
        // We first compute the inverse of each coefficient, except for the Z_H(t) term.
        // We then batch invert the entire result, and multiply by Z_H(t).
        let mut inverted_lagrange_coeffs: Vec<F> = Vec::with_capacity(self.all_domain_elems.len());
        for i in 0..self.domain_order {
            let l = self.v_inv_elems[i];
            let r = self.all_domain_elems[i];
            inverted_lagrange_coeffs.push(l * (interpolation_point - r));
        }
        let vp_t = self.domain_vp.evaluate(&interpolation_point);
        let lagrange_coeffs = inverted_lagrange_coeffs.as_mut_slice();
        batch_inversion_and_mul::<F>(lagrange_coeffs, &vp_t);
        lagrange_coeffs.iter().cloned().collect()
    }

    pub fn interpolate(&self, interpolation_point: F) -> F {
        let lagrange_coeffs = self.compute_lagrange_coefficients(interpolation_point);
        let mut interpolation = F::zero();
        for i in 0..self.domain_order {
            interpolation += lagrange_coeffs[i] * self.poly_evaluations[i];
        }
        interpolation
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{fp::FpVar, FieldVar},
        poly::{
            domain::Radix2DomainVar,
            evaluations::univariate::lagrange_interpolator::LagrangeInterpolator,
        },
        R1CSVar,
    };
    use ark_ff::{FftField, Field, One};
    use ark_poly::{univariate::DensePolynomial, Polynomial, UVPolynomial};
    use ark_std::{test_rng, UniformRand};
    use ark_test_curves::bls12_381::Fr;

    #[test]
    pub fn test_native_interpolate() {
        let mut rng = test_rng();
        let poly = DensePolynomial::rand(15, &mut rng);
        let gen = Fr::get_root_of_unity(1 << 4).unwrap();
        assert_eq!(gen.pow(&[1 << 4]), Fr::one());
        let domain = Radix2DomainVar::new(
            gen,
            4, // 2^4 = 16
            FpVar::constant(Fr::GENERATOR),
        )
        .unwrap();
        // generate evaluations of `poly` on this domain
        let mut coset_point = domain.offset().value().unwrap();
        let mut oracle_evals = Vec::new();
        for _ in 0..(1 << 4) {
            oracle_evals.push(poly.evaluate(&coset_point));
            coset_point *= gen;
        }

        let interpolator = LagrangeInterpolator::new(
            domain.offset().value().unwrap(),
            domain.gen,
            domain.dim,
            oracle_evals,
        );

        // the point to evaluate at
        let interpolate_point = Fr::rand(&mut rng);

        let expected = poly.evaluate(&interpolate_point);
        let actual = interpolator.interpolate(interpolate_point);

        assert_eq!(actual, expected)
    }
}
