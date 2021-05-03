use crate::boolean::Boolean;
use crate::fields::fp::FpVar;
use crate::fields::FieldVar;
use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use ark_std::vec::Vec;

pub mod vanishing_poly;

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
/// Defines an evaluation domain over a prime field. The domain is a coset of size `1<<dim`.
/// This domain is `h<g>` where g is `gen` and h is `offset`.
pub struct EvaluationDomainVar<F: PrimeField> {
    /// generator of subgroup g
    pub gen: F,
    /// index of the quotient group (i.e. the `offset`)
    pub offset: F,
    /// dimension of evaluation domain
    pub dim: u64,
}

impl<F: PrimeField> EvaluationDomainVar<F> {
    /// order of the domain
    pub fn order(&self) -> usize {
        1 << self.dim
    }

    /// Returns g, g^2, ..., g^{dim}
    fn powers_of_gen(&self, dim: usize) -> Vec<F> {
        let mut result = Vec::new();
        let mut cur = self.gen;
        for _ in 0..dim {
            result.push(cur);
            cur = cur * cur;
        }
        result
    }

    /// For domain `h<g>` with dimension `n`, `position` represented by `query_pos` in big endian form,
    /// returns `h*g^{position}<g^{n-query_pos.len()}>`
    pub fn query_position_to_coset(
        &self,
        query_pos: &[Boolean<F>],
        coset_dim: u64,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let mut coset_index = query_pos;
        assert!(
            query_pos.len() == self.dim as usize
                || query_pos.len() == (self.dim - coset_dim) as usize
        );
        if query_pos.len() == self.dim as usize {
            coset_index = &coset_index[0..(coset_index.len() - coset_dim as usize)];
        }
        let mut coset = Vec::new();
        let powers_of_g = &self.powers_of_gen(self.dim as usize)[(coset_dim as usize)..];

        let mut first_point_in_coset: FpVar<F> = FpVar::zero();
        for i in 0..coset_index.len() {
            let term = coset_index[i].select(&FpVar::constant(powers_of_g[i]), &FpVar::zero())?;
            first_point_in_coset += &term;
        }

        first_point_in_coset *= &FpVar::Constant(self.offset);

        coset.push(first_point_in_coset);
        for i in 1..(1 << (coset_dim as usize)) {
            let new_elem = &coset[i - 1] * &FpVar::Constant(self.gen);
            coset.push(new_elem);
        }

        Ok(coset)
    }
}
