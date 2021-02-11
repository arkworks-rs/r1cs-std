use crate::boolean::Boolean;
use crate::fields::fp::FpVar;
use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use ark_std::vec::Vec;

pub mod vanishing_poly;

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
/// Defines an evaluation domain over a prime field.
/// This domain is `h<g>` where g is `gen` and h is `offset`. The size of coset is `dim`.
pub struct EvaluationDomain<F: PrimeField> {
    /// generator of subgroup g
    pub gen: F,
    /// index of the quotient group
    pub offset: F,
    /// dimension of evaluation domain
    pub dim: u64,
}

impl<F: PrimeField> EvaluationDomain<F> {
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
        _query_pos: &[Boolean<F>],
        _coset_dim: u64,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        self.powers_of_gen(1);
        todo!()
    }
}
