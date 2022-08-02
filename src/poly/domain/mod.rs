use crate::{
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
};
use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use ark_std::vec::Vec;

pub mod vanishing_poly;

#[derive(Clone, Debug)]
/// Defines an evaluation domain over a prime field. The domain is a coset of
/// size `1<<dim`.
///
/// Native code corresponds to `ark-poly::univariate::domain::radix2`, but
/// `ark-poly` only supports subgroup for now.
// TODO: support cosets in `ark-poly`.
pub struct Radix2DomainVar<F: PrimeField> {
    /// generator of subgroup g
    pub gen: F,
    /// index of the quotient group (i.e. the `offset`)
    offset: FpVar<F>,
    /// dimension of evaluation domain, which is log2(size of coset)
    pub dim: u64,
}
impl<F: PrimeField> Radix2DomainVar<F> {
    /// Construct an evaluation domain with the given offset.
    pub fn new(gen: F, dimension: u64, offset: FpVar<F>) -> Result<Self, SynthesisError> {
        offset.enforce_not_equal(&FpVar::zero())?;
        Ok(Self {
            gen,
            offset,
            dim: dimension,
        })
    }

    /// What is the offset of `self`?
    pub fn offset(&self) -> &FpVar<F> {
        &self.offset
    }
}

impl<F: PrimeField> EqGadget<F> for Radix2DomainVar<F> {
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        if self.gen != other.gen || self.dim != other.dim {
            Ok(Boolean::constant(false))
        } else {
            self.offset.is_eq(&other.offset)
        }
    }
}

impl<F: PrimeField> Radix2DomainVar<F> {
    /// order of the domain
    pub fn order(&self) -> usize {
        1 << self.dim
    }

    /// Returns offset, offset*g, offset*g^2, ..., offset*g^{coset_size}
    pub fn elements(&self) -> Vec<FpVar<F>> {
        let mut result = Vec::new();
        result.push(self.offset.clone());
        for _ in 1..(1 << self.dim) {
            let new_element = result.last().unwrap() * self.gen;
            result.push(new_element);
        }
        result
    }

    /// Size of the domain
    pub fn size(&self) -> u64 {
        1 << self.dim
    }

    /// For domain `h<g>` with dimension `n`, `position` represented by
    /// `query_pos` in big endian form, returns all points of
    /// `h*g^{position}<g^{2^{n-coset_dim}}>`. The result is the query coset at
    /// index `query_pos` for the FRI protocol.
    ///
    /// # Panics
    /// This function panics when `query_pos.len() != coset_dim` or
    /// `query_pos.len() != self.dim`.
    pub fn query_position_to_coset_elements(
        &self,
        query_pos: &[Boolean<F>],
        coset_dim: u64,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        Ok(self
            .query_position_to_coset(query_pos, coset_dim)?
            .elements())
    }

    /// For domain `h<g>` with dimension `n`, `position` represented by
    /// `query_pos` in big endian form, returns all points of
    /// `h*g^{position}<g^{n-query_pos.len()}>`
    ///
    /// # Panics
    /// This function panics when `query_pos.len() < log2_num_cosets`.
    pub fn query_position_to_coset(
        &self,
        query_pos: &[Boolean<F>],
        coset_dim: u64,
    ) -> Result<Self, SynthesisError> {
        let coset_index = truncate_to_coset_index(query_pos, self.dim, coset_dim);
        let offset_var = &self.offset * FpVar::Constant(self.gen).pow_le(&coset_index)?;
        Ok(Self {
            gen: self.gen.pow(&[1 << (self.dim - coset_dim)]), // distance between coset
            offset: offset_var,
            dim: coset_dim,
        })
    }
}

fn truncate_to_coset_index<F: PrimeField>(
    query_pos: &[Boolean<F>],
    codeword_dim: u64,
    coset_dim: u64,
) -> Vec<Boolean<F>> {
    let log2_num_cosets = (codeword_dim - coset_dim) as usize;
    assert!(query_pos.len() >= log2_num_cosets);
    query_pos[0..log2_num_cosets].to_vec()
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;
    use ark_ff::PrimeField;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{rand::Rng, test_rng};

    use crate::{alloc::AllocVar, fields::fp::FpVar, poly::domain::Radix2DomainVar, R1CSVar};

    fn test_query_coset_template<F: PrimeField>() {
        const COSET_DIM: u64 = 7;
        const COSET_SIZE: u64 = 1 << COSET_DIM;
        const LOCALIZATION: u64 = 3;
        let cs = ConstraintSystem::new_ref();
        let mut rng = test_rng();
        let gen = F::get_root_of_unity(COSET_SIZE).unwrap();
        let offset = F::rand(&mut rng);
        let offset_var = FpVar::new_witness(cs.clone(), || Ok(offset)).unwrap();
        let domain = Radix2DomainVar::new(gen, COSET_DIM, offset_var).unwrap();

        let num_cosets = 1 << (COSET_DIM - LOCALIZATION);

        let coset_index = rng.gen_range(0..num_cosets);
        let coset_index_var = UInt32::new_witness(cs.clone(), || Ok(coset_index))
            .unwrap()
            .to_bits_le()
            .into_iter()
            .take(COSET_DIM as usize)
            .collect::<Vec<_>>();

        let elements_actual = domain
            .query_position_to_coset(&coset_index_var, LOCALIZATION)
            .unwrap()
            .elements();

        let elements_expected = domain
            .elements()
            .into_iter()
            .skip(coset_index as usize)
            .step_by(1 << (COSET_DIM - LOCALIZATION))
            .collect::<Vec<_>>();

        assert_eq!(elements_expected.len(), elements_actual.len());

        elements_expected
            .into_iter()
            .zip(elements_actual.into_iter())
            .for_each(|(left, right)| {
                assert_eq!(left.value().unwrap(), right.value().unwrap());
            });
    }

    #[test]
    fn test_on_bls12_381() {
        test_query_coset_template::<ark_bls12_381::Fr>();
    }

    #[test]
    fn test_on_bls12_377() {
        test_query_coset_template::<ark_bls12_377::Fr>();
    }
}
