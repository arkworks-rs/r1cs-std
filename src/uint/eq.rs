use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use ark_std::vec::Vec;

use crate::boolean::Boolean;
use crate::eq::EqGadget;

use super::*;

impl<const N: usize, T: PrimUInt, ConstraintF: PrimeField> EqGadget<ConstraintF>
    for UInt<N, T, ConstraintF>
{
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn is_eq(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        let chunk_size = usize::try_from(ConstraintF::MODULUS_BIT_SIZE - 1).unwrap();
        let chunks_are_eq = self
            .bits
            .chunks(chunk_size)
            .zip(other.bits.chunks(chunk_size))
            .map(|(a, b)| {
                let a = Boolean::le_bits_to_fp(a)?;
                let b = Boolean::le_bits_to_fp(b)?;
                a.is_eq(&b)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Boolean::kary_and(&chunks_are_eq)
    }

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let chunk_size = usize::try_from(ConstraintF::MODULUS_BIT_SIZE - 1).unwrap();
        for (a, b) in self
            .bits
            .chunks(chunk_size)
            .zip(other.bits.chunks(chunk_size))
        {
            let a = Boolean::le_bits_to_fp(a)?;
            let b = Boolean::le_bits_to_fp(b)?;
            a.conditional_enforce_equal(&b, condition)?;
        }
        Ok(())
    }

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        condition: &Boolean<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let chunk_size = usize::try_from(ConstraintF::MODULUS_BIT_SIZE - 1).unwrap();
        for (a, b) in self
            .bits
            .chunks(chunk_size)
            .zip(other.bits.chunks(chunk_size))
        {
            let a = Boolean::le_bits_to_fp(a)?;
            let b = Boolean::le_bits_to_fp(b)?;
            a.conditional_enforce_not_equal(&b, condition)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        alloc::{AllocVar, AllocationMode},
        prelude::EqGadget,
        uint::test_utils::{run_binary_exhaustive, run_binary_random},
        R1CSVar,
    };
    use ark_ff::PrimeField;
    use ark_test_curves::bls12_381::Fr;

    fn uint_eq<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
        b: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs().or(b.cs());
        let both_constant = a.is_constant() && b.is_constant();
        let computed = a.is_eq(&b)?;
        let expected_mode = if both_constant {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let expected =
            Boolean::new_variable(cs.clone(), || Ok(a.value()? == b.value()?), expected_mode)?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !both_constant {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    fn uint_neq<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
        b: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs().or(b.cs());
        let both_constant = a.is_constant() && b.is_constant();
        let computed = a.is_neq(&b)?;
        let expected_mode = if both_constant {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let expected =
            Boolean::new_variable(cs.clone(), || Ok(a.value()? != b.value()?), expected_mode)?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !both_constant {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    #[test]
    fn u8_eq() {
        run_binary_exhaustive(uint_eq::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_eq() {
        run_binary_random::<1000, 16, _, _>(uint_eq::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_eq() {
        run_binary_random::<1000, 32, _, _>(uint_eq::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_eq() {
        run_binary_random::<1000, 64, _, _>(uint_eq::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_eq() {
        run_binary_random::<1000, 128, _, _>(uint_eq::<u128, 128, Fr>).unwrap()
    }

    #[test]
    fn u8_neq() {
        run_binary_exhaustive(uint_neq::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_neq() {
        run_binary_random::<1000, 16, _, _>(uint_neq::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_neq() {
        run_binary_random::<1000, 32, _, _>(uint_neq::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_neq() {
        run_binary_random::<1000, 64, _, _>(uint_neq::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_neq() {
        run_binary_random::<1000, 128, _, _>(uint_neq::<u128, 128, Fr>).unwrap()
    }
}
