use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use ark_std::fmt::Debug;

use num_traits::PrimInt;

use crate::boolean::Boolean;
use crate::eq::EqGadget;

use super::UInt;

impl<const N: usize, T: PrimInt + Debug, ConstraintF: PrimeField> EqGadget<ConstraintF>
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
                let a = Boolean::le_bits_to_fp_var(a)?;
                let b = Boolean::le_bits_to_fp_var(b)?;
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
            let a = Boolean::le_bits_to_fp_var(a)?;
            let b = Boolean::le_bits_to_fp_var(b)?;
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
            let a = Boolean::le_bits_to_fp_var(a)?;
            let b = Boolean::le_bits_to_fp_var(b)?;
            a.conditional_enforce_not_equal(&b, condition)?;
        }
        Ok(())
    }
}
