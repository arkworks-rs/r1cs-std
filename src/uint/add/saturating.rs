use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;

use crate::uint::*;
use crate::{boolean::Boolean, R1CSVar};

impl<const N: usize, T: PrimUInt, F: PrimeField> UInt<N, T, F> {
    /// Compute `*self = self.wrapping_add(other)`.
    pub fn saturating_add_in_place(&mut self, other: &Self) {
        let result = Self::saturating_add_many(&[self.clone(), other.clone()]).unwrap();
        *self = result;
    }

    /// Compute `self.wrapping_add(other)`.
    pub fn saturating_add(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.saturating_add_in_place(other);
        result
    }

    /// Perform wrapping addition of `operands`.
    /// Computes `operands[0].wrapping_add(operands[1]).wrapping_add(operands[2])...`.
    ///
    /// The user must ensure that overflow does not occur.
    #[tracing::instrument(target = "r1cs", skip(operands))]
    pub fn saturating_add_many(operands: &[Self]) -> Result<Self, SynthesisError>
    where
        F: PrimeField,
    {
        let (sum_bits, value) = Self::add_many_helper(operands, |a, b| a.saturating_add(b))?;
        if operands.is_constant() {
            // If all operands are constant, then the result is also constant.
            // In this case, we can return early.
            Ok(UInt::constant(value.unwrap()))
        } else if sum_bits.len() == N {
            // No overflow occurred.
            Ok(UInt::from_bits_le(&sum_bits))
        } else {
            // Split the sum into the bottom `N` bits and the top bits.
            let (bottom_bits, top_bits) = sum_bits.split_at(N);

            // Construct a candidate result assuming that no overflow occurred.
            let bits = TryFrom::try_from(bottom_bits.to_vec()).unwrap();
            let candidate_result = UInt { bits, value };

            // Check if any of the top bits is set.
            // If any of them is set, then overflow occurred.
            let overflow_occurred = Boolean::kary_or(&top_bits)?;

            // If overflow occurred, return the maximum value.
            overflow_occurred.select(&Self::MAX, &candidate_result)
        }
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

    fn uint_saturating_add<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
        b: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs().or(b.cs());
        let both_constant = a.is_constant() && b.is_constant();
        let computed = a.saturating_add(&b);
        let expected_mode = if both_constant {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let expected = UInt::new_variable(
            cs.clone(),
            || Ok(a.value()?.saturating_add(b.value()?)),
            expected_mode,
        )?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !both_constant {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    #[test]
    fn u8_saturating_add() {
        run_binary_exhaustive(uint_saturating_add::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_saturating_add() {
        run_binary_random::<1000, 16, _, _>(uint_saturating_add::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_saturating_add() {
        run_binary_random::<1000, 32, _, _>(uint_saturating_add::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_saturating_add() {
        run_binary_random::<1000, 64, _, _>(uint_saturating_add::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_saturating_add() {
        run_binary_random::<1000, 128, _, _>(uint_saturating_add::<u128, 128, Fr>).unwrap()
    }
}
