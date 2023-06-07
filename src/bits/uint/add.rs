use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use ark_std::fmt::Debug;

use num_traits::{PrimInt, WrappingAdd};

use crate::{boolean::Boolean, fields::fp::FpVar, R1CSVar};

use super::UInt;

impl<const N: usize, T: PrimInt + Debug + WrappingAdd, F: PrimeField> UInt<N, T, F> {
    /// Compute `*self = self.wrapping_add(other)`.
    pub fn wrapping_add_in_place(&mut self, other: &Self) {
        let result = Self::wrapping_add_many(&[self.clone(), other.clone()]).unwrap();
        *self = result;
    }

    /// Compute `self.wrapping_add(other)`.
    pub fn wrapping_add(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.wrapping_add_in_place(other);
        result
    }

    /// Perform wrapping addition of `operands`.
    /// Computes `operands[0].wrapping_add(operands[1]).wrapping_add(operands[2])...`.
    ///
    /// The user must ensure that overflow does not occur.
    #[tracing::instrument(target = "r1cs", skip(operands))]
    pub fn wrapping_add_many(operands: &[Self]) -> Result<Self, SynthesisError>
    where
        F: PrimeField,
    {
        // Bounds on `N` to avoid overflows

        assert!(operands.len() >= 1);
        let max_value_size = N as u32 + ark_std::log2(operands.len());
        assert!(max_value_size <= F::MODULUS_BIT_SIZE);

        if operands.len() == 1 {
            return Ok(operands[0].clone());
        }

        // Compute the value of the result.
        let mut value = Some(T::zero());
        for op in operands {
            value = value.and_then(|v| Some(v.wrapping_add(&op.value?)));
        }
        if operands.is_constant() {
            return Ok(UInt::constant(value.unwrap()));
        }

        // Compute the full (non-wrapped) sum of the operands.
        let result = operands
            .iter()
            .map(|op| Boolean::le_bits_to_fp(&op.bits).unwrap())
            .sum::<FpVar<_>>();
        let (mut result_bits, _) = result.to_bits_le_with_top_bits_zero(max_value_size as usize)?;
        // Discard any carry bits, since these will get discarded by wrapping.
        result_bits.truncate(N);
        let bits = TryFrom::try_from(result_bits).unwrap();

        Ok(UInt { bits, value })
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

    fn uint_wrapping_add<T: PrimInt + Debug + WrappingAdd, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
        b: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs().or(b.cs());
        let both_constant = a.is_constant() && b.is_constant();
        let computed = a.wrapping_add(&b);
        let _ = dbg!(a.value());
        let _ = dbg!(b.value());
        dbg!(a.is_constant());
        dbg!(b.is_constant());
        let expected_mode = if both_constant {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let expected = UInt::new_variable(
            cs.clone(),
            || Ok(a.value()?.wrapping_add(&b.value()?)),
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
    fn u8_wrapping_add() {
        run_binary_exhaustive(uint_wrapping_add::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_wrapping_add() {
        run_binary_random::<1000, 16, _, _>(uint_wrapping_add::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_wrapping_add() {
        run_binary_random::<1000, 32, _, _>(uint_wrapping_add::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_wrapping_add() {
        run_binary_random::<1000, 64, _, _>(uint_wrapping_add::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_wrapping_add() {
        run_binary_random::<1000, 128, _, _>(uint_wrapping_add::<u128, 128, Fr>).unwrap()
    }
}
