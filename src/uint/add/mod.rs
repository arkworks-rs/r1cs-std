use crate::fields::fp::FpVar;

use super::*;

mod saturating;
mod wrapping;

impl<const N: usize, T: PrimUInt, F: PrimeField> UInt<N, T, F> {
    /// Adds up `operands`, returning the bit decomposition of the result, along with
    /// the value of the result. If all the operands are constant, then the bit decomposition
    /// is empty, and the value is the constant value of the result.
    ///
    /// # Panics
    ///
    /// This method panics if the result of addition could possibly exceed the field size.
    #[tracing::instrument(target = "r1cs", skip(operands, adder))]
    fn add_many_helper(
        operands: &[Self],
        adder: impl Fn(T, T) -> T,
    ) -> Result<(Vec<Boolean<F>>, Option<T>), SynthesisError> {
        // Bounds on `N` to avoid overflows

        assert!(operands.len() >= 1);
        let max_value_size = N as u32 + ark_std::log2(operands.len());
        assert!(max_value_size <= F::MODULUS_BIT_SIZE);

        if operands.len() == 1 {
            return Ok((operands[0].bits.to_vec(), operands[0].value));
        }

        // Compute the value of the result.
        let mut value = Some(T::zero());
        for op in operands {
            value = value.and_then(|v| Some(adder(v, op.value?)));
        }
        if operands.is_constant() {
            // If all operands are constant, then the result is also constant.
            // In this case, we can return early.
            return Ok((Vec::new(), value));
        }

        // Compute the full (non-wrapped) sum of the operands.
        let result = operands
            .iter()
            .map(|op| Boolean::le_bits_to_fp(&op.bits).unwrap())
            .sum::<FpVar<_>>();
        let (result, _) = result.to_bits_le_with_top_bits_zero(max_value_size as usize)?;
        Ok((result, value))
    }
}
