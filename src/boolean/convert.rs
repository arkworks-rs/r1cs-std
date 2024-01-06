use super::*;
use crate::convert::{ToBytesGadget, ToConstraintFieldGadget};

impl<F: Field> ToBytesGadget<F> for Boolean<F> {
    /// Outputs `1u8` if `self` is true, and `0u8` otherwise.
    #[tracing::instrument(target = "r1cs")]
    fn to_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let value = self.value().map(u8::from).ok();
        let mut bits = [Boolean::FALSE; 8];
        bits[0] = self.clone();
        Ok(vec![UInt8 { bits, value }])
    }
}

impl<F: PrimeField> ToConstraintFieldGadget<F> for Boolean<F> {
    #[tracing::instrument(target = "r1cs")]
    fn to_constraint_field(&self) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let var = From::from(self.clone());
        Ok(vec![var])
    }
}
