use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;

use crate::{boolean::Boolean, R1CSVar};

/// Specifies how to generate constraints for comparing two variables.
pub trait CmpGadget<F: Field>: R1CSVar<F> {
    fn is_gt(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        other.is_lt(self)
    }

    fn is_ge(&self, other: &Self) -> Result<Boolean<F>, SynthesisError>;

    fn is_lt(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        Ok(!self.is_ge(other)?)
    }

    fn is_le(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        other.is_ge(self)
    }
}
