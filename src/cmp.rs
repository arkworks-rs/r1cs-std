use ark_ff::{Field, PrimeField};
use ark_relations::r1cs::SynthesisError;

use crate::{boolean::Boolean, eq::EqGadget, R1CSVar};

/// Specifies how to generate constraints for comparing two variables.
pub trait CmpGadget<F: Field>: R1CSVar<F> + EqGadget<F> {
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

/// Mimics the behavior of `std::cmp::PartialOrd` for `()`.
impl<F: Field> CmpGadget<F> for () {
    fn is_gt(&self, _other: &Self) -> Result<Boolean<F>, SynthesisError> {
        Ok(Boolean::FALSE)
    }

    fn is_ge(&self, _other: &Self) -> Result<Boolean<F>, SynthesisError> {
        Ok(Boolean::TRUE)
    }

    fn is_lt(&self, _other: &Self) -> Result<Boolean<F>, SynthesisError> {
        Ok(Boolean::FALSE)
    }

    fn is_le(&self, _other: &Self) -> Result<Boolean<F>, SynthesisError> {
        Ok(Boolean::TRUE)
    }
}

/// Mimics the lexicographic comparison behavior of `std::cmp::PartialOrd` for `[T]`.
impl<T: CmpGadget<F>, F: PrimeField> CmpGadget<F> for [T] {
    fn is_ge(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        let mut result = Boolean::TRUE;
        let mut all_equal_so_far = Boolean::TRUE;
        for (a, b) in self.iter().zip(other) {
            all_equal_so_far &= a.is_eq(b)?;
            result &= a.is_gt(b)? | &all_equal_so_far;
        }
        Ok(result)
    }
}
