use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;
use ark_std::vec::Vec;

use crate::{boolean::Boolean, uint8::UInt8};

/// Specifies constraints for conversion to a little-endian bit representation
/// of `self`.
pub trait ToBitsGadget<F: Field> {
    /// Outputs the canonical little-endian bit-wise representation of `self`.
    ///
    /// This is the correct default for 99% of use cases.
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError>;

    /// Outputs a possibly non-unique little-endian bit-wise representation of
    /// `self`.
    ///
    /// If you're not absolutely certain that your usecase can get away with a
    /// non-canonical representation, please use `self.to_bits()` instead.
    fn to_non_unique_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        self.to_bits_le()
    }

    /// Outputs the canonical big-endian bit-wise representation of `self`.
    fn to_bits_be(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let mut res = self.to_bits_le()?;
        res.reverse();
        Ok(res)
    }

    /// Outputs a possibly non-unique big-endian bit-wise representation of
    /// `self`.
    fn to_non_unique_bits_be(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let mut res = self.to_non_unique_bits_le()?;
        res.reverse();
        Ok(res)
    }
}

impl<F: Field> ToBitsGadget<F> for Boolean<F> {
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        Ok(vec![self.clone()])
    }
}

impl<F: Field> ToBitsGadget<F> for [Boolean<F>] {
    /// Outputs `self`.
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        Ok(self.to_vec())
    }
}

impl<F: Field, T> ToBitsGadget<F> for Vec<T>
where
    [T]: ToBitsGadget<F>,
{
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        self.as_slice().to_bits_le().map(|v| v.to_vec())
    }

    fn to_non_unique_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        self.as_slice().to_non_unique_bits_le().map(|v| v.to_vec())
    }
}

/// Specifies constraints for conversion to a little-endian byte representation
/// of `self`.
pub trait ToBytesGadget<F: Field> {
    /// Outputs a canonical, little-endian, byte decomposition of `self`.
    ///
    /// This is the correct default for 99% of use cases.
    fn to_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError>;

    /// Outputs a possibly non-unique byte decomposition of `self`.
    ///
    /// If you're not absolutely certain that your usecase can get away with a
    /// non-canonical representation, please use `self.to_bytes_le(cs)` instead.
    fn to_non_unique_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        self.to_bytes_le()
    }
}

impl<'a, F: Field, T: 'a + ToBytesGadget<F>> ToBytesGadget<F> for &'a T {
    fn to_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        (*self).to_bytes_le()
    }

    fn to_non_unique_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        (*self).to_non_unique_bytes_le()
    }
}

impl<T: ToBytesGadget<F>, F: Field> ToBytesGadget<F> for [T] {
    fn to_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let mut bytes = Vec::new();
        for elem in self {
            let elem = elem.to_bytes_le()?;
            bytes.extend_from_slice(&elem);
            // Make sure that there's enough capacity to avoid reallocations.
            bytes.reserve(elem.len() * (self.len() - 1));
        }
        Ok(bytes)
    }

    fn to_non_unique_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let mut bytes = Vec::new();
        for elem in self {
            let elem = elem.to_non_unique_bytes_le()?;
            bytes.extend_from_slice(&elem);
            // Make sure that there's enough capacity to avoid reallocations.
            bytes.reserve(elem.len() * (self.len() - 1));
        }
        Ok(bytes)
    }
}

impl<T: ToBytesGadget<F>, F: Field> ToBytesGadget<F> for Vec<T> {
    fn to_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        self.as_slice().to_bytes_le()
    }

    fn to_non_unique_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        self.as_slice().to_non_unique_bytes_le()
    }
}

impl<T: ToBytesGadget<F>, F: Field, const N: usize> ToBytesGadget<F> for [T; N] {
    fn to_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        self.as_slice().to_bytes_le()
    }

    fn to_non_unique_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        self.as_slice().to_non_unique_bytes_le()
    }
}

impl<F: Field> ToBytesGadget<F> for () {
    fn to_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        Ok(Vec::new())
    }

    fn to_non_unique_bytes_le(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        Ok(Vec::new())
    }
}

/// Specifies how to convert a variable of type `Self` to variables of
/// type `FpVar<ConstraintF>`
pub trait ToConstraintFieldGadget<ConstraintF: ark_ff::PrimeField> {
    /// Converts `self` to `FpVar<ConstraintF>` variables.
    fn to_constraint_field(
        &self,
    ) -> Result<Vec<crate::fields::fp::FpVar<ConstraintF>>, ark_relations::r1cs::SynthesisError>;
}
