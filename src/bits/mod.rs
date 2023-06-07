use crate::{
    bits::{boolean::Boolean, uint8::UInt8},
    Vec,
};
use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;

/// This module contains `Boolean`, a R1CS equivalent of the `bool` type.
pub mod boolean;
/// This module contains `UInt8`, a R1CS equivalent of the `u8` type.
pub mod uint8;
/// This module contains a macro for generating `UIntN` types, which are R1CS
/// equivalents of `N`-bit unsigned integers.
#[macro_use]
pub mod uint;

pub mod uint16 {
    pub type UInt16<F> = super::uint::UInt<16, u16, F>;
}
pub mod uint32 {
    pub type UInt32<F> = super::uint::UInt<32, u32, F>;
}
pub mod uint64 {
    pub type UInt64<F> = super::uint::UInt<64, u64, F>;
}
pub mod uint128 {
    pub type UInt128<F> = super::uint::UInt<128, u128, F>;
}

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
    fn to_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError>;

    /// Outputs a possibly non-unique byte decomposition of `self`.
    ///
    /// If you're not absolutely certain that your usecase can get away with a
    /// non-canonical representation, please use `self.to_bytes(cs)` instead.
    fn to_non_unique_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        self.to_bytes()
    }
}

impl<'a, F: Field, T: 'a + ToBytesGadget<F>> ToBytesGadget<F> for &'a T {
    fn to_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        (*self).to_bytes()
    }
}
