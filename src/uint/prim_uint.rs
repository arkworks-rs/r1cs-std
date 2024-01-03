use core::ops::{Shl, ShlAssign, Shr, ShrAssign};
use core::usize;

#[doc(hidden)]
// Adapted from <https://github.com/rust-num/num-traits/pull/224>
pub trait PrimUInt:
    core::fmt::Debug
    + num_traits::PrimInt
    + num_traits::WrappingAdd
    + num_traits::SaturatingAdd
    + Shl<usize, Output = Self>
    + Shl<u8, Output = Self>
    + Shl<u16, Output = Self>
    + Shl<u32, Output = Self>
    + Shl<u64, Output = Self>
    + Shl<u128, Output = Self>
    + Shr<usize, Output = Self>
    + Shr<u8, Output = Self>
    + Shr<u16, Output = Self>
    + Shr<u32, Output = Self>
    + Shr<u64, Output = Self>
    + Shr<u128, Output = Self>
    + ShlAssign<usize>
    + ShlAssign<u8>
    + ShlAssign<u16>
    + ShlAssign<u32>
    + ShlAssign<u64>
    + ShlAssign<u128>
    + ShrAssign<usize>
    + ShrAssign<u8>
    + ShrAssign<u16>
    + ShrAssign<u32>
    + ShrAssign<u64>
    + ShrAssign<u128>
    + Into<u128>
    + _private::Sealed
    + ark_std::UniformRand
{
    type Bytes: NumBytes;
    const MAX: Self;
    #[doc(hidden)]
    const MAX_VALUE_BIT_DECOMP: &'static [bool];

    /// Return the memory representation of this number as a byte array in little-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use ark_r1cs_std::uint::PrimUInt;
    ///
    /// let bytes = PrimUInt::to_le_bytes(&0x12345678u32);
    /// assert_eq!(bytes, [0x78, 0x56, 0x34, 0x12]);
    /// ```
    fn to_le_bytes(&self) -> Self::Bytes;

    /// Return the memory representation of this number as a byte array in big-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use ark_r1cs_std::uint::PrimUInt;
    ///
    /// let bytes = PrimUInt::to_be_bytes(&0x12345678u32);
    /// assert_eq!(bytes, [0x12, 0x34, 0x56, 0x78]);
    /// ```
    fn to_be_bytes(&self) -> Self::Bytes;
}

impl PrimUInt for u8 {
    const MAX: Self = u8::MAX;
    const MAX_VALUE_BIT_DECOMP: &'static [bool] = &[true; 8];
    type Bytes = [u8; 1];

    #[inline]
    fn to_le_bytes(&self) -> Self::Bytes {
        u8::to_le_bytes(*self)
    }

    #[inline]
    fn to_be_bytes(&self) -> Self::Bytes {
        u8::to_be_bytes(*self)
    }
}

impl PrimUInt for u16 {
    const MAX: Self = u16::MAX;
    const MAX_VALUE_BIT_DECOMP: &'static [bool] = &[true; 16];
    type Bytes = [u8; 2];

    #[inline]
    fn to_le_bytes(&self) -> Self::Bytes {
        u16::to_le_bytes(*self)
    }

    #[inline]
    fn to_be_bytes(&self) -> Self::Bytes {
        u16::to_be_bytes(*self)
    }
}

impl PrimUInt for u32 {
    const MAX: Self = u32::MAX;
    const MAX_VALUE_BIT_DECOMP: &'static [bool] = &[true; 32];
    type Bytes = [u8; 4];

    #[inline]
    fn to_le_bytes(&self) -> Self::Bytes {
        u32::to_le_bytes(*self)
    }

    #[inline]
    fn to_be_bytes(&self) -> Self::Bytes {
        u32::to_be_bytes(*self)
    }
}

impl PrimUInt for u64 {
    const MAX: Self = u64::MAX;
    const MAX_VALUE_BIT_DECOMP: &'static [bool] = &[true; 64];
    type Bytes = [u8; 8];

    #[inline]
    fn to_le_bytes(&self) -> Self::Bytes {
        u64::to_le_bytes(*self)
    }

    #[inline]
    fn to_be_bytes(&self) -> Self::Bytes {
        u64::to_be_bytes(*self)
    }
}

impl PrimUInt for u128 {
    const MAX: Self = u128::MAX;
    const MAX_VALUE_BIT_DECOMP: &'static [bool] = &[true; 128];
    type Bytes = [u8; 16];

    #[inline]
    fn to_le_bytes(&self) -> Self::Bytes {
        u128::to_le_bytes(*self)
    }

    #[inline]
    fn to_be_bytes(&self) -> Self::Bytes {
        u128::to_be_bytes(*self)
    }
}

#[doc(hidden)]
pub trait NumBytes:
    core::fmt::Debug
    + AsRef<[u8]>
    + AsMut<[u8]>
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + core::hash::Hash
    + core::borrow::Borrow<[u8]>
    + core::borrow::BorrowMut<[u8]>
{
}

#[doc(hidden)]
impl<const N: usize> NumBytes for [u8; N] {}

mod _private {
    pub trait Sealed {}

    impl Sealed for u8 {}
    impl Sealed for u16 {}
    impl Sealed for u32 {}
    impl Sealed for u64 {}
    impl Sealed for u128 {}
}
