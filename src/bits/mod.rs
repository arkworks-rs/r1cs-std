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
