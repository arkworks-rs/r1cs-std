#![cfg_attr(not(feature = "std"), no_std)]
//! This crate implements common "gadgets" that make
//! programming rank-1 constraint systems easier.
#![warn(
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    missing_docs
)]
#![allow(deprecated)]
#![allow(clippy::op_ref)]

#[macro_use]
extern crate ark_std;

#[macro_use]
extern crate ark_ff;

#[macro_use]
extern crate ark_relations;

/// Some utility macros for making downstream impls easier.
#[macro_use]
pub mod macros;

pub(crate) use ark_std::vec::Vec;

#[doc(hidden)]
pub mod gr1cs_var;
pub use gr1cs_var::*;

/// This module contains `Boolean`, an R1CS equivalent of the `bool` type.
pub mod boolean;

/// Finite field arithmetic.
pub mod fields;

/// Implementations of elliptic curve group arithmetic for popular curve models.
pub mod groups;

/// Gadgets for computing pairings in bilinear groups.
pub mod pairing;

/// Utilities for allocating new variables in a constraint system.
pub mod alloc;

/// Utilities for comparing  variables.
pub mod cmp;

/// Utilities for converting variables to other kinds of variables.
pub mod convert;

/// Utilities for checking equality of variables.
pub mod eq;

/// Definitions of polynomial variables over finite fields.
pub mod poly;

/// Contains traits for conditionally selecting a variable from a
/// list of variables.
pub mod select;

#[cfg(test)]
pub(crate) mod test_utils;

/// This module contains `UInt8`, a R1CS equivalent of the `u8` type.
pub mod uint8;
/// This module contains a macro for generating `UIntN` types, which are R1CS
/// equivalents of `N`-bit unsigned integers.
#[macro_use]
pub mod uint;

/// This module contains `UInt16`, a R1CS equivalent of the `u16` type.
pub mod uint16 {
    /// A `UInt16` is a variable that represents a 16-bit unsigned integer in
    /// R1CS.
    pub type UInt16<F> = super::uint::UInt<16, u16, F>;
}
/// This module contains `UInt32`, a R1CS equivalent of the `u32` type.
pub mod uint32 {
    /// A `UInt32` is a variable that represents a 32-bit unsigned integer in
    /// R1CS.
    pub type UInt32<F> = super::uint::UInt<32, u32, F>;
}
/// This module contains `UInt64`, a R1CS equivalent of the `u64` type.
pub mod uint64 {
    /// A `UInt64` is a variable that represents a 64-bit unsigned integer in
    /// R1CS.
    pub type UInt64<F> = super::uint::UInt<64, u64, F>;
}
/// This module contains `UInt128`, a R1CS equivalent of the `u128` type.
pub mod uint128 {
    /// A `UInt128` is a variable that represents a 128-bit unsigned integer in
    /// R1CS.
    pub type UInt128<F> = super::uint::UInt<128, u128, F>;
}

#[allow(missing_docs)]
pub mod prelude {
    pub use crate::{
        alloc::*,
        boolean::Boolean,
        convert::{ToBitsGadget, ToBytesGadget},
        eq::*,
        fields::{FieldOpsBounds, FieldVar},
        groups::{CurveVar, GroupOpsBounds},
        pairing::PairingVar,
        select::*,
        uint128::UInt128,
        uint16::UInt16,
        uint32::UInt32,
        uint64::UInt64,
        uint8::UInt8,
        GR1CSVar,
    };
}

/// A utility trait to convert `Self` to `Result<T, SynthesisErrorA`.>
pub trait Assignment<T> {
    /// Converts `self` to `Result`.
    fn get(self) -> Result<T, ark_relations::gr1cs::SynthesisError>;
}

impl<T> Assignment<T> for Option<T> {
    fn get(self) -> Result<T, ark_relations::gr1cs::SynthesisError> {
        self.ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
    }
}
