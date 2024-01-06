#![cfg_attr(not(feature = "std"), no_std)]
//! This crate implements common "gadgets" that make
//! programming rank-1 constraint systems easier.
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
#![allow(clippy::op_ref)]

#[macro_use]
extern crate ark_std;

#[macro_use]
extern crate ark_ff;

#[macro_use]
extern crate ark_relations;

#[doc(hidden)]
#[macro_use]
extern crate derivative;

/// Some utility macros for making downstream impls easier.
#[macro_use]
pub mod macros;

pub(crate) use ark_std::vec::Vec;

use ark_ff::Field;

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
        R1CSVar,
    };
}

/// This trait describes some core functionality that is common to high-level
/// variables, such as `Boolean`s, `FieldVar`s, `GroupVar`s, etc.
pub trait R1CSVar<F: Field> {
    /// The type of the "native" value that `Self` represents in the constraint
    /// system.
    type Value: core::fmt::Debug + Eq + Clone;

    /// Returns the underlying `ConstraintSystemRef`.
    ///
    /// If `self` is a constant value, then this *must* return
    /// `ark_relations::r1cs::ConstraintSystemRef::None`.
    fn cs(&self) -> ark_relations::r1cs::ConstraintSystemRef<F>;

    /// Returns `true` if `self` is a circuit-generation-time constant.
    fn is_constant(&self) -> bool {
        self.cs().is_none()
    }

    /// Returns the value that is assigned to `self` in the underlying
    /// `ConstraintSystem`.
    fn value(&self) -> Result<Self::Value, ark_relations::r1cs::SynthesisError>;
}

impl<F: Field, T: R1CSVar<F>> R1CSVar<F> for [T] {
    type Value = Vec<T::Value>;

    fn cs(&self) -> ark_relations::r1cs::ConstraintSystemRef<F> {
        let mut result = ark_relations::r1cs::ConstraintSystemRef::None;
        for var in self {
            result = var.cs().or(result);
        }
        result
    }

    fn value(&self) -> Result<Self::Value, ark_relations::r1cs::SynthesisError> {
        let mut result = Vec::new();
        for var in self {
            result.push(var.value()?);
        }
        Ok(result)
    }
}

impl<'a, F: Field, T: 'a + R1CSVar<F>> R1CSVar<F> for &'a T {
    type Value = T::Value;

    fn cs(&self) -> ark_relations::r1cs::ConstraintSystemRef<F> {
        (*self).cs()
    }

    fn value(&self) -> Result<Self::Value, ark_relations::r1cs::SynthesisError> {
        (*self).value()
    }
}

/// A utility trait to convert `Self` to `Result<T, SynthesisErrorA`.>
pub trait Assignment<T> {
    /// Converts `self` to `Result`.
    fn get(self) -> Result<T, ark_relations::r1cs::SynthesisError>;
}

impl<T> Assignment<T> for Option<T> {
    fn get(self) -> Result<T, ark_relations::r1cs::SynthesisError> {
        self.ok_or(ark_relations::r1cs::SynthesisError::AssignmentMissing)
    }
}
