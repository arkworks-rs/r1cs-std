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

/// This module implements gadgets related to bit manipulation, such as
/// `Boolean` and `UInt`s.
pub mod bits;
pub use self::bits::*;

/// This module implements gadgets related to field arithmetic.
pub mod fields;

/// This module implements gadgets related to group arithmetic, and specifically
/// elliptic curve arithmetic.
pub mod groups;

/// This module implements gadgets related to computing pairings in bilinear
/// groups.
pub mod pairing;

/// This module describes a trait for allocating new variables in a constraint
/// system.
pub mod alloc;
/// This module describes a trait for checking equality of variables.
pub mod eq;
/// This module implements functions for manipulating polynomial variables over
/// finite fields.
pub mod poly;
/// This module describes traits for conditionally selecting a variable from a
/// list of variables.
pub mod select;

#[allow(missing_docs)]
pub mod prelude {
    pub use crate::{
        alloc::*,
        bits::{boolean::Boolean, uint32::UInt32, uint8::UInt8, ToBitsGadget, ToBytesGadget},
        eq::*,
        fields::{FieldOpsBounds, FieldVar},
        groups::{CurveVar, GroupOpsBounds},
        pairing::PairingVar,
        select::*,
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

/// Specifies how to convert a variable of type `Self` to variables of
/// type `FpVar<ConstraintF>`
pub trait ToConstraintFieldGadget<ConstraintF: ark_ff::PrimeField> {
    /// Converts `self` to `FpVar<ConstraintF>` variables.
    fn to_constraint_field(
        &self,
    ) -> Result<Vec<crate::fields::fp::FpVar<ConstraintF>>, ark_relations::r1cs::SynthesisError>;
}
