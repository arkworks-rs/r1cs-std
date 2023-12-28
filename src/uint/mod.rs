use ark_ff::{Field, PrimeField};
use core::{borrow::Borrow, convert::TryFrom, fmt::Debug};

use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};

use crate::{boolean::Boolean, prelude::*, Assignment, Vec};

mod add;
mod and;
mod cmp;
mod convert;
mod eq;
mod not;
mod or;
mod rotate;
mod select;
mod shl;
mod shr;
mod xor;

#[doc(hidden)]
pub mod prim_uint;
pub use prim_uint::*;

#[cfg(test)]
pub(crate) mod test_utils;

/// This struct represent an unsigned `N` bit integer as a sequence of `N` [`Boolean`]s.
#[derive(Clone, Debug)]
pub struct UInt<const N: usize, T: PrimUInt, F: Field> {
    #[doc(hidden)]
    pub bits: [Boolean<F>; N],
    #[doc(hidden)]
    pub value: Option<T>,
}

impl<const N: usize, T: PrimUInt, F: Field> R1CSVar<F> for UInt<N, T, F> {
    type Value = T;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.bits.as_ref().cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let mut value = T::zero();
        for (i, bit) in self.bits.iter().enumerate() {
            value = value + (T::from(bit.value()? as u8).unwrap() << i);
        }
        debug_assert_eq!(self.value, Some(value));
        Ok(value)
    }
}

impl<const N: usize, T: PrimUInt, F: Field> UInt<N, T, F> {
    pub const MAX: Self = Self {
        bits: [Boolean::TRUE; N],
        value: Some(T::MAX),
    };

    /// Construct a constant [`UInt`] from the native unsigned integer type.
    ///
    /// This *does not* create new variables or constraints.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let var = UInt8::new_witness(cs.clone(), || Ok(2))?;
    ///
    /// let constant = UInt8::constant(2);
    /// var.enforce_equal(&constant)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    pub fn constant(value: T) -> Self {
        let mut bits = [Boolean::FALSE; N];
        let mut bit_values = value;

        for i in 0..N {
            bits[i] = Boolean::constant((bit_values & T::one()) == T::one());
            bit_values = bit_values >> 1u8;
        }

        Self {
            bits,
            value: Some(value),
        }
    }

    /// Construct a constant vector of [`UInt`] from a vector of the native type
    ///
    /// This *does not* create any new variables or constraints.
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let var = vec![UInt8::new_witness(cs.clone(), || Ok(2))?];
    ///
    /// let constant = UInt8::constant_vec(&[2]);
    /// var.enforce_equal(&constant)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    pub fn constant_vec(values: &[T]) -> Vec<Self> {
        values.iter().map(|v| Self::constant(*v)).collect()
    }

    /// Allocates a slice of `uN`'s as private witnesses.
    pub fn new_witness_vec(
        cs: impl Into<Namespace<F>>,
        values: &[impl Into<Option<T>> + Copy],
    ) -> Result<Vec<Self>, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let mut output_vec = Vec::with_capacity(values.len());
        for value in values {
            let byte: Option<T> = Into::into(*value);
            output_vec.push(Self::new_witness(cs.clone(), || byte.get())?);
        }
        Ok(output_vec)
    }
}

impl<const N: usize, T: PrimUInt, ConstraintF: Field> AllocVar<T, ConstraintF>
    for UInt<N, T, ConstraintF>
{
    fn new_variable<S: Borrow<T>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<S, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let value = f().map(|f| *f.borrow()).ok();

        let mut values = [None; N];
        if let Some(val) = value {
            values
                .iter_mut()
                .enumerate()
                .for_each(|(i, v)| *v = Some(((val >> i) & T::one()) == T::one()));
        }

        let mut bits = [Boolean::FALSE; N];
        for (b, v) in bits.iter_mut().zip(&values) {
            *b = Boolean::new_variable(cs.clone(), || v.get(), mode)?;
        }
        Ok(Self { bits, value })
    }
}
