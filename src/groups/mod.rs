use crate::prelude::*;
use ark_ec::ProjectiveCurve;
use ark_ff::Field;
use ark_relations::r1cs::{Namespace, SynthesisError};
use core::ops::{Add, AddAssign, Sub, SubAssign};

use core::{borrow::Borrow, fmt::Debug};

/// This module contains implementations of arithmetic for various curve models.
pub mod curves;

pub use self::curves::short_weierstrass::{bls12, mnt4, mnt6};

/// A hack used to work around the lack of implied bounds.
pub trait GroupOpsBounds<'a, F, T: 'a>:
    Sized
    + Add<&'a T, Output = T>
    + Sub<&'a T, Output = T>
    + Add<T, Output = T>
    + Sub<T, Output = T>
    + Add<F, Output = T>
    + Sub<F, Output = T>
{
}

/// A variable that represents a curve point for
/// the curve `C`.
pub trait CurveVar<C: ProjectiveCurve, ConstraintF: Field>:
    'static
    + Sized
    + Clone
    + Debug
    + R1CSVar<ConstraintF, Value = C>
    + ToBitsGadget<ConstraintF>
    + ToBytesGadget<ConstraintF>
    + EqGadget<ConstraintF>
    + CondSelectGadget<ConstraintF>
    + AllocVar<C, ConstraintF>
    + AllocVar<C::Affine, ConstraintF>
    + for<'a> GroupOpsBounds<'a, C, Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + AddAssign<C>
    + SubAssign<C>
    + AddAssign<Self>
    + SubAssign<Self>
{
    /// Returns the constant `F::zero()`. This is the identity
    /// of the group.
    fn zero() -> Self;

    /// Returns a `Boolean` representing whether `self == Self::zero()`.
    #[tracing::instrument(target = "r1cs")]
    fn is_zero(&self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        self.is_eq(&Self::zero())
    }

    /// Returns a constant with value `v`.
    ///
    /// This *should not* allocate any variables.
    fn constant(other: C) -> Self;

    /// Allocates a variable in the subgroup without checking if it's in the
    /// prime-order subgroup.
    fn new_variable_omit_prime_order_check(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<C, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>;

    /// Enforce that `self` is in the prime-order subgroup.
    fn enforce_prime_order(&self) -> Result<(), SynthesisError>;

    /// Computes `self + self`.
    #[tracing::instrument(target = "r1cs")]
    fn double(&self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result.double_in_place()?;
        Ok(result)
    }

    /// Sets `self = self + self`.
    fn double_in_place(&mut self) -> Result<(), SynthesisError>;

    /// Coputes `-self`.
    fn negate(&self) -> Result<Self, SynthesisError>;

    /// Computes `bits * self`, where `bits` is a little-endian
    /// `Boolean` representation of a scalar.
    #[tracing::instrument(target = "r1cs", skip(bits))]
    fn scalar_mul_le<'a>(
        &self,
        bits: impl Iterator<Item = &'a Boolean<ConstraintF>>,
    ) -> Result<Self, SynthesisError> {
        // TODO: in the constant case we should call precomputed_scalar_mul_le,
        // but rn there's a bug when doing this with TE curves.

        // Computes the standard little-endian double-and-add algorithm
        // (Algorithm 3.26, Guide to Elliptic Curve Cryptography)
        let mut res = Self::zero();
        let mut multiple = self.clone();
        for bit in bits {
            let tmp = res.clone() + &multiple;
            res = bit.select(&tmp, &res)?;
            multiple.double_in_place()?;
        }
        Ok(res)
    }

    /// Computes a `I * self` in place, where `I` is a `Boolean` *little-endian*
    /// representation of the scalar.
    ///
    /// The bases are precomputed power-of-two multiples of a single
    /// base.
    #[tracing::instrument(target = "r1cs", skip(scalar_bits_with_bases))]
    fn precomputed_base_scalar_mul_le<'a, I, B>(
        &mut self,
        scalar_bits_with_bases: I,
    ) -> Result<(), SynthesisError>
    where
        I: Iterator<Item = (B, &'a C)>,
        B: Borrow<Boolean<ConstraintF>>,
        C: 'a,
    {
        // Computes the standard little-endian double-and-add algorithm
        // (Algorithm 3.26, Guide to Elliptic Curve Cryptography)

        // Let `original` be the initial value of `self`.
        let mut result = Self::zero();
        for (bit, base) in scalar_bits_with_bases {
            // Compute `self + 2^i * original`
            let self_plus_base = result.clone() + *base;
            // If `bit == 1`, set self = self + 2^i * original;
            // else, set self = self;
            result = bit.borrow().select(&self_plus_base, &result)?;
        }
        *self = result;
        Ok(())
    }

    /// Computes `Σⱼ(scalarⱼ * baseⱼ)` for all j,
    /// where `scalarⱼ` is a `Boolean` *little-endian*
    /// representation of the j-th scalar.
    #[tracing::instrument(target = "r1cs", skip(bases, scalars))]
    fn precomputed_base_multiscalar_mul_le<'a, T, I, B>(
        bases: &[B],
        scalars: I,
    ) -> Result<Self, SynthesisError>
    where
        T: 'a + ToBitsGadget<ConstraintF> + ?Sized,
        I: Iterator<Item = &'a T>,
        B: Borrow<[C]>,
    {
        let mut result = Self::zero();
        // Compute Σᵢ(bitᵢ * baseᵢ) for all i.
        for (bits, bases) in scalars.zip(bases) {
            let bases = bases.borrow();
            let bits = bits.to_bits_le()?;
            result.precomputed_base_scalar_mul_le(bits.iter().zip(bases))?;
        }
        Ok(result)
    }
}
