use ark_ff::{prelude::*, BitIteratorBE};
use ark_relations::r1cs::SynthesisError;
use core::{
    fmt::Debug,
    ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign},
};

use crate::prelude::*;

/// This module contains a generic implementation of cubic extension field
/// variables. That is, it implements the R1CS equivalent of
/// `ark_ff::CubicExtField`.
pub mod cubic_extension;
/// This module contains a generic implementation of quadratic extension field
/// variables. That is, it implements the R1CS equivalent of
/// `ark_ff::QuadExtField`.
pub mod quadratic_extension;

/// This module contains a generic implementation of prime field variables.
/// That is, it implements the R1CS equivalent of `ark_ff::Fp*`.
pub mod fp;

/// This module contains a generic implementation of the degree-12 tower
/// extension field. That is, it implements the R1CS equivalent of
/// `ark_ff::Fp12`
pub mod fp12;
/// This module contains a generic implementation of the degree-2 tower
/// extension field. That is, it implements the R1CS equivalent of
/// `ark_ff::Fp2`
pub mod fp2;
/// This module contains a generic implementation of the degree-3 tower
/// extension field. That is, it implements the R1CS equivalent of
/// `ark_ff::Fp3`
pub mod fp3;
/// This module contains a generic implementation of the degree-4 tower
/// extension field. That is, it implements the R1CS equivalent of
/// `ark_ff::Fp4`
pub mod fp4;
/// This module contains a generic implementation of the degree-6 tower
/// extension field. That is, it implements the R1CS equivalent of
/// `ark_ff::fp6_2over3::Fp6`
pub mod fp6_2over3;
/// This module contains a generic implementation of the degree-6 tower
/// extension field. That is, it implements the R1CS equivalent of
/// `ark_ff::fp6_3over2::Fp6`
pub mod fp6_3over2;

/// This trait is a hack used to work around the lack of implied bounds.
pub trait FieldOpsBounds<'a, F, T: 'a>:
    Sized
    + Add<&'a T, Output = T>
    + Sub<&'a T, Output = T>
    + Mul<&'a T, Output = T>
    + Add<T, Output = T>
    + Sub<T, Output = T>
    + Mul<T, Output = T>
    + Add<F, Output = T>
    + Sub<F, Output = T>
    + Mul<F, Output = T>
{
}

/// A variable representing a field. Corresponds to the native type `F`.
pub trait FieldVar<F: Field, ConstraintF: Field>:
    'static
    + Clone
    + From<Boolean<ConstraintF>>
    + R1CSVar<ConstraintF, Value = F>
    + EqGadget<ConstraintF>
    + ToBitsGadget<ConstraintF>
    + AllocVar<F, ConstraintF>
    + ToBytesGadget<ConstraintF>
    + CondSelectGadget<ConstraintF>
    + for<'a> FieldOpsBounds<'a, F, Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + for<'a> MulAssign<&'a Self>
    + AddAssign<Self>
    + SubAssign<Self>
    + MulAssign<Self>
    + AddAssign<F>
    + SubAssign<F>
    + MulAssign<F>
    + Debug
{
    /// Returns the constant `F::zero()`.
    fn zero() -> Self;

    /// Returns a `Boolean` representing whether `self == Self::zero()`.
    fn is_zero(&self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        self.is_eq(&Self::zero())
    }

    /// Returns the constant `F::one()`.
    fn one() -> Self;

    /// Returns a `Boolean` representing whether `self == Self::one()`.
    fn is_one(&self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        self.is_eq(&Self::one())
    }

    /// Returns a constant with value `v`.
    ///
    /// This *should not* allocate any variables.
    fn constant(v: F) -> Self;

    /// Computes `self + self`.
    fn double(&self) -> Result<Self, SynthesisError> {
        Ok(self.clone() + self)
    }

    /// Sets `self = self + self`.
    fn double_in_place(&mut self) -> Result<&mut Self, SynthesisError> {
        *self += self.double()?;
        Ok(self)
    }

    /// Coputes `-self`.
    fn negate(&self) -> Result<Self, SynthesisError>;

    /// Sets `self = -self`.
    #[inline]
    fn negate_in_place(&mut self) -> Result<&mut Self, SynthesisError> {
        *self = self.negate()?;
        Ok(self)
    }

    /// Computes `self * self`.
    ///
    /// A default implementation is provided which just invokes the underlying
    /// multiplication routine. However, this method should be specialized
    /// for extension fields, where faster algorithms exist for squaring.
    fn square(&self) -> Result<Self, SynthesisError> {
        Ok(self.clone() * self)
    }

    /// Sets `self = self.square()`.
    fn square_in_place(&mut self) -> Result<&mut Self, SynthesisError> {
        *self = self.square()?;
        Ok(self)
    }

    /// Enforces that `self * other == result`.
    fn mul_equals(&self, other: &Self, result: &Self) -> Result<(), SynthesisError> {
        let actual_result = self.clone() * other;
        result.enforce_equal(&actual_result)
    }

    /// Enforces that `self * self == result`.
    fn square_equals(&self, result: &Self) -> Result<(), SynthesisError> {
        let actual_result = self.square()?;
        result.enforce_equal(&actual_result)
    }

    /// Computes `result` such that `self * result == Self::one()`.
    fn inverse(&self) -> Result<Self, SynthesisError>;

    /// Returns `(self / d)`. but requires fewer constraints than `self * d.inverse()`.
    /// It is up to the caller to ensure that `d` is non-zero,
    /// since in that case the result is unconstrained.
    fn mul_by_inverse(&self, d: &Self) -> Result<Self, SynthesisError> {
        let d_inv = if self.is_constant() || d.is_constant() {
            d.inverse()?
        } else {
            Self::new_witness(self.cs(), || Ok(d.value()?.inverse().unwrap_or(F::zero())))?
        };
        Ok(d_inv * self)
    }

    /// Computes the frobenius map over `self`.
    fn frobenius_map(&self, power: usize) -> Result<Self, SynthesisError>;

    /// Sets `self = self.frobenius_map()`.
    fn frobenius_map_in_place(&mut self, power: usize) -> Result<&mut Self, SynthesisError> {
        *self = self.frobenius_map(power)?;
        Ok(self)
    }

    /// Comptues `self^bits`, where `bits` is a *little-endian* bit-wise
    /// decomposition of the exponent.
    fn pow_le(&self, bits: &[Boolean<ConstraintF>]) -> Result<Self, SynthesisError> {
        let mut res = Self::one();
        let mut power = self.clone();
        for bit in bits {
            let tmp = res.clone() * &power;
            res = bit.select(&tmp, &res)?;
            power.square_in_place()?;
        }
        Ok(res)
    }

    /// Computes `self^S`, where S is interpreted as an little-endian
    /// u64-decomposition of an integer.
    fn pow_by_constant<S: AsRef<[u64]>>(&self, exp: S) -> Result<Self, SynthesisError> {
        let mut res = Self::one();
        for i in BitIteratorBE::without_leading_zeros(exp) {
            res.square_in_place()?;
            if i {
                res *= self;
            }
        }
        Ok(res)
    }
}
