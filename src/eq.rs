use crate::{prelude::*, Vec};
use ark_ff::{Field, PrimeField};
use ark_relations::r1cs::SynthesisError;

/// Specifies how to generate constraints that check for equality for two
/// variables of type `Self`.
pub trait EqGadget<F: Field> {
    /// Output a `Boolean` value representing whether `self.value() ==
    /// other.value()`.
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError>;

    /// Output a `Boolean` value representing whether `self.value() !=
    /// other.value()`.
    ///
    /// By default, this is defined as `self.is_eq(other)?.not()`.
    fn is_neq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        Ok(!self.is_eq(other)?)
    }

    /// If `should_enforce == true`, enforce that `self` and `other` are equal;
    /// else, enforce a vacuously true statement.
    ///
    /// A safe default implementation is provided that generates the following
    /// constraints: `self.is_eq(other)?.conditional_enforce_equal(&Boolean:
    /// :TRUE, should_enforce)`.
    ///
    /// More efficient specialized implementation may be possible; implementors
    /// are encouraged to carefully analyze the efficiency and safety of these.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        self.is_eq(&other)?
            .conditional_enforce_equal(&Boolean::TRUE, should_enforce)
    }

    /// Enforce that `self` and `other` are equal.
    ///
    /// A safe default implementation is provided that generates the following
    /// constraints: `self.conditional_enforce_equal(other,
    /// &Boolean::TRUE)`.
    ///
    /// More efficient specialized implementation may be possible; implementors
    /// are encouraged to carefully analyze the efficiency and safety of these.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn enforce_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.conditional_enforce_equal(other, &Boolean::TRUE)
    }

    /// If `should_enforce == true`, enforce that `self` and `other` are *not*
    /// equal; else, enforce a vacuously true statement.
    ///
    /// A safe default implementation is provided that generates the following
    /// constraints: `self.is_neq(other)?.conditional_enforce_equal(&
    /// Boolean::TRUE, should_enforce)`.
    ///
    /// More efficient specialized implementation may be possible; implementors
    /// are encouraged to carefully analyze the efficiency and safety of these.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        self.is_neq(&other)?
            .conditional_enforce_equal(&Boolean::TRUE, should_enforce)
    }

    /// Enforce that `self` and `other` are *not* equal.
    ///
    /// A safe default implementation is provided that generates the following
    /// constraints: `self.conditional_enforce_not_equal(other,
    /// &Boolean::TRUE)`.
    ///
    /// More efficient specialized implementation may be possible; implementors
    /// are encouraged to carefully analyze the efficiency and safety of these.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn enforce_not_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.conditional_enforce_not_equal(other, &Boolean::TRUE)
    }
}

impl<T: EqGadget<F> + R1CSVar<F>, F: PrimeField> EqGadget<F> for [T] {
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        assert_eq!(self.len(), other.len());
        if self.is_empty() & other.is_empty() {
            Ok(Boolean::TRUE)
        } else {
            let mut results = Vec::with_capacity(self.len());
            for (a, b) in self.iter().zip(other) {
                results.push(a.is_eq(b)?);
            }
            Boolean::kary_and(&results)
        }
    }

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        assert_eq!(self.len(), other.len());
        for (a, b) in self.iter().zip(other) {
            a.conditional_enforce_equal(b, condition)?;
        }
        Ok(())
    }

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        assert_eq!(self.len(), other.len());
        let some_are_different = self.is_neq(other)?;
        if [&some_are_different, should_enforce].is_constant() {
            assert!(some_are_different.value()?);
            Ok(())
        } else {
            let cs = [&some_are_different, should_enforce].cs();
            cs.enforce_constraint(
                some_are_different.lc(),
                should_enforce.lc(),
                should_enforce.lc(),
            )
        }
    }
}

/// This blanket implementation just forwards to the impl on [`[T]`].
impl<T: EqGadget<F> + R1CSVar<F>, F: PrimeField> EqGadget<F> for Vec<T> {
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        self.as_slice().is_eq(other.as_slice())
    }

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        self.as_slice()
            .conditional_enforce_equal(other.as_slice(), condition)
    }

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        self.as_slice()
            .conditional_enforce_not_equal(other.as_slice(), should_enforce)
    }
}

/// Dummy impl for `()`.
impl<F: Field> EqGadget<F> for () {
    /// Output a `Boolean` value representing whether `self.value() ==
    /// other.value()`.
    #[inline]
    fn is_eq(&self, _other: &Self) -> Result<Boolean<F>, SynthesisError> {
        Ok(Boolean::TRUE)
    }

    /// If `should_enforce == true`, enforce that `self` and `other` are equal;
    /// else, enforce a vacuously true statement.
    ///
    /// This is a no-op as `self.is_eq(other)?` is always `true`.
    #[tracing::instrument(target = "r1cs", skip(self, _other))]
    fn conditional_enforce_equal(
        &self,
        _other: &Self,
        _should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        Ok(())
    }

    /// Enforce that `self` and `other` are equal.
    ///
    /// This does not generate any constraints as `self.is_eq(other)?` is always
    /// `true`.
    #[tracing::instrument(target = "r1cs", skip(self, _other))]
    fn enforce_equal(&self, _other: &Self) -> Result<(), SynthesisError> {
        Ok(())
    }
}

/// This blanket implementation just forwards to the impl on [`[T]`].
impl<T: EqGadget<F> + R1CSVar<F>, F: PrimeField, const N: usize> EqGadget<F> for [T; N] {
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        self.as_slice().is_eq(other.as_slice())
    }

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        self.as_slice()
            .conditional_enforce_equal(other.as_slice(), condition)
    }

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        self.as_slice()
            .conditional_enforce_not_equal(other.as_slice(), should_enforce)
    }
}
