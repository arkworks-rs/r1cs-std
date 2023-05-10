use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;
use ark_std::{ops::BitOr, ops::BitOrAssign};

use super::Boolean;

impl<F: Field> Boolean<F> {
    fn _or(&self, other: &Self) -> Result<Self, SynthesisError> {
        use Boolean::*;
        match (self, other) {
            (&Constant(false), x) | (x, &Constant(false)) => Ok(x.clone()),
            (&Constant(true), _) | (_, &Constant(true)) => Ok(Constant(true)),
            (Var(ref x), Var(ref y)) => Ok(Var(x.or(y)?)),
        }
    }
}

impl<'a, F: Field> BitOr<Self> for &'a Boolean<F> {
    type Output = Boolean<F>;

    /// Outputs `self | other`.
    ///
    /// If at least one of `self` and `other` are constants, then this method
    /// *does not* create any constraints or variables.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    ///
    /// let a = Boolean::new_witness(cs.clone(), || Ok(true))?;
    /// let b = Boolean::new_witness(cs.clone(), || Ok(false))?;
    ///
    /// a.or(&b)?.enforce_equal(&Boolean::TRUE)?;
    /// b.or(&a)?.enforce_equal(&Boolean::TRUE)?;
    ///
    /// a.or(&a)?.enforce_equal(&Boolean::TRUE)?;
    /// b.or(&b)?.enforce_equal(&Boolean::FALSE)?;
    ///
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: Self) -> Self::Output {
        self._or(other).unwrap()
    }
}

impl<'a, F: Field> BitOr<&'a Self> for Boolean<F> {
    type Output = Boolean<F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: &Self) -> Self::Output {
        self._or(&other).unwrap()
    }
}

impl<'a, F: Field> BitOr<Boolean<F>> for &'a Boolean<F> {
    type Output = Boolean<F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: Boolean<F>) -> Self::Output {
        self._or(&other).unwrap()
    }
}

impl<F: Field> BitOr<Self> for Boolean<F> {
    type Output = Self;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: Self) -> Self::Output {
        self._or(&other).unwrap()
    }
}

impl<F: Field> BitOrAssign<Self> for Boolean<F> {
    /// Sets `self = self | other`.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor_assign(&mut self, other: Self) {
        let result = self._or(&other).unwrap();
        *self = result;
    }
}

impl<'a, F: Field> BitOrAssign<&'a Self> for Boolean<F> {
    /// Sets `self = self | other`.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor_assign(&mut self, other: &'a Self) {
        let result = self._or(other).unwrap();
        *self = result;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        alloc::{AllocVar, AllocationMode},
        boolean::test_utils::run_binary_exhaustive,
        prelude::EqGadget,
        R1CSVar,
    };
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn or() {
        run_binary_exhaustive::<Fr>(|a, b| {
            let cs = a.cs().or(b.cs());
            let both_constant = a.is_constant() && b.is_constant();
            let computed = &a | &b;
            let expected_mode = if both_constant {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            let expected = Boolean::new_variable(
                cs.clone(),
                || Ok(a.value().unwrap() | b.value().unwrap()),
                expected_mode,
            )?;
            assert_eq!(expected.value(), computed.value());
            expected.enforce_equal(&expected)?;
            if !both_constant {
                assert!(cs.is_satisfied().unwrap());
            }
            Ok(())
        })
        .unwrap()
    }
}
