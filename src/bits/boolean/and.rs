use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;
use ark_std::{ops::BitAnd, ops::BitAndAssign};

use super::Boolean;

impl<F: Field> Boolean<F> {
    fn _and(&self, other: &Self) -> Result<Self, SynthesisError> {
        use Boolean::*;
        match (self, other) {
            // false AND x is always false
            (&Constant(false), _) | (_, &Constant(false)) => Ok(Constant(false)),
            // true AND x is always x
            (&Constant(true), x) | (x, &Constant(true)) => Ok(x.clone()),
            (Var(ref x), Var(ref y)) => Ok(Var(x.and(y)?)),
        }
    }
}

impl<'a, F: Field> BitAnd<Self> for &'a Boolean<F> {
    type Output = Boolean<F>;
    /// Outputs `self & other`.
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
    /// a.and(&a)?.enforce_equal(&Boolean::TRUE)?;
    ///
    /// a.and(&b)?.enforce_equal(&Boolean::FALSE)?;
    /// b.and(&a)?.enforce_equal(&Boolean::FALSE)?;
    /// b.and(&b)?.enforce_equal(&Boolean::FALSE)?;
    ///
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand(self, other: Self) -> Self::Output {
        self._and(other).unwrap()
    }
}

impl<'a, F: Field> BitAnd<&'a Self> for Boolean<F> {
    type Output = Boolean<F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand(self, other: &Self) -> Self::Output {
        self._and(&other).unwrap()
    }
}

impl<'a, F: Field> BitAnd<Boolean<F>> for &'a Boolean<F> {
    type Output = Boolean<F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand(self, other: Boolean<F>) -> Self::Output {
        self._and(&other).unwrap()
    }
}

impl<F: Field> BitAnd<Self> for Boolean<F> {
    type Output = Self;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand(self, other: Self) -> Self::Output {
        self._and(&other).unwrap()
    }
}

impl<F: Field> BitAndAssign<Self> for Boolean<F> {
    /// Sets `self = self & other`.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand_assign(&mut self, other: Self) {
        let result = self._and(&other).unwrap();
        *self = result;
    }
}

impl<'a, F: Field> BitAndAssign<&'a Self> for Boolean<F> {
    /// Sets `self = self & other`.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand_assign(&mut self, other: &'a Self) {
        let result = self._and(other).unwrap();
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
    fn and() {
        run_binary_exhaustive::<Fr>(|a, b| {
            let cs = a.cs().or(b.cs());
            let both_constant = a.is_constant() && b.is_constant();
            let computed = &a & &b;
            let expected_mode = if both_constant {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            let expected =
                Boolean::new_variable(cs.clone(), || Ok(a.value()? & b.value()?), expected_mode)?;
            assert_eq!(expected.value(), computed.value());
            expected.enforce_equal(&computed)?;
            if !both_constant {
                assert!(cs.is_satisfied().unwrap());
            }
            Ok(())
        })
        .unwrap()
    }
}
