use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;
use ark_std::ops::Not;

use super::Boolean;

impl<F: Field> Boolean<F> {
    fn _not(&self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result.not_in_place()?;
        Ok(result)
    }

    pub fn not_in_place(&mut self) -> Result<(), SynthesisError> {
        match *self {
            Boolean::Constant(ref mut c) => *c = !*c,
            Boolean::Var(ref mut v) => *v = v.not()?,
        }
        Ok(())
    }
}

impl<'a, F: Field> Not for &'a Boolean<F> {
    type Output = Boolean<F>;
    /// Negates `self`.
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
    ///
    /// let a = Boolean::new_witness(cs.clone(), || Ok(true))?;
    /// let b = Boolean::new_witness(cs.clone(), || Ok(false))?;
    ///
    /// (!&a).enforce_equal(&b)?;
    /// (!&b).enforce_equal(&a)?;
    ///
    /// (!&a).enforce_equal(&Boolean::FALSE)?;
    /// (!&b).enforce_equal(&Boolean::TRUE)?;
    ///
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self))]
    fn not(self) -> Self::Output {
        self._not().unwrap()
    }
}

impl<'a, F: Field> Not for &'a mut Boolean<F> {
    type Output = Boolean<F>;

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn not(self) -> Self::Output {
        self._not().unwrap()
    }
}

impl<F: Field> Not for Boolean<F> {
    type Output = Boolean<F>;

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn not(self) -> Self::Output {
        self._not().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        alloc::{AllocVar, AllocationMode},
        boolean::test_utils::run_unary_exhaustive,
        prelude::EqGadget,
        R1CSVar,
    };
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn not() {
        run_unary_exhaustive::<Fr>(|a| {
            let cs = a.cs();
            let computed = !&a;
            let expected_mode = if a.is_constant() {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            let expected = Boolean::new_variable(cs.clone(), || Ok(!a.value()?), expected_mode)?;
            assert_eq!(expected.value(), computed.value());
            expected.enforce_equal(&computed)?;
            if !a.is_constant() {
                assert!(cs.is_satisfied().unwrap());
            }
            Ok(())
        })
        .unwrap()
    }
}
