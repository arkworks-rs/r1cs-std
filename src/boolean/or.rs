use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use ark_std::{ops::BitOr, ops::BitOrAssign};

use crate::{
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
};

use super::Boolean;

impl<F: PrimeField> Boolean<F> {
    fn _or(&self, other: &Self) -> Result<Self, SynthesisError> {
        use Boolean::*;
        match (self, other) {
            (&Constant(false), x) | (x, &Constant(false)) => Ok(x.clone()),
            (&Constant(true), _) | (_, &Constant(true)) => Ok(Constant(true)),
            (Var(ref x), Var(ref y)) => Ok(Var(x.or(y)?)),
        }
    }

    /// Outputs `bits[0] | bits[1] | ... | bits.last().unwrap()`.
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
    /// let c = Boolean::new_witness(cs.clone(), || Ok(false))?;
    ///
    /// Boolean::kary_or(&[a.clone(), b.clone(), c.clone()])?.enforce_equal(&Boolean::TRUE)?;
    /// Boolean::kary_or(&[a.clone(), c.clone()])?.enforce_equal(&Boolean::TRUE)?;
    /// Boolean::kary_or(&[b.clone(), c.clone()])?.enforce_equal(&Boolean::FALSE)?;
    ///
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs")]
    pub fn kary_or(bits: &[Self]) -> Result<Self, SynthesisError> {
        assert!(!bits.is_empty());
        if bits.len() <= 3 {
            let mut cur: Option<Self> = None;
            for next in bits {
                cur = if let Some(b) = cur {
                    Some(b | next)
                } else {
                    Some(next.clone())
                };
            }

            Ok(cur.expect("should not be 0"))
        } else {
            // b0 | b1 | ... | bN == 1 if and only if not all of b0, b1, ..., bN are 0.
            // We can enforce this by requiring that the sum of b0, b1, ..., bN is not 0.
            let sum_bits: FpVar<_> = bits.iter().map(|b| FpVar::from(b.clone())).sum();
            sum_bits.is_neq(&FpVar::zero())
        }
    }
}

impl<'a, F: PrimeField> BitOr<Self> for &'a Boolean<F> {
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
    /// (&a | &b).enforce_equal(&Boolean::TRUE)?;
    /// (&b | &a).enforce_equal(&Boolean::TRUE)?;
    ///
    /// (&a | &a).enforce_equal(&Boolean::TRUE)?;
    /// (&b | &b).enforce_equal(&Boolean::FALSE)?;
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

impl<'a, F: PrimeField> BitOr<&'a Self> for Boolean<F> {
    type Output = Boolean<F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: &Self) -> Self::Output {
        self._or(&other).unwrap()
    }
}

impl<'a, F: PrimeField> BitOr<Boolean<F>> for &'a Boolean<F> {
    type Output = Boolean<F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: Boolean<F>) -> Self::Output {
        self._or(&other).unwrap()
    }
}

impl<F: PrimeField> BitOr<Self> for Boolean<F> {
    type Output = Self;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: Self) -> Self::Output {
        self._or(&other).unwrap()
    }
}

impl<F: PrimeField> BitOrAssign<Self> for Boolean<F> {
    /// Sets `self = self | other`.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor_assign(&mut self, other: Self) {
        let result = self._or(&other).unwrap();
        *self = result;
    }
}

impl<'a, F: PrimeField> BitOrAssign<&'a Self> for Boolean<F> {
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
            let expected =
                Boolean::new_variable(cs.clone(), || Ok(a.value()? | b.value()?), expected_mode)?;
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
