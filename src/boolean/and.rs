use ark_ff::{Field, PrimeField};
use ark_relations::r1cs::SynthesisError;
use ark_std::{ops::BitAnd, ops::BitAndAssign};

use crate::{fields::fp::FpVar, prelude::EqGadget};

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

    /// Outputs `!(self & other)`.
    pub fn nand(&self, other: &Self) -> Result<Self, SynthesisError> {
        self._and(other).map(|x| !x)
    }
}

impl<F: PrimeField> Boolean<F> {
    /// Outputs `bits[0] & bits[1] & ... & bits.last().unwrap()`.
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
    /// let c = Boolean::new_witness(cs.clone(), || Ok(true))?;
    ///
    /// Boolean::kary_and(&[a.clone(), b.clone(), c.clone()])?.enforce_equal(&Boolean::FALSE)?;
    /// Boolean::kary_and(&[a.clone(), c.clone()])?.enforce_equal(&Boolean::TRUE)?;
    ///
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs")]
    pub fn kary_and(bits: &[Self]) -> Result<Self, SynthesisError> {
        assert!(!bits.is_empty());
        if bits.len() <= 3 {
            let mut cur: Option<Self> = None;
            for next in bits {
                cur = if let Some(b) = cur {
                    Some(b & next)
                } else {
                    Some(next.clone())
                };
            }

            Ok(cur.expect("should not be 0"))
        } else {
            // b0 & b1 & ... & bN == 1 if and only if sum(b0, b1, ..., bN) == N
            let sum_bits: FpVar<_> = bits.iter().map(|b| FpVar::from(b.clone())).sum();
            let num_bits = FpVar::Constant(F::from(bits.len() as u64));
            sum_bits.is_eq(&num_bits)
        }
    }

    /// Outputs `!(bits[0] & bits[1] & ... & bits.last().unwrap())`.
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
    /// let c = Boolean::new_witness(cs.clone(), || Ok(true))?;
    ///
    /// Boolean::kary_nand(&[a.clone(), b.clone(), c.clone()])?.enforce_equal(&Boolean::TRUE)?;
    /// Boolean::kary_nand(&[a.clone(), c.clone()])?.enforce_equal(&Boolean::FALSE)?;
    /// Boolean::kary_nand(&[b.clone(), c.clone()])?.enforce_equal(&Boolean::TRUE)?;
    ///
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs")]
    pub fn kary_nand(bits: &[Self]) -> Result<Self, SynthesisError> {
        Ok(!Self::kary_and(bits)?)
    }

    /// Enforces that `!(bits[0] & bits[1] & ... ) == Boolean::TRUE`.
    ///
    /// Informally, this means that at least one element in `bits` must be
    /// `false`.
    #[tracing::instrument(target = "r1cs")]
    pub fn enforce_kary_nand(bits: &[Self]) -> Result<(), SynthesisError> {
        Self::kary_and(bits)?.enforce_equal(&Boolean::FALSE)
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
    /// (&a & &a).enforce_equal(&Boolean::TRUE)?;
    ///
    /// (&a & &b).enforce_equal(&Boolean::FALSE)?;
    /// (&b & &a).enforce_equal(&Boolean::FALSE)?;
    /// (&b & &b).enforce_equal(&Boolean::FALSE)?;
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
    use ark_relations::r1cs::ConstraintSystem;
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

    #[test]
    fn nand() {
        run_binary_exhaustive::<Fr>(|a, b| {
            let cs = a.cs().or(b.cs());
            let both_constant = a.is_constant() && b.is_constant();
            let computed = a.nand(&b)?;
            let expected_mode = if both_constant {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            let expected = Boolean::new_variable(
                cs.clone(),
                || Ok(!(a.value()? & b.value()?)),
                expected_mode,
            )?;
            assert_eq!(expected.value(), computed.value());
            expected.enforce_equal(&computed)?;
            if !both_constant {
                assert!(cs.is_satisfied().unwrap());
            }
            Ok(())
        })
        .unwrap()
    }

    #[test]
    fn enforce_nand() -> Result<(), SynthesisError> {
        {
            let cs = ConstraintSystem::<Fr>::new_ref();

            assert!(
                Boolean::enforce_kary_nand(&[Boolean::new_constant(cs.clone(), false)?]).is_ok()
            );
            assert!(
                Boolean::enforce_kary_nand(&[Boolean::new_constant(cs.clone(), true)?]).is_err()
            );
        }

        for i in 1..5 {
            // with every possible assignment for them
            for mut b in 0..(1 << i) {
                // with every possible negation
                for mut n in 0..(1 << i) {
                    let cs = ConstraintSystem::<Fr>::new_ref();

                    let mut expected = true;

                    let mut bits = vec![];
                    for _ in 0..i {
                        expected &= b & 1 == 1;

                        let bit = if n & 1 == 1 {
                            Boolean::new_witness(cs.clone(), || Ok(b & 1 == 1))?
                        } else {
                            !Boolean::new_witness(cs.clone(), || Ok(b & 1 == 0))?
                        };
                        bits.push(bit);

                        b >>= 1;
                        n >>= 1;
                    }

                    let expected = !expected;

                    Boolean::enforce_kary_nand(&bits)?;

                    if expected {
                        assert!(cs.is_satisfied().unwrap());
                    } else {
                        assert!(!cs.is_satisfied().unwrap());
                    }
                }
            }
        }
        Ok(())
    }

    #[test]
    fn kary_and() -> Result<(), SynthesisError> {
        // test different numbers of operands
        for i in 1..15 {
            // with every possible assignment for them
            for mut b in 0..(1 << i) {
                let cs = ConstraintSystem::<Fr>::new_ref();

                let mut expected = true;

                let mut bits = vec![];
                for _ in 0..i {
                    expected &= b & 1 == 1;
                    bits.push(Boolean::new_witness(cs.clone(), || Ok(b & 1 == 1))?);
                    b >>= 1;
                }

                let r = Boolean::kary_and(&bits)?;

                assert!(cs.is_satisfied().unwrap());

                if let Boolean::Var(ref r) = r {
                    assert_eq!(r.value()?, expected);
                }
            }
        }
        Ok(())
    }
}
