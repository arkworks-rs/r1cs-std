use super::*;

impl<F: PrimeField> Boolean<F> {
    /// Conditionally selects one of `first` and `second` based on the value of
    /// `self`:
    ///
    /// If `self.is_eq(&Boolean::TRUE)`, this outputs `first`; else, it outputs
    /// `second`.
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
    /// let cond = Boolean::new_witness(cs.clone(), || Ok(true))?;
    ///
    /// cond.select(&a, &b)?.enforce_equal(&Boolean::TRUE)?;
    /// cond.select(&b, &a)?.enforce_equal(&Boolean::FALSE)?;
    ///
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(first, second))]
    pub fn select<T: CondSelectGadget<F>>(
        &self,
        first: &T,
        second: &T,
    ) -> Result<T, SynthesisError> {
        T::conditionally_select(&self, first, second)
    }
}
impl<F: PrimeField> CondSelectGadget<F> for Boolean<F> {
    #[tracing::instrument(target = "r1cs")]
    fn conditionally_select(
        cond: &Boolean<F>,
        true_val: &Self,
        false_val: &Self,
    ) -> Result<Self, SynthesisError> {
        use Boolean::*;
        match cond {
            Constant(true) => Ok(true_val.clone()),
            Constant(false) => Ok(false_val.clone()),
            cond @ Var(_) => match (true_val, false_val) {
                (x, &Constant(false)) => Ok(cond & x),
                (&Constant(false), x) => Ok((!cond) & x),
                (&Constant(true), x) => Ok(cond | x),
                (x, &Constant(true)) => Ok((!cond) | x),
                (a, b) => {
                    let cs = cond.cs();
                    let result: Boolean<F> =
                        AllocatedBool::new_witness_without_booleanity_check(cs.clone(), || {
                            let cond = cond.value()?;
                            Ok(if cond { a.value()? } else { b.value()? })
                        })?
                        .into();
                    // a = self; b = other; c = cond;
                    //
                    // r = c * a + (1  - c) * b
                    // r = b + c * (a - b)
                    // c * (a - b) = r - b
                    //
                    // If a, b, cond are all boolean, so is r.
                    //
                    // self | other | cond | result
                    // -----|-------|----------------
                    //   0  |   0   |   1  |    0
                    //   0  |   1   |   1  |    0
                    //   1  |   0   |   1  |    1
                    //   1  |   1   |   1  |    1
                    //   0  |   0   |   0  |    0
                    //   0  |   1   |   0  |    1
                    //   1  |   0   |   0  |    0
                    //   1  |   1   |   0  |    1
                    cs.enforce_constraint(
                        cond.lc(),
                        lc!() + a.lc() - b.lc(),
                        lc!() + result.lc() - b.lc(),
                    )?;

                    Ok(result)
                },
            },
        }
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
            let expected_mode = if both_constant {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            for cond in [true, false] {
                let expected = Boolean::new_variable(
                    cs.clone(),
                    || Ok(if cond { a.value()? } else { b.value()? }),
                    expected_mode,
                )?;
                let cond = Boolean::new_variable(cs.clone(), || Ok(cond), expected_mode)?;
                let computed = cond.select(&a, &b)?;

                assert_eq!(expected.value(), computed.value());
                expected.enforce_equal(&computed)?;
                if !both_constant {
                    assert!(cs.is_satisfied().unwrap());
                }
            }
            Ok(())
        })
        .unwrap()
    }
}
