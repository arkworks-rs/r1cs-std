use ark_relations::gr1cs::SynthesisError;

use crate::{boolean::Boolean, eq::EqGadget};

use super::*;

impl<F: Field> EqGadget<F> for Boolean<F> {
    #[tracing::instrument(target = "gr1cs")]
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        // self | other | XNOR(self, other) | self == other
        // -----|-------|-------------------|--------------
        //   0  |   0   |         1         |      1
        //   0  |   1   |         0         |      0
        //   1  |   0   |         0         |      0
        //   1  |   1   |         1         |      1
        Ok(!(self ^ other))
    }

    #[tracing::instrument(target = "gr1cs")]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        use Boolean::*;
        let one = Variable::One;
        // We will use the following trick: a == b <=> a - b == 0
        // This works because a - b == 0 if and only if a = 0 and b = 0, or a = 1 and b
        // = 1, which is exactly the definition of a == b.

        // If condition is false, this is a no-op.
        if condition == &Constant(false) {
            return Ok(());
        }

        let cs = self.cs().or(other.cs()).or(condition.cs());
        match (self, other) {
            // 1 == 1; 0 == 0
            (Constant(true), Constant(true)) | (Constant(false), Constant(false)) => return Ok(()),
            // Constants unequal: if condition is Constant(true), unsatisfiable; if condition
            // is variable, we should enforce (a - b) * condition == 0 which will imply
            // condition = 0 in this case.
            (Constant(_), Constant(_)) if condition == &Constant(true) => {
                return Err(SynthesisError::Unsatisfiable)
            },
            _ => (),
        };

        let difference = || match (self, other) {
            // 1 - a
            (Constant(true), Var(a)) | (Var(a), Constant(true)) => lc_diff![one, a.variable()],
            // a - 0 = a
            (Constant(false), Var(a)) | (Var(a), Constant(false)) => a.variable().into(),
            // b - a
            (Var(a), Var(b)) => lc_diff![b.variable(), a.variable()],
            // both constants unequal: return ±1 accordingly
            (Constant(true), Constant(false)) => one.into(),
            (Constant(false), Constant(true)) => lc!() - one,
            // equal constants handled earlier
            (Constant(false), Constant(false)) | (Constant(true), Constant(true)) => lc!(),
        };
        cs.enforce_r1cs_constraint(difference, || condition.lc(), || lc!())?;
        Ok(())
    }

    #[tracing::instrument(target = "gr1cs")]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        use Boolean::*;
        let one = Variable::One;

        if should_enforce != &Constant(false) {
            let cs = self.cs().or(other.cs()).or(should_enforce.cs());
            // We will use the following trick: a != b <=> a + b == 1
            // This works because a + b == 1 if and only if a = 0 and b = 1, or a = 1 and b
            // = 0, which is exactly the definition of a != b.
            match (self, other) {
                // 1 != 0; 0 != 1
                (Constant(true), Constant(false)) | (Constant(false), Constant(true)) => {
                    return Ok(())
                },
                // false == false and true == true
                (Constant(_), Constant(_)) => return Err(SynthesisError::Unsatisfiable),
                (..) => (),
            }
            let sum = || match (self, other) {
                // 1 + a
                (Constant(true), Var(a)) | (Var(a), Constant(true)) => {
                    lc![one, a.variable()]
                },
                // a + 0 = a
                (Constant(false), Var(a)) | (Var(a), Constant(false)) => a.variable().into(),
                // b + a,
                (Var(a), Var(b)) => lc![b.variable(), a.variable()],
                // handled above
                (..) => unreachable!(),
            };
            cs.enforce_r1cs_constraint(sum, || should_enforce.lc(), || one.into())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        alloc::{AllocVar, AllocationMode},
        boolean::test_utils::{run_binary_exhaustive, run_unary_exhaustive},
        prelude::EqGadget,
        GR1CSVar,
    };
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn eq() {
        run_binary_exhaustive::<Fr>(|a, b| {
            let cs = a.cs().or(b.cs());
            let both_constant = a.is_constant() && b.is_constant();
            let computed = &a.is_eq(&b)?;
            let expected_mode = if both_constant {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            let expected =
                Boolean::new_variable(cs.clone(), || Ok(a.value()? == b.value()?), expected_mode)?;
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
    fn neq() {
        run_binary_exhaustive::<Fr>(|a, b| {
            let cs = a.cs().or(b.cs());
            let both_constant = a.is_constant() && b.is_constant();
            let computed = &a.is_neq(&b)?;
            let expected_mode = if both_constant {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            let expected =
                Boolean::new_variable(cs.clone(), || Ok(a.value()? != b.value()?), expected_mode)?;
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
    fn neq_and_eq_consistency() {
        run_binary_exhaustive::<Fr>(|a, b| {
            let cs = a.cs().or(b.cs());
            let both_constant = a.is_constant() && b.is_constant();
            let is_neq = &a.is_neq(&b)?;
            let is_eq = &a.is_eq(&b)?;
            let expected_mode = if both_constant {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            let expected_is_neq =
                Boolean::new_variable(cs.clone(), || Ok(a.value()? != b.value()?), expected_mode)?;
            assert_eq!(expected_is_neq.value(), is_neq.value());
            assert_ne!(expected_is_neq.value(), is_eq.value());
            expected_is_neq.enforce_equal(is_neq)?;
            expected_is_neq.enforce_equal(&!is_eq)?;
            expected_is_neq.enforce_not_equal(is_eq)?;
            if !both_constant {
                assert!(cs.is_satisfied().unwrap());
            }
            Ok(())
        })
        .unwrap()
    }

    #[test]
    fn enforce_eq_and_enforce_neq_consistency() {
        run_unary_exhaustive::<Fr>(|a| {
            let cs = a.cs();
            let not_a = !&a;
            a.enforce_equal(&a)?;
            not_a.enforce_equal(&not_a)?;
            a.enforce_not_equal(&not_a)?;
            not_a.enforce_not_equal(&a)?;
            if !a.is_constant() {
                assert!(cs.is_satisfied().unwrap());
            }
            Ok(())
        })
        .unwrap()
    }

    #[test]
    fn eq_soundness() {
        run_binary_exhaustive::<Fr>(|a, b| {
            let cs = a.cs().or(b.cs());
            let both_constant = a.is_constant() && b.is_constant();
            let computed = &a.is_eq(&b)?;
            let expected_mode = if both_constant {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            let expected =
                Boolean::new_variable(cs.clone(), || Ok(a.value()? != b.value()?), expected_mode)?;
            assert_ne!(expected.value(), computed.value());
            expected.enforce_not_equal(&computed)?;
            if !both_constant {
                assert!(cs.is_satisfied().unwrap());
            }
            Ok(())
        })
        .unwrap()
    }

    #[test]
    fn neq_soundness() {
        run_binary_exhaustive::<Fr>(|a, b| {
            let cs = a.cs().or(b.cs());
            let both_constant = a.is_constant() && b.is_constant();
            let computed = &a.is_neq(&b)?;
            let expected_mode = if both_constant {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            let expected =
                Boolean::new_variable(cs.clone(), || Ok(a.value()? == b.value()?), expected_mode)?;
            assert_ne!(expected.value(), computed.value());
            expected.enforce_not_equal(&computed)?;
            if !both_constant {
                assert!(cs.is_satisfied().unwrap());
            }
            Ok(())
        })
        .unwrap()
    }

    #[test]
    fn conditional_enforce_equal_const_unequal_cond_var_false() {
        use ark_relations::gr1cs::ConstraintSystem;
        use ark_test_curves::bls12_381::Fr;

        let cs = ConstraintSystem::<Fr>::new_ref();
        let a = Boolean::<Fr>::TRUE;
        let b = Boolean::<Fr>::FALSE;
        let cond = Boolean::new_witness(cs.clone(), || Ok(false)).unwrap();

        a.conditional_enforce_equal(&b, &cond).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn conditional_enforce_equal_const_unequal_cond_var_true_unsat() {
        use ark_relations::gr1cs::ConstraintSystem;
        use ark_test_curves::bls12_381::Fr;

        let cs = ConstraintSystem::<Fr>::new_ref();
        let a = Boolean::<Fr>::TRUE;
        let b = Boolean::<Fr>::FALSE;
        let cond = Boolean::new_witness(cs.clone(), || Ok(true)).unwrap();

        a.conditional_enforce_equal(&b, &cond).unwrap();
        assert!(!cs.is_satisfied().unwrap());
    }

    #[test]
    fn conditional_enforce_equal_const_unequal_cond_const_false_noop() {
        use ark_relations::gr1cs::ConstraintSystem;
        use ark_test_curves::bls12_381::Fr;

        let cs = ConstraintSystem::<Fr>::new_ref();
        let a = Boolean::<Fr>::TRUE;
        let b = Boolean::<Fr>::FALSE;
        let cond = Boolean::<Fr>::FALSE;

        a.conditional_enforce_equal(&b, &cond).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn conditional_enforce_equal_const_unequal_cond_const_true_errors() {
        use ark_test_curves::bls12_381::Fr;

        let a = Boolean::<Fr>::TRUE;
        let b = Boolean::<Fr>::FALSE;
        let cond = Boolean::<Fr>::TRUE;

        let err = a.conditional_enforce_equal(&b, &cond).unwrap_err();
        assert!(matches!(err, SynthesisError::Unsatisfiable));
    }
}
