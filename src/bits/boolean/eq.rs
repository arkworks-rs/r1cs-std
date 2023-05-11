use ark_relations::r1cs::SynthesisError;

use crate::boolean::Boolean;
use crate::eq::EqGadget;

use super::*;

impl<F: Field> EqGadget<F> for Boolean<F> {
    #[tracing::instrument(target = "r1cs")]
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        // self | other | XNOR(self, other) | self == other
        // -----|-------|-------------------|--------------
        //   0  |   0   |         1         |      1
        //   0  |   1   |         0         |      0
        //   1  |   0   |         0         |      0
        //   1  |   1   |         1         |      1
        Ok(!(self ^ other))
    }

    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        use Boolean::*;
        let one = Variable::One;
        // We will use the following trick: a == b <=> a - b == 0
        // This works because a - b == 0 if and only if a = 0 and b = 0, or a = 1 and b = 1,
        // which is exactly the definition of a == b.
        let difference = match (self, other) {
            // 1 == 1; 0 == 0
            (Constant(true), Constant(true)) | (Constant(false), Constant(false)) => return Ok(()),
            // false != true
            (Constant(_), Constant(_)) => return Err(SynthesisError::Unsatisfiable),
            // 1 - a
            (Constant(true), Var(a)) | (Var(a), Constant(true)) => lc!() + one - a.variable(),
            // a - 0 = a
            (Constant(false), Var(a)) | (Var(a), Constant(false)) => lc!() + a.variable(),
            // b - a,
            (Var(a), Var(b)) => lc!() + b.variable() - a.variable(),
        };

        if condition != &Constant(false) {
            let cs = self.cs().or(other.cs()).or(condition.cs());
            cs.enforce_constraint(lc!() + difference, condition.lc(), lc!())?;
        }
        Ok(())
    }

    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<F>,
    ) -> Result<(), SynthesisError> {
        use Boolean::*;
        let one = Variable::One;
        // We will use the following trick: a != b <=> a + b == 1
        // This works because a + b == 1 if and only if a = 0 and b = 1, or a = 1 and b = 0,
        // which is exactly the definition of a != b.
        let sum = match (self, other) {
            // 1 != 0; 0 != 1
            (Constant(true), Constant(false)) | (Constant(false), Constant(true)) => return Ok(()),
            // false == false and true == true
            (Constant(_), Constant(_)) => return Err(SynthesisError::Unsatisfiable),
            // 1 + a
            (Constant(true), Var(a)) | (Var(a), Constant(true)) => lc!() + one + a.variable(),
            // a + 0 = a
            (Constant(false), Var(a)) | (Var(a), Constant(false)) => lc!() + a.variable(),
            // b + a,
            (Var(a), Var(b)) => lc!() + b.variable() + a.variable(),
        };

        if should_enforce != &Constant(false) {
            let cs = self.cs().or(other.cs()).or(should_enforce.cs());
            cs.enforce_constraint(sum, should_enforce.lc(), lc!() + one)?;
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
        R1CSVar,
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
}
