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
        let difference = match (self, other) {
            // 1 == 1; 0 == 0
            (Constant(true), Constant(true)) | (Constant(false), Constant(false)) => return Ok(()),
            // false != true
            (Constant(_), Constant(_)) => return Err(SynthesisError::AssignmentMissing),
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
        let difference = match (self, other) {
            // 1 != 0; 0 != 1
            (Constant(true), Constant(false)) | (Constant(false), Constant(true)) => return Ok(()),
            // false == false and true == true
            (Constant(_), Constant(_)) => return Err(SynthesisError::AssignmentMissing),
            // 1 - a
            (Constant(true), Var(a)) | (Var(a), Constant(true)) => lc!() + one - a.variable(),
            // a - 0 = a
            (Constant(false), Var(a)) | (Var(a), Constant(false)) => lc!() + a.variable(),
            // b - a,
            (Var(a), Var(b)) => lc!() + b.variable() - a.variable(),
        };

        if should_enforce != &Constant(false) {
            let cs = self.cs().or(other.cs()).or(should_enforce.cs());
            cs.enforce_constraint(difference, should_enforce.lc(), should_enforce.lc())?;
        }
        Ok(())
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
            let computed = &a.is_eq(&b)?;
            let expected_mode = if both_constant {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            let expected = Boolean::new_variable(
                cs.clone(),
                || Ok(a.value().unwrap() == b.value().unwrap()),
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
