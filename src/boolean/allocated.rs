use core::borrow::Borrow;

use ark_ff::{Field, PrimeField};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError, Variable};

use crate::{
    alloc::{AllocVar, AllocationMode},
    select::CondSelectGadget,
    Assignment,
};

use super::Boolean;

/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
///
/// In general, one should prefer using `Boolean` instead of `AllocatedBool`,
/// as `Boolean` offers better support for constant values, and implements
/// more traits.
#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub struct AllocatedBool<F: Field> {
    pub(super) variable: Variable,
    pub(super) cs: ConstraintSystemRef<F>,
}

pub(crate) fn bool_to_field<F: Field>(val: impl Borrow<bool>) -> F {
    F::from(*val.borrow())
}

impl<F: Field> AllocatedBool<F> {
    /// Get the assigned value for `self`.
    pub fn value(&self) -> Result<bool, SynthesisError> {
        let value = self.cs.assigned_value(self.variable).get()?;
        if value.is_zero() {
            Ok(false)
        } else if value.is_one() {
            Ok(true)
        } else {
            unreachable!("Incorrect value assigned: {:?}", value);
        }
    }

    /// Get the R1CS variable for `self`.
    pub fn variable(&self) -> Variable {
        self.variable
    }

    /// Allocate a witness variable without a booleanity check.
    #[doc(hidden)]
    pub fn new_witness_without_booleanity_check<T: Borrow<bool>>(
        cs: ConstraintSystemRef<F>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
    ) -> Result<Self, SynthesisError> {
        let variable = cs.new_witness_variable(|| f().map(bool_to_field))?;
        Ok(Self { variable, cs })
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBool`.
    #[tracing::instrument(target = "r1cs")]
    pub fn not(&self) -> Result<Self, SynthesisError> {
        let variable = self.cs.new_lc(lc!() + Variable::One - self.variable)?;
        Ok(Self {
            variable,
            cs: self.cs.clone(),
        })
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBool`.
    #[tracing::instrument(target = "r1cs")]
    pub fn xor(&self, b: &Self) -> Result<Self, SynthesisError> {
        let result = Self::new_witness_without_booleanity_check(self.cs.clone(), || {
            Ok(self.value()? ^ b.value()?)
        })?;

        // Constrain (a + a) * (b) = (a + b - c)
        // Given that a and b are boolean constrained, if they
        // are equal, the only solution for c is 0, and if they
        // are different, the only solution for c is 1.
        //
        // ¬(a ∧ b) ∧ ¬(¬a ∧ ¬b) = c
        // (1 - (a * b)) * (1 - ((1 - a) * (1 - b))) = c
        // (1 - ab) * (1 - (1 - a - b + ab)) = c
        // (1 - ab) * (a + b - ab) = c
        // a + b - ab - (a^2)b - (b^2)a + (a^2)(b^2) = c
        // a + b - ab - ab - ab + ab = c
        // a + b - 2ab = c
        // -2a * b = c - a - b
        // 2a * b = a + b - c
        // (a + a) * b = a + b - c
        self.cs.enforce_constraint(
            lc!() + self.variable + self.variable,
            lc!() + b.variable,
            lc!() + self.variable + b.variable - result.variable,
        )?;

        Ok(result)
    }

    /// Performs an AND operation over the two operands, returning
    /// an `AllocatedBool`.
    #[tracing::instrument(target = "r1cs")]
    pub fn and(&self, b: &Self) -> Result<Self, SynthesisError> {
        let result = Self::new_witness_without_booleanity_check(self.cs.clone(), || {
            Ok(self.value()? & b.value()?)
        })?;

        // Constrain (a) * (b) = (c), ensuring c is 1 iff
        // a AND b are both 1.
        self.cs.enforce_constraint(
            lc!() + self.variable,
            lc!() + b.variable,
            lc!() + result.variable,
        )?;

        Ok(result)
    }

    /// Performs an OR operation over the two operands, returning
    /// an `AllocatedBool`.
    #[tracing::instrument(target = "r1cs")]
    pub fn or(&self, b: &Self) -> Result<Self, SynthesisError> {
        let result = Self::new_witness_without_booleanity_check(self.cs.clone(), || {
            Ok(self.value()? | b.value()?)
        })?;

        // Constrain (1 - a) * (1 - b) = (1 - c), ensuring c is 0 iff
        // a and b are both false, and otherwise c is 1.
        self.cs.enforce_constraint(
            lc!() + Variable::One - self.variable,
            lc!() + Variable::One - b.variable,
            lc!() + Variable::One - result.variable,
        )?;

        Ok(result)
    }

    /// Calculates `a AND (NOT b)`.
    #[tracing::instrument(target = "r1cs")]
    pub fn and_not(&self, b: &Self) -> Result<Self, SynthesisError> {
        let result = Self::new_witness_without_booleanity_check(self.cs.clone(), || {
            Ok(self.value()? & !b.value()?)
        })?;

        // Constrain (a) * (1 - b) = (c), ensuring c is 1 iff
        // a is true and b is false, and otherwise c is 0.
        self.cs.enforce_constraint(
            lc!() + self.variable,
            lc!() + Variable::One - b.variable,
            lc!() + result.variable,
        )?;

        Ok(result)
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    #[tracing::instrument(target = "r1cs")]
    pub fn nor(&self, b: &Self) -> Result<Self, SynthesisError> {
        let result = Self::new_witness_without_booleanity_check(self.cs.clone(), || {
            Ok(!(self.value()? | b.value()?))
        })?;

        // Constrain (1 - a) * (1 - b) = (c), ensuring c is 1 iff
        // a and b are both false, and otherwise c is 0.
        self.cs.enforce_constraint(
            lc!() + Variable::One - self.variable,
            lc!() + Variable::One - b.variable,
            lc!() + result.variable,
        )?;

        Ok(result)
    }
}

impl<F: Field> AllocVar<bool, F> for AllocatedBool<F> {
    /// Produces a new variable of the appropriate kind
    /// (instance or witness), with a booleanity check.
    ///
    /// N.B.: we could omit the booleanity check when allocating `self`
    /// as a new public input, but that places an additional burden on
    /// protocol designers. Better safe than sorry!
    fn new_variable<T: Borrow<bool>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        if mode == AllocationMode::Constant {
            let variable = if *f()?.borrow() {
                Variable::One
            } else {
                Variable::Zero
            };
            Ok(Self { variable, cs })
        } else {
            let variable = if mode == AllocationMode::Input {
                cs.new_input_variable(|| f().map(bool_to_field))?
            } else {
                cs.new_witness_variable(|| f().map(bool_to_field))?
            };

            // Constrain: (1 - a) * a = 0
            // This constrains a to be either 0 or 1.

            cs.enforce_constraint(lc!() + Variable::One - variable, lc!() + variable, lc!())?;

            Ok(Self { variable, cs })
        }
    }
}

impl<F: PrimeField> CondSelectGadget<F> for AllocatedBool<F> {
    #[tracing::instrument(target = "r1cs")]
    fn conditionally_select(
        cond: &Boolean<F>,
        true_val: &Self,
        false_val: &Self,
    ) -> Result<Self, SynthesisError> {
        let res = Boolean::conditionally_select(
            cond,
            &true_val.clone().into(),
            &false_val.clone().into(),
        )?;
        match res {
            Boolean::Var(a) => Ok(a),
            _ => unreachable!("Impossible"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use ark_relations::r1cs::ConstraintSystem;
    use ark_test_curves::bls12_381::Fr;
    #[test]
    fn allocated_xor() -> Result<(), SynthesisError> {
        for a_val in [false, true].iter().copied() {
            for b_val in [false, true].iter().copied() {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let a = AllocatedBool::new_witness(cs.clone(), || Ok(a_val))?;
                let b = AllocatedBool::new_witness(cs.clone(), || Ok(b_val))?;
                let c = AllocatedBool::xor(&a, &b)?;
                assert_eq!(c.value()?, a_val ^ b_val);

                assert!(cs.is_satisfied().unwrap());
                assert_eq!(a.value()?, (a_val));
                assert_eq!(b.value()?, (b_val));
                assert_eq!(c.value()?, (a_val ^ b_val));
            }
        }
        Ok(())
    }

    #[test]
    fn allocated_or() -> Result<(), SynthesisError> {
        for a_val in [false, true].iter().copied() {
            for b_val in [false, true].iter().copied() {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let a = AllocatedBool::new_witness(cs.clone(), || Ok(a_val))?;
                let b = AllocatedBool::new_witness(cs.clone(), || Ok(b_val))?;
                let c = AllocatedBool::or(&a, &b)?;
                assert_eq!(c.value()?, a_val | b_val);

                assert!(cs.is_satisfied().unwrap());
                assert_eq!(a.value()?, (a_val));
                assert_eq!(b.value()?, (b_val));
                assert_eq!(c.value()?, (a_val | b_val));
            }
        }
        Ok(())
    }

    #[test]
    fn allocated_and() -> Result<(), SynthesisError> {
        for a_val in [false, true].iter().copied() {
            for b_val in [false, true].iter().copied() {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let a = AllocatedBool::new_witness(cs.clone(), || Ok(a_val))?;
                let b = AllocatedBool::new_witness(cs.clone(), || Ok(b_val))?;
                let c = AllocatedBool::and(&a, &b)?;
                assert_eq!(c.value()?, a_val & b_val);

                assert!(cs.is_satisfied().unwrap());
                assert_eq!(a.value()?, (a_val));
                assert_eq!(b.value()?, (b_val));
                assert_eq!(c.value()?, (a_val & b_val));
            }
        }
        Ok(())
    }

    #[test]
    fn allocated_and_not() -> Result<(), SynthesisError> {
        for a_val in [false, true].iter().copied() {
            for b_val in [false, true].iter().copied() {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let a = AllocatedBool::new_witness(cs.clone(), || Ok(a_val))?;
                let b = AllocatedBool::new_witness(cs.clone(), || Ok(b_val))?;
                let c = AllocatedBool::and_not(&a, &b)?;
                assert_eq!(c.value()?, a_val & !b_val);

                assert!(cs.is_satisfied().unwrap());
                assert_eq!(a.value()?, (a_val));
                assert_eq!(b.value()?, (b_val));
                assert_eq!(c.value()?, (a_val & !b_val));
            }
        }
        Ok(())
    }

    #[test]
    fn allocated_nor() -> Result<(), SynthesisError> {
        for a_val in [false, true].iter().copied() {
            for b_val in [false, true].iter().copied() {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let a = AllocatedBool::new_witness(cs.clone(), || Ok(a_val))?;
                let b = AllocatedBool::new_witness(cs.clone(), || Ok(b_val))?;
                let c = AllocatedBool::nor(&a, &b)?;
                assert_eq!(c.value()?, !a_val & !b_val);

                assert!(cs.is_satisfied().unwrap());
                assert_eq!(a.value()?, (a_val));
                assert_eq!(b.value()?, (b_val));
                assert_eq!(c.value()?, (!a_val & !b_val));
            }
        }
        Ok(())
    }
}
