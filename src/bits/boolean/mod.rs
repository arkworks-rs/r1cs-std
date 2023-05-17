use ark_ff::{BitIteratorBE, Field, PrimeField};

use crate::{fields::fp::FpVar, prelude::*, Assignment, ToConstraintFieldGadget, Vec};
use ark_relations::r1cs::{
    ConstraintSystemRef, LinearCombination, Namespace, SynthesisError, Variable,
};
use core::borrow::Borrow;

mod and;
mod cmp;
mod eq;
mod not;
mod or;
mod xor;

#[cfg(test)]
mod test_utils;

/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
///
/// In general, one should prefer using `Boolean` instead of `AllocatedBool`,
/// as `Boolean` offers better support for constant values, and implements
/// more traits.
#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub struct AllocatedBool<F: Field> {
    variable: Variable,
    cs: ConstraintSystemRef<F>,
}

pub(crate) fn bool_to_field<F: Field>(val: impl Borrow<bool>) -> F {
    if *val.borrow() {
        F::one()
    } else {
        F::zero()
    }
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
    fn new_witness_without_booleanity_check<T: Borrow<bool>>(
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

        // Constrain (1 - a) * (1 - b) = (c), ensuring c is 1 iff
        // a and b are both false, and otherwise c is 0.
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

impl<F: Field> CondSelectGadget<F> for AllocatedBool<F> {
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

/// Represents a boolean value in the constraint system which is guaranteed
/// to be either zero or one.
#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub enum Boolean<F: Field> {
    Var(AllocatedBool<F>),
    Constant(bool),
}

impl<F: Field> R1CSVar<F> for Boolean<F> {
    type Value = bool;

    fn cs(&self) -> ConstraintSystemRef<F> {
        match self {
            Self::Var(a) => a.cs.clone(),
            _ => ConstraintSystemRef::None,
        }
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        match self {
            Boolean::Constant(c) => Ok(*c),
            Boolean::Var(ref v) => v.value(),
        }
    }
}

impl<F: Field> Boolean<F> {
    /// The constant `true`.
    pub const TRUE: Self = Boolean::Constant(true);

    /// The constant `false`.
    pub const FALSE: Self = Boolean::Constant(false);

    /// Constructs a `Boolean` vector from a slice of constant `u8`.
    /// The `u8`s are decomposed in little-endian manner.
    ///
    /// This *does not* create any new variables or constraints.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let t = Boolean::<Fr>::TRUE;
    /// let f = Boolean::<Fr>::FALSE;
    ///
    /// let bits = vec![f, t];
    /// let generated_bits = Boolean::constant_vec_from_bytes(&[2]);
    /// bits[..2].enforce_equal(&generated_bits[..2])?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    pub fn constant_vec_from_bytes(values: &[u8]) -> Vec<Self> {
        let mut bits = vec![];
        for byte in values {
            for i in 0..8 {
                bits.push(Self::Constant(((byte >> i) & 1u8) == 1u8));
            }
        }
        bits
    }

    /// Constructs a constant `Boolean` with value `b`.
    ///
    /// This *does not* create any new variables or constraints.
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let true_var = Boolean::<Fr>::TRUE;
    /// let false_var = Boolean::<Fr>::FALSE;
    ///
    /// true_var.enforce_equal(&Boolean::constant(true))?;
    /// false_var.enforce_equal(&Boolean::constant(false))?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn constant(b: bool) -> Self {
        Boolean::Constant(b)
    }

    /// Constructs a `LinearCombination` from `Self`'s variables according
    /// to the following map.
    ///
    /// * `Boolean::TRUE => lc!() + Variable::One`
    /// * `Boolean::FALSE => lc!()`
    /// * `Boolean::Var(v) => lc!() + v.variable()`
    pub fn lc(&self) -> LinearCombination<F> {
        match self {
            &Boolean::Constant(false) => lc!(),
            &Boolean::Constant(true) => lc!() + Variable::One,
            Boolean::Var(v) => v.variable().into(),
        }
    }

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
        let mut cur: Option<Self> = None;
        for next in bits {
            cur = if let Some(b) = cur {
                Some(b & next)
            } else {
                Some(next.clone())
            };
        }

        Ok(cur.expect("should not be 0"))
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
        let mut cur: Option<Self> = None;
        for next in bits {
            cur = if let Some(b) = cur {
                Some(b | next)
            } else {
                Some(next.clone())
            };
        }

        Ok(cur.expect("should not be 0"))
    }

    /// Outputs `(bits[0] & bits[1] & ... & bits.last().unwrap()).not()`.
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

    /// Enforces that `Self::kary_nand(bits).is_eq(&Boolean::TRUE)`.
    ///
    /// Informally, this means that at least one element in `bits` must be
    /// `false`.
    #[tracing::instrument(target = "r1cs")]
    fn enforce_kary_nand(bits: &[Self]) -> Result<(), SynthesisError> {
        Self::kary_nand(bits)?.enforce_equal(&Boolean::TRUE)
    }

    /// Convert a little-endian bitwise representation of a field element to
    /// `FpVar<F>`
    #[tracing::instrument(target = "r1cs", skip(bits))]
    pub fn le_bits_to_fp(bits: &[Self]) -> Result<FpVar<F>, SynthesisError>
    where
        F: PrimeField,
    {
        // Compute the value of the `FpVar` variable via double-and-add.
        let mut value = None;
        let cs = bits.cs();
        // Assign a value only when `cs` is in setup mode, or if we are constructing
        // a constant.
        let should_construct_value = (!cs.is_in_setup_mode()) || bits.is_constant();
        if should_construct_value {
            let bits = bits.iter().map(|b| b.value().unwrap()).collect::<Vec<_>>();
            let bytes = bits
                .chunks(8)
                .map(|c| {
                    let mut value = 0u8;
                    for (i, &bit) in c.iter().enumerate() {
                        value += (bit as u8) << i;
                    }
                    value
                })
                .collect::<Vec<_>>();
            value = Some(F::from_le_bytes_mod_order(&bytes));
        }

        if bits.is_constant() {
            Ok(FpVar::constant(value.unwrap()))
        } else {
            let mut power = F::one();
            // Compute a linear combination for the new field variable, again
            // via double and add.

            let combined = bits
                .iter()
                .map(|b| {
                    let result = FpVar::from(b.clone()) * power;
                    power.double_in_place();
                    result
                })
                .sum();
            // If the number of bits is less than the size of the field,
            // then we do not need to enforce that the element is less than
            // the modulus.
            if bits.len() >= F::MODULUS_BIT_SIZE as usize {
                Self::enforce_in_field_le(bits)?;
            }
            Ok(combined)
        }
    }

    /// Enforces that `bits`, when interpreted as a integer, is less than
    /// `F::characteristic()`, That is, interpret bits as a little-endian
    /// integer, and enforce that this integer is "in the field Z_p", where
    /// `p = F::characteristic()` .
    #[tracing::instrument(target = "r1cs")]
    pub fn enforce_in_field_le(bits: &[Self]) -> Result<(), SynthesisError> {
        // `bits` < F::characteristic() <==> `bits` <= F::characteristic() -1
        let mut b = F::characteristic().to_vec();
        assert_eq!(b[0] % 2, 1);
        b[0] -= 1; // This works, because the LSB is one, so there's no borrows.
        let run = Self::enforce_smaller_or_equal_than_le(bits, b)?;

        // We should always end in a "run" of zeros, because
        // the characteristic is an odd prime. So, this should
        // be empty.
        assert!(run.is_empty());

        Ok(())
    }

    /// Enforces that `bits` is less than or equal to `element`,
    /// when both are interpreted as (little-endian) integers.
    #[tracing::instrument(target = "r1cs", skip(element))]
    pub fn enforce_smaller_or_equal_than_le<'a>(
        bits: &[Self],
        element: impl AsRef<[u64]>,
    ) -> Result<Vec<Self>, SynthesisError> {
        let b: &[u64] = element.as_ref();

        let mut bits_iter = bits.iter().rev(); // Iterate in big-endian

        // Runs of ones in r
        let mut last_run = Boolean::constant(true);
        let mut current_run = vec![];

        let mut element_num_bits = 0;
        for _ in BitIteratorBE::without_leading_zeros(b) {
            element_num_bits += 1;
        }

        if bits.len() > element_num_bits {
            let mut or_result = Boolean::constant(false);
            for should_be_zero in &bits[element_num_bits..] {
                or_result |= should_be_zero;
                let _ = bits_iter.next().unwrap();
            }
            or_result.enforce_equal(&Boolean::constant(false))?;
        }

        for (b, a) in BitIteratorBE::without_leading_zeros(b).zip(bits_iter.by_ref()) {
            if b {
                // This is part of a run of ones.
                current_run.push(a.clone());
            } else {
                if !current_run.is_empty() {
                    // This is the start of a run of zeros, but we need
                    // to k-ary AND against `last_run` first.

                    current_run.push(last_run.clone());
                    last_run = Self::kary_and(&current_run)?;
                    current_run.truncate(0);
                }

                // If `last_run` is true, `a` must be false, or it would
                // not be in the field.
                //
                // If `last_run` is false, `a` can be true or false.
                //
                // Ergo, at least one of `last_run` and `a` must be false.
                Self::enforce_kary_nand(&[last_run.clone(), a.clone()])?;
            }
        }
        assert!(bits_iter.next().is_none());

        Ok(current_run)
    }

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

impl<F: Field> From<AllocatedBool<F>> for Boolean<F> {
    fn from(b: AllocatedBool<F>) -> Self {
        Boolean::Var(b)
    }
}

impl<F: Field> AllocVar<bool, F> for Boolean<F> {
    fn new_variable<T: Borrow<bool>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        if mode == AllocationMode::Constant {
            Ok(Boolean::Constant(*f()?.borrow()))
        } else {
            AllocatedBool::new_variable(cs, f, mode).map(Boolean::Var)
        }
    }
}

impl<F: Field> ToBytesGadget<F> for Boolean<F> {
    /// Outputs `1u8` if `self` is true, and `0u8` otherwise.
    #[tracing::instrument(target = "r1cs")]
    fn to_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let value = self.value().map(u8::from).ok();
        let mut bits = [Boolean::FALSE; 8];
        bits[0] = self.clone();
        Ok(vec![UInt8 { bits, value }])
    }
}

impl<F: PrimeField> ToConstraintFieldGadget<F> for Boolean<F> {
    #[tracing::instrument(target = "r1cs")]
    fn to_constraint_field(&self) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let var = From::from(self.clone());
        Ok(vec![var])
    }
}

impl<F: Field> CondSelectGadget<F> for Boolean<F> {
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
mod test {
    use super::{AllocatedBool, Boolean};
    use crate::prelude::*;
    use ark_ff::{BitIteratorBE, BitIteratorLE, Field, One, PrimeField, UniformRand};
    use ark_relations::r1cs::{ConstraintSystem, SynthesisError};
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn test_boolean_to_byte() -> Result<(), SynthesisError> {
        for val in [true, false].iter() {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let a = Boolean::new_witness(cs.clone(), || Ok(*val))?;
            let bytes = a.to_bytes()?;
            assert_eq!(bytes.len(), 1);
            let byte = &bytes[0];
            assert_eq!(byte.value()?, *val as u8);

            for (i, bit) in byte.bits.iter().enumerate() {
                assert_eq!(bit.value()?, (byte.value()? >> i) & 1 == 1);
            }
        }
        Ok(())
    }

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

    #[test]
    fn test_smaller_than_or_equal_to() -> Result<(), SynthesisError> {
        let mut rng = ark_std::test_rng();
        for _ in 0..1000 {
            let mut r = Fr::rand(&mut rng);
            let mut s = Fr::rand(&mut rng);
            if r > s {
                core::mem::swap(&mut r, &mut s)
            }

            let cs = ConstraintSystem::<Fr>::new_ref();

            let native_bits: Vec<_> = BitIteratorLE::new(r.into_bigint()).collect();
            let bits = Vec::new_witness(cs.clone(), || Ok(native_bits))?;
            Boolean::enforce_smaller_or_equal_than_le(&bits, s.into_bigint())?;

            assert!(cs.is_satisfied().unwrap());
        }

        for _ in 0..1000 {
            let r = Fr::rand(&mut rng);
            if r == -Fr::one() {
                continue;
            }
            let s = r + Fr::one();
            let s2 = r.double();
            let cs = ConstraintSystem::<Fr>::new_ref();

            let native_bits: Vec<_> = BitIteratorLE::new(r.into_bigint()).collect();
            let bits = Vec::new_witness(cs.clone(), || Ok(native_bits))?;
            Boolean::enforce_smaller_or_equal_than_le(&bits, s.into_bigint())?;
            if r < s2 {
                Boolean::enforce_smaller_or_equal_than_le(&bits, s2.into_bigint())?;
            }

            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    #[test]
    fn test_enforce_in_field() -> Result<(), SynthesisError> {
        {
            let cs = ConstraintSystem::<Fr>::new_ref();

            let mut bits = vec![];
            for b in BitIteratorBE::new(Fr::characteristic()).skip(1) {
                bits.push(Boolean::new_witness(cs.clone(), || Ok(b))?);
            }
            bits.reverse();

            Boolean::enforce_in_field_le(&bits)?;

            assert!(!cs.is_satisfied().unwrap());
        }

        let mut rng = ark_std::test_rng();

        for _ in 0..1000 {
            let r = Fr::rand(&mut rng);
            let cs = ConstraintSystem::<Fr>::new_ref();

            let mut bits = vec![];
            for b in BitIteratorBE::new(r.into_bigint()).skip(1) {
                bits.push(Boolean::new_witness(cs.clone(), || Ok(b))?);
            }
            bits.reverse();

            Boolean::enforce_in_field_le(&bits)?;

            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    #[test]
    fn test_enforce_nand() -> Result<(), SynthesisError> {
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
    fn test_kary_and() -> Result<(), SynthesisError> {
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

    #[test]
    fn test_bits_to_fp() -> Result<(), SynthesisError> {
        use AllocationMode::*;
        let rng = &mut ark_std::test_rng();
        let cs = ConstraintSystem::<Fr>::new_ref();

        let modes = [Input, Witness, Constant];
        for &mode in modes.iter() {
            for _ in 0..1000 {
                let f = Fr::rand(rng);
                let bits = BitIteratorLE::new(f.into_bigint()).collect::<Vec<_>>();
                let bits: Vec<_> =
                    AllocVar::new_variable(cs.clone(), || Ok(bits.as_slice()), mode)?;
                let f = AllocVar::new_variable(cs.clone(), || Ok(f), mode)?;
                let claimed_f = Boolean::le_bits_to_fp(&bits)?;
                claimed_f.enforce_equal(&f)?;
            }

            for _ in 0..1000 {
                let f = Fr::from(u64::rand(rng));
                let bits = BitIteratorLE::new(f.into_bigint()).collect::<Vec<_>>();
                let bits: Vec<_> =
                    AllocVar::new_variable(cs.clone(), || Ok(bits.as_slice()), mode)?;
                let f = AllocVar::new_variable(cs.clone(), || Ok(f), mode)?;
                let claimed_f = Boolean::le_bits_to_fp(&bits)?;
                claimed_f.enforce_equal(&f)?;
            }
            assert!(cs.is_satisfied().unwrap());
        }

        Ok(())
    }
}
