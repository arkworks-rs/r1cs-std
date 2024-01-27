use ark_ff::{BitIteratorBE, Field, PrimeField};

use crate::{fields::fp::FpVar, prelude::*, Vec};
use ark_relations::r1cs::{
    ConstraintSystemRef, LinearCombination, Namespace, SynthesisError, Variable,
};
use core::borrow::Borrow;

mod allocated;
mod and;
mod cmp;
mod convert;
mod eq;
mod not;
mod or;
mod select;
mod xor;

pub use allocated::AllocatedBool;

#[cfg(test)]
mod test_utils;

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
    /// true_var.enforce_equal(&Boolean::TRUE)?;
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

    /// Convert a little-endian bitwise representation of a field element to
    /// `FpVar<F>`
    ///
    /// Wraps around if the bit representation is larger than the field modulus.
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

#[cfg(test)]
mod test {
    use super::Boolean;
    use crate::convert::ToBytesGadget;
    use crate::prelude::*;
    use ark_ff::{
        AdditiveGroup, BitIteratorBE, BitIteratorLE, Field, One, PrimeField, UniformRand,
    };
    use ark_relations::r1cs::{ConstraintSystem, SynthesisError};
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn test_boolean_to_byte() -> Result<(), SynthesisError> {
        for val in [true, false].iter() {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let a = Boolean::new_witness(cs.clone(), || Ok(*val))?;
            let bytes = a.to_bytes_le()?;
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
