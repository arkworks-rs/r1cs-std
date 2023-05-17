use ark_ff::{Field, PrimeField};
use core::{borrow::Borrow, convert::TryFrom, fmt::Debug};
use num_traits::PrimInt;

use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};

use crate::{boolean::Boolean, prelude::*, Assignment, Vec};

mod add;
mod and;
mod cmp;
mod convert;
mod eq;
mod not;
mod or;
mod rotate;
mod xor;

#[cfg(test)]
pub(crate) mod test_utils;

/// This struct represent an unsigned `N` bit integer as a sequence of `N` [`Boolean`]s.
#[derive(Clone, Debug)]
pub struct UInt<const N: usize, T: PrimInt + Debug, F: Field> {
    #[doc(hidden)]
    pub bits: [Boolean<F>; N],
    #[doc(hidden)]
    pub value: Option<T>,
}

impl<const N: usize, T: PrimInt + Debug, F: Field> R1CSVar<F> for UInt<N, T, F> {
    type Value = T;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.bits.as_ref().cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let mut value = T::zero();
        for (i, bit) in self.bits.iter().enumerate() {
            value = value + (T::from(bit.value()? as u8).unwrap() << i);
        }
        debug_assert_eq!(self.value, Some(value));
        Ok(value)
    }
}

impl<const N: usize, T: PrimInt + Debug, F: Field> UInt<N, T, F> {
    /// Construct a constant [`UInt`] from the native unsigned integer type.
    ///
    /// This *does not* create new variables or constraints.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let var = UInt8::new_witness(cs.clone(), || Ok(2))?;
    ///
    /// let constant = UInt8::constant(2);
    /// var.enforce_equal(&constant)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    pub fn constant(value: T) -> Self {
        let mut bits = [Boolean::FALSE; N];
        let mut bit_values = value;

        for i in 0..N {
            bits[i] = Boolean::constant((bit_values & T::one()) == T::one());
            bit_values = bit_values >> 1;
        }

        Self {
            bits,
            value: Some(value),
        }
    }

    /// Construct a constant vector of [`UInt`] from a vector of the native type
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
    /// let var = vec![UInt8::new_witness(cs.clone(), || Ok(2))?];
    ///
    /// let constant = UInt8::constant_vec(&[2]);
    /// var.enforce_equal(&constant)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    pub fn constant_vec(values: &[T]) -> Vec<Self> {
        values.iter().map(|v| Self::constant(*v)).collect()
    }

    /// Allocates a slice of `uN`'s as private witnesses.
    pub fn new_witness_vec(
        cs: impl Into<Namespace<F>>,
        values: &[impl Into<Option<T>> + Copy],
    ) -> Result<Vec<Self>, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let mut output_vec = Vec::with_capacity(values.len());
        for value in values {
            let byte: Option<T> = Into::into(*value);
            output_vec.push(Self::new_witness(cs.clone(), || byte.get())?);
        }
        Ok(output_vec)
    }
}

impl<const N: usize, T: PrimInt + Debug, ConstraintF: Field> CondSelectGadget<ConstraintF>
    for UInt<N, T, ConstraintF>
{
    #[tracing::instrument(target = "r1cs", skip(cond, true_value, false_value))]
    fn conditionally_select(
        cond: &Boolean<ConstraintF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let selected_bits = true_value
            .bits
            .iter()
            .zip(&false_value.bits)
            .map(|(t, f)| cond.select(t, f));
        let mut bits = [Boolean::FALSE; N];
        for (result, new) in bits.iter_mut().zip(selected_bits) {
            *result = new?;
        }

        let value = cond.value().ok().and_then(|cond| {
            if cond {
                true_value.value().ok()
            } else {
                false_value.value().ok()
            }
        });
        Ok(Self { bits, value })
    }
}

impl<const N: usize, T: PrimInt + Debug, ConstraintF: Field> AllocVar<T, ConstraintF>
    for UInt<N, T, ConstraintF>
{
    fn new_variable<S: Borrow<T>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<S, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let value = f().map(|f| *f.borrow()).ok();

        let mut values = [None; N];
        if let Some(val) = value {
            values
                .iter_mut()
                .enumerate()
                .for_each(|(i, v)| *v = Some(((val >> i) & T::one()) == T::one()));
        }

        let mut bits = [Boolean::FALSE; N];
        for (b, v) in bits.iter_mut().zip(&values) {
            *b = Boolean::new_variable(cs.clone(), || v.get(), mode)?;
        }
        Ok(Self { bits, value })
    }
}

// #[cfg(test)]
// mod test {
//     use super::UInt;
//     use crate::{bits::boolean::Boolean, prelude::*, Vec};
//     use ark_relations::r1cs::{ConstraintSystem, SynthesisError};
//     use ark_std::rand::Rng;
//     use ark_test_curves::mnt4_753::Fr;

//     #[test]
//     fn test_from_bits() -> Result<(), SynthesisError> {
//         let mut rng = ark_std::test_rng();

//         for _ in 0..1000 {
//             let v = (0..$size)
//             .map(|_| Boolean::constant(rng.gen()))
//             .collect::<Vec<Boolean<Fr>>>();

//             let b = UInt::from_bits_le(&v);

//             for (i, bit) in b.bits.iter().enumerate() {
//                 match bit {
//                     &Boolean::Constant(bit) => {
//                         assert_eq!(bit, ((b.value()? >> i) & 1 == 1));
//                     },
//                     _ => unreachable!(),
//                 }
//             }

//             let expected_to_be_same = b.to_bits_le();

//             for x in v.iter().zip(expected_to_be_same.iter()) {
//                 match x {
//                     (&Boolean::TRUE, &Boolean::TRUE) => {},
//                     (&Boolean::FALSE, &Boolean::FALSE) => {},
//                     _ => unreachable!(),
//                 }
//             }
//         }
//         Ok(())
//     }

//     #[test]
//     fn test_xor() -> Result<(), SynthesisError> {
//         use Boolean::*;
//         let mut rng = ark_std::test_rng();

//         for _ in 0..1000 {
//             let cs = ConstraintSystem::<Fr>::new_ref();

//             let a: $native = rng.gen();
//             let b: $native = rng.gen();
//             let c: $native = rng.gen();

//             let mut expected = a ^ b ^ c;

//             let a_bit = $name::new_witness(cs.clone(), || Ok(a))?;
//             let b_bit = $name::constant(b);
//             let c_bit = $name::new_witness(cs.clone(), || Ok(c))?;

//             let r = a_bit.xor(&b_bit).unwrap();
//             let r = r.xor(&c_bit).unwrap();

//             assert!(cs.is_satisfied().unwrap());

//             assert!(r.value == Some(expected));

//             for b in r.bits.iter() {
//                 match b {
//                     Is(b) => assert_eq!(b.value()?, (expected & 1 == 1)),
//                     Not(b) => assert_eq!(!b.value()?, (expected & 1 == 1)),
//                     Constant(b) => assert_eq!(*b, (expected & 1 == 1)),
//                 }

//                 expected >>= 1;
//             }
//         }
//         Ok(())
//     }

//     #[test]
//     fn test_add_many_constants() -> Result<(), SynthesisError> {
//         let mut rng = ark_std::test_rng();

//         for _ in 0..1000 {
//             let cs = ConstraintSystem::<Fr>::new_ref();

//             let a: $native = rng.gen();
//             let b: $native = rng.gen();
//             let c: $native = rng.gen();

//             let a_bit = $name::new_constant(cs.clone(), a)?;
//             let b_bit = $name::new_constant(cs.clone(), b)?;
//             let c_bit = $name::new_constant(cs.clone(), c)?;

//             let mut expected = a.wrapping_add(b).wrapping_add(c);

//             let r = $name::add_many(&[a_bit, b_bit, c_bit]).unwrap();

//             assert!(r.value == Some(expected));

//             for b in r.bits.iter() {
//                 match b {
//                     Boolean::Is(_) => unreachable!(),
//                     Boolean::Not(_) => unreachable!(),
//                     Boolean::Constant(b) => assert_eq!(*b, (expected & 1 == 1)),
//                 }

//                 expected >>= 1;
//             }
//         }
//         Ok(())
//     }
