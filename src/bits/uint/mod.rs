use ark_ff::{Field, One, PrimeField, Zero};
use core::{borrow::Borrow, convert::TryFrom, fmt::Debug};
use num_bigint::BigUint;
use num_traits::{NumCast, PrimInt};

use ark_relations::r1cs::{
    ConstraintSystemRef, LinearCombination, Namespace, SynthesisError, Variable,
};

use crate::{
    boolean::{AllocatedBool, Boolean},
    prelude::*,
    Assignment, Vec,
};

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

    /// Perform modular addition of `operands`.
    ///
    /// The user must ensure that overflow does not occur.
    #[tracing::instrument(target = "r1cs", skip(operands))]
    pub fn add_many(operands: &[Self]) -> Result<Self, SynthesisError>
    where
        F: PrimeField,
    {
        // Make some arbitrary bounds for ourselves to avoid overflows
        // in the scalar field
        assert!(F::MODULUS_BIT_SIZE as usize >= 2 * N);

        assert!(operands.len() >= 1);
        assert!(N as u32 + ark_std::log2(operands.len()) <= F::MODULUS_BIT_SIZE);

        if operands.len() == 1 {
            return Ok(operands[0].clone());
        }

        // Compute the maximum value of the sum so we allocate enough bits for
        // the result
        let mut max_value = T::max_value() * T::from(operands.len() as u128).unwrap();

        // Keep track of the resulting value
        let mut result_value = Some(BigUint::zero());

        // This is a linear combination that we will enforce to be "zero"
        let mut lc = LinearCombination::zero();

        let mut all_constants = true;

        // Iterate over the operands
        for op in operands {
            // Accumulate the value
            match op.value {
                Some(val) => {
                    result_value
                        .as_mut()
                        .map(|v| *v += BigUint::from(val.to_u128().unwrap()));
                },

                None => {
                    // If any of our operands have unknown value, we won't
                    // know the value of the result
                    result_value = None;
                },
            }

            // Iterate over each bit_gadget of the operand and add the operand to
            // the linear combination
            let mut coeff = F::one();
            for bit in &op.bits {
                match *bit {
                    Boolean::Constant(bit) => {
                        if bit {
                            lc += (coeff, Variable::One);
                        }
                    },
                    _ => {
                        all_constants = false;

                        // Add coeff * bit_gadget
                        lc = lc + (coeff, &bit.lc());
                    },
                }

                coeff.double_in_place();
            }
        }

        // The value of the actual result is modulo 2^$size
        let modular_value = result_value.clone().and_then(|v| {
            let modulus = BigUint::from(1u64) << (N as u32);
            NumCast::from(v % modulus)
        });

        if all_constants && modular_value.is_some() {
            // We can just return a constant, rather than
            // unpacking the result into allocated bits.

            return modular_value
                .map(UInt::constant)
                .ok_or(SynthesisError::AssignmentMissing);
        }
        let cs = operands.cs();

        // Storage area for the resulting bits
        let mut result_bits = vec![];

        // Allocate each bit_gadget of the result
        let mut coeff = F::one();
        let mut i = 0;
        while max_value != T::zero() {
            // Allocate the bit_gadget
            let b = AllocatedBool::new_witness(cs.clone(), || {
                result_value
                    .clone()
                    .map(|v| (v >> i) & BigUint::one() == BigUint::one())
                    .get()
            })?;

            // Subtract this bit_gadget from the linear combination to ensure the sums
            // balance out
            lc = lc - (coeff, b.variable());

            result_bits.push(b.into());

            max_value = max_value >> 1;
            i += 1;
            coeff.double_in_place();
        }

        // Enforce that the linear combination equals zero
        cs.enforce_constraint(lc!(), lc!(), lc)?;

        // Discard carry bits that we don't care about
        result_bits.truncate(N);
        let bits = TryFrom::try_from(result_bits).unwrap();

        Ok(UInt {
            bits,
            value: modular_value,
        })
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

//     #[test]
//     fn test_add_many() -> Result<(), SynthesisError> {
//         let mut rng = ark_std::test_rng();

//         for _ in 0..1000 {
//             let cs = ConstraintSystem::<Fr>::new_ref();

//             let a: $native = rng.gen();
//             let b: $native = rng.gen();
//             let c: $native = rng.gen();
//             let d: $native = rng.gen();

//             let mut expected = (a ^ b).wrapping_add(c).wrapping_add(d);

//             let a_bit = $name::new_witness(ark_relations::ns!(cs, "a_bit"), || Ok(a))?;
//             let b_bit = $name::constant(b);
//             let c_bit = $name::constant(c);
//             let d_bit = $name::new_witness(ark_relations::ns!(cs, "d_bit"), || Ok(d))?;

//             let r = a_bit.xor(&b_bit).unwrap();
//             let r = $name::add_many(&[r, c_bit, d_bit]).unwrap();

//             assert!(cs.is_satisfied().unwrap());
//             assert!(r.value == Some(expected));

//             for b in r.bits.iter() {
//                 match b {
//                     Boolean::Is(b) => assert_eq!(b.value()?, (expected & 1 == 1)),
//                     Boolean::Not(b) => assert_eq!(!b.value()?, (expected & 1 == 1)),
//                     Boolean::Constant(_) => unreachable!(),
//                 }

//                 expected >>= 1;
//             }
//         }
//         Ok(())
//     }

//     #[test]
//     fn test_rotr() -> Result<(), SynthesisError> {
//         let mut rng = ark_std::test_rng();

//         let mut num = rng.gen();

//         let a: $name<Fr> = $name::constant(num);

//         for i in 0..$size {
//             let b = a.rotr(i);

//             assert!(b.value.unwrap() == num);

//             let mut tmp = num;
//             for b in &b.bits {
//                 match b {
//                     Boolean::Constant(b) => assert_eq!(*b, tmp & 1 == 1),
//                     _ => unreachable!(),
//                 }

//                 tmp >>= 1;
//             }

//             num = num.rotate_right(1);
//         }
//         Ok(())
//     }
// }
