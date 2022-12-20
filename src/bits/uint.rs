macro_rules! make_uint {
    ($name:ident, $size:expr, $native:ident, $mod_name:ident, $r1cs_doc_name:expr, $native_doc_name:expr, $num_bits_doc:expr) => {
        #[doc = "This module contains the "]
        #[doc = $r1cs_doc_name]
        #[doc = "type, which is the R1CS equivalent of the "]
        #[doc = $native_doc_name]
        #[doc = " type."]
        pub mod $mod_name {
            use ark_ff::{Field, One, PrimeField, Zero};
            use core::{borrow::Borrow, convert::TryFrom};
            use num_bigint::BigUint;
            use num_traits::cast::ToPrimitive;

            use ark_relations::r1cs::{
                ConstraintSystemRef, LinearCombination, Namespace, SynthesisError, Variable,
            };

            use crate::{
                boolean::{AllocatedBool, Boolean},
                prelude::*,
                Assignment, Vec,
            };

            #[doc = "This struct represent an unsigned"]
            #[doc = $num_bits_doc]
            #[doc = " bit integer as a sequence of "]
            #[doc = $num_bits_doc]
            #[doc = " `Boolean`s. \n"]
            #[doc = "This is the R1CS equivalent of the native "]
            #[doc = $native_doc_name]
            #[doc = " unsigned integer type."]
            #[derive(Clone, Debug)]
            pub struct $name<F: Field> {
                // Least significant bit first
                bits: [Boolean<F>; $size],
                value: Option<$native>,
            }

            impl<F: Field> R1CSVar<F> for $name<F> {
                type Value = $native;

                fn cs(&self) -> ConstraintSystemRef<F> {
                    self.bits.as_ref().cs()
                }

                fn value(&self) -> Result<Self::Value, SynthesisError> {
                    let mut value = None;
                    for (i, bit) in self.bits.iter().enumerate() {
                        let b = $native::from(bit.value()?);
                        value = match value {
                            Some(value) => Some(value + (b << i)),
                            None => Some(b << i),
                        };
                    }
                    debug_assert_eq!(self.value, value);
                    value.get()
                }
            }

            impl<F: Field> $name<F> {
                #[doc = "Construct a constant "]
                #[doc = $r1cs_doc_name]
                #[doc = " from the native "]
                #[doc = $native_doc_name]
                #[doc = " type."]
                pub fn constant(value: $native) -> Self {
                    let mut bits = [Boolean::FALSE; $size];

                    let mut tmp = value;
                    for i in 0..$size {
                        bits[i] = Boolean::constant((tmp & 1) == 1);
                        tmp >>= 1;
                    }

                    $name {
                        bits,
                        value: Some(value),
                    }
                }

                /// Turns `self` into the underlying little-endian bits.
                pub fn to_bits_le(&self) -> Vec<Boolean<F>> {
                    self.bits.to_vec()
                }

                /// Construct `Self` from a slice of `Boolean`s.
                ///
                /// # Panics
                #[doc = "This method panics if `bits.len() != "]
                #[doc = $num_bits_doc]
                #[doc = "`."]
                pub fn from_bits_le(bits: &[Boolean<F>]) -> Self {
                    assert_eq!(bits.len(), $size);

                    let bits = <&[Boolean<F>; $size]>::try_from(bits).unwrap().clone();

                    let mut value = Some(0);
                    for b in bits.iter().rev() {
                        value.as_mut().map(|v| *v <<= 1);

                        match *b {
                            Boolean::Constant(b) => {
                                value.as_mut().map(|v| *v |= $native::from(b));
                            },
                            Boolean::Is(ref b) => match b.value() {
                                Ok(b) => {
                                    value.as_mut().map(|v| *v |= $native::from(b));
                                },
                                Err(_) => value = None,
                            },
                            Boolean::Not(ref b) => match b.value() {
                                Ok(b) => {
                                    value.as_mut().map(|v| *v |= $native::from(!b));
                                },
                                Err(_) => value = None,
                            },
                        }
                    }

                    Self { value, bits }
                }

                /// Rotates `self` to the right by `by` steps, wrapping around.
                #[tracing::instrument(target = "r1cs", skip(self))]
                pub fn rotr(&self, by: usize) -> Self {
                    let mut result = self.clone();
                    let by = by % $size;

                    let new_bits = self.bits.iter().skip(by).chain(&self.bits).take($size);

                    for (res, new) in result.bits.iter_mut().zip(new_bits) {
                        *res = new.clone();
                    }

                    result.value = self
                        .value
                        .map(|v| v.rotate_right(u32::try_from(by).unwrap()));
                    result
                }

                /// Outputs `self ^ other`.
                ///
                /// If at least one of `self` and `other` are constants, then this
                /// method *does not* create any constraints or variables.
                #[tracing::instrument(target = "r1cs", skip(self, other))]
                pub fn xor(&self, other: &Self) -> Result<Self, SynthesisError> {
                    let mut result = self.clone();
                    result.value = match (self.value, other.value) {
                        (Some(a), Some(b)) => Some(a ^ b),
                        _ => None,
                    };

                    let new_bits = self.bits.iter().zip(&other.bits).map(|(a, b)| a.xor(b));

                    for (res, new) in result.bits.iter_mut().zip(new_bits) {
                        *res = new?;
                    }

                    Ok(result)
                }

                /// Perform modular addition of `operands`.
                ///
                /// The user must ensure that overflow does not occur.
                #[tracing::instrument(target = "r1cs", skip(operands))]
                pub fn addmany(operands: &[Self]) -> Result<Self, SynthesisError>
                where
                    F: PrimeField,
                {
                    // Make some arbitrary bounds for ourselves to avoid overflows
                    // in the scalar field
                    assert!(F::MODULUS_BIT_SIZE >= 2 * $size);

                    // Support up to 128
                    assert!($size <= 128);

                    assert!(operands.len() >= 1);
                    assert!($size * operands.len() <= F::MODULUS_BIT_SIZE as usize);

                    if operands.len() == 1 {
                        return Ok(operands[0].clone());
                    }

                    // Compute the maximum value of the sum so we allocate enough bits for
                    // the result
                    let mut max_value =
                        BigUint::from($native::max_value()) * BigUint::from(operands.len());

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
                                result_value.as_mut().map(|v| *v += BigUint::from(val));
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
                                Boolean::Is(ref bit) => {
                                    all_constants = false;

                                    // Add coeff * bit_gadget
                                    lc += (coeff, bit.variable());
                                },
                                Boolean::Not(ref bit) => {
                                    all_constants = false;

                                    // Add coeff * (1 - bit_gadget) = coeff * ONE - coeff *
                                    // bit_gadget
                                    lc = lc + (coeff, Variable::One) - (coeff, bit.variable());
                                },
                                Boolean::Constant(bit) => {
                                    if bit {
                                        lc += (coeff, Variable::One);
                                    }
                                },
                            }

                            coeff.double_in_place();
                        }
                    }

                    // The value of the actual result is modulo 2^$size
                    let modular_value = result_value.clone().map(|v| {
                        let modulus = BigUint::from(1u64) << ($size as u32);
                        (v % modulus).to_u128().unwrap() as $native
                    });

                    if all_constants && modular_value.is_some() {
                        // We can just return a constant, rather than
                        // unpacking the result into allocated bits.

                        return Ok($name::constant(modular_value.unwrap()));
                    }
                    let cs = operands.cs();

                    // Storage area for the resulting bits
                    let mut result_bits = vec![];

                    // Allocate each bit_gadget of the result
                    let mut coeff = F::one();
                    let mut i = 0;
                    while max_value != BigUint::zero() {
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

                        max_value >>= 1;
                        i += 1;
                        coeff.double_in_place();
                    }

                    // Enforce that the linear combination equals zero
                    cs.enforce_constraint(lc!(), lc!(), lc)?;

                    // Discard carry bits that we don't care about
                    result_bits.truncate($size);
                    let bits = TryFrom::try_from(result_bits).unwrap();

                    Ok($name {
                        bits,
                        value: modular_value,
                    })
                }
            }

            impl<ConstraintF: Field> ToBytesGadget<ConstraintF> for $name<ConstraintF> {
                #[tracing::instrument(target = "r1cs", skip(self))]
                fn to_bytes(&self) -> Result<Vec<UInt8<ConstraintF>>, SynthesisError> {
                    Ok(self
                        .to_bits_le()
                        .chunks(8)
                        .map(UInt8::from_bits_le)
                        .collect())
                }
            }

            impl<ConstraintF: Field> EqGadget<ConstraintF> for $name<ConstraintF> {
                #[tracing::instrument(target = "r1cs", skip(self))]
                fn is_eq(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError> {
                    self.bits.as_ref().is_eq(&other.bits)
                }

                #[tracing::instrument(target = "r1cs", skip(self))]
                fn conditional_enforce_equal(
                    &self,
                    other: &Self,
                    condition: &Boolean<ConstraintF>,
                ) -> Result<(), SynthesisError> {
                    self.bits.conditional_enforce_equal(&other.bits, condition)
                }

                #[tracing::instrument(target = "r1cs", skip(self))]
                fn conditional_enforce_not_equal(
                    &self,
                    other: &Self,
                    condition: &Boolean<ConstraintF>,
                ) -> Result<(), SynthesisError> {
                    self.bits
                        .conditional_enforce_not_equal(&other.bits, condition)
                }
            }

            impl<ConstraintF: Field> CondSelectGadget<ConstraintF> for $name<ConstraintF> {
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
                    let mut bits = [Boolean::FALSE; $size];
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

            impl<ConstraintF: Field> AllocVar<$native, ConstraintF> for $name<ConstraintF> {
                fn new_variable<T: Borrow<$native>>(
                    cs: impl Into<Namespace<ConstraintF>>,
                    f: impl FnOnce() -> Result<T, SynthesisError>,
                    mode: AllocationMode,
                ) -> Result<Self, SynthesisError> {
                    let ns = cs.into();
                    let cs = ns.cs();
                    let value = f().map(|f| *f.borrow()).ok();

                    let mut values = [None; $size];
                    if let Some(val) = value {
                        values
                            .iter_mut()
                            .enumerate()
                            .for_each(|(i, v)| *v = Some((val >> i) & 1 == 1));
                    }

                    let mut bits = [Boolean::FALSE; $size];
                    for (b, v) in bits.iter_mut().zip(&values) {
                        *b = Boolean::new_variable(cs.clone(), || v.get(), mode)?;
                    }
                    Ok(Self { bits, value })
                }
            }

            #[cfg(test)]
            mod test {
                use super::$name;
                use crate::{bits::boolean::Boolean, prelude::*, Vec};
                use ark_relations::r1cs::{ConstraintSystem, SynthesisError};
                use ark_std::rand::Rng;
                use ark_test_curves::mnt4_753::Fr;

                #[test]
                fn test_from_bits() -> Result<(), SynthesisError> {
                    let mut rng = ark_std::test_rng();

                    for _ in 0..1000 {
                        let v = (0..$size)
                            .map(|_| Boolean::constant(rng.gen()))
                            .collect::<Vec<Boolean<Fr>>>();

                        let b = $name::from_bits_le(&v);

                        for (i, bit) in b.bits.iter().enumerate() {
                            match bit {
                                &Boolean::Constant(bit) => {
                                    assert_eq!(bit, ((b.value()? >> i) & 1 == 1));
                                },
                                _ => unreachable!(),
                            }
                        }

                        let expected_to_be_same = b.to_bits_le();

                        for x in v.iter().zip(expected_to_be_same.iter()) {
                            match x {
                                (&Boolean::Constant(true), &Boolean::Constant(true)) => {},
                                (&Boolean::Constant(false), &Boolean::Constant(false)) => {},
                                _ => unreachable!(),
                            }
                        }
                    }
                    Ok(())
                }

                #[test]
                fn test_xor() -> Result<(), SynthesisError> {
                    use Boolean::*;
                    let mut rng = ark_std::test_rng();

                    for _ in 0..1000 {
                        let cs = ConstraintSystem::<Fr>::new_ref();

                        let a: $native = rng.gen();
                        let b: $native = rng.gen();
                        let c: $native = rng.gen();

                        let mut expected = a ^ b ^ c;

                        let a_bit = $name::new_witness(cs.clone(), || Ok(a))?;
                        let b_bit = $name::constant(b);
                        let c_bit = $name::new_witness(cs.clone(), || Ok(c))?;

                        let r = a_bit.xor(&b_bit).unwrap();
                        let r = r.xor(&c_bit).unwrap();

                        assert!(cs.is_satisfied().unwrap());

                        assert!(r.value == Some(expected));

                        for b in r.bits.iter() {
                            match b {
                                Is(b) => assert_eq!(b.value()?, (expected & 1 == 1)),
                                Not(b) => assert_eq!(!b.value()?, (expected & 1 == 1)),
                                Constant(b) => assert_eq!(*b, (expected & 1 == 1)),
                            }

                            expected >>= 1;
                        }
                    }
                    Ok(())
                }

                #[test]
                fn test_addmany_constants() -> Result<(), SynthesisError> {
                    let mut rng = ark_std::test_rng();

                    for _ in 0..1000 {
                        let cs = ConstraintSystem::<Fr>::new_ref();

                        let a: $native = rng.gen();
                        let b: $native = rng.gen();
                        let c: $native = rng.gen();

                        let a_bit = $name::new_constant(cs.clone(), a)?;
                        let b_bit = $name::new_constant(cs.clone(), b)?;
                        let c_bit = $name::new_constant(cs.clone(), c)?;

                        let mut expected = a.wrapping_add(b).wrapping_add(c);

                        let r = $name::addmany(&[a_bit, b_bit, c_bit]).unwrap();

                        assert!(r.value == Some(expected));

                        for b in r.bits.iter() {
                            match b {
                                Boolean::Is(_) => unreachable!(),
                                Boolean::Not(_) => unreachable!(),
                                Boolean::Constant(b) => assert_eq!(*b, (expected & 1 == 1)),
                            }

                            expected >>= 1;
                        }
                    }
                    Ok(())
                }

                #[test]
                fn test_addmany() -> Result<(), SynthesisError> {
                    let mut rng = ark_std::test_rng();

                    for _ in 0..1000 {
                        let cs = ConstraintSystem::<Fr>::new_ref();

                        let a: $native = rng.gen();
                        let b: $native = rng.gen();
                        let c: $native = rng.gen();
                        let d: $native = rng.gen();

                        let mut expected = (a ^ b).wrapping_add(c).wrapping_add(d);

                        let a_bit = $name::new_witness(ark_relations::ns!(cs, "a_bit"), || Ok(a))?;
                        let b_bit = $name::constant(b);
                        let c_bit = $name::constant(c);
                        let d_bit = $name::new_witness(ark_relations::ns!(cs, "d_bit"), || Ok(d))?;

                        let r = a_bit.xor(&b_bit).unwrap();
                        let r = $name::addmany(&[r, c_bit, d_bit]).unwrap();

                        assert!(cs.is_satisfied().unwrap());
                        assert!(r.value == Some(expected));

                        for b in r.bits.iter() {
                            match b {
                                Boolean::Is(b) => assert_eq!(b.value()?, (expected & 1 == 1)),
                                Boolean::Not(b) => assert_eq!(!b.value()?, (expected & 1 == 1)),
                                Boolean::Constant(_) => unreachable!(),
                            }

                            expected >>= 1;
                        }
                    }
                    Ok(())
                }

                #[test]
                fn test_rotr() -> Result<(), SynthesisError> {
                    let mut rng = ark_std::test_rng();

                    let mut num = rng.gen();

                    let a: $name<Fr> = $name::constant(num);

                    for i in 0..$size {
                        let b = a.rotr(i);

                        assert!(b.value.unwrap() == num);

                        let mut tmp = num;
                        for b in &b.bits {
                            match b {
                                Boolean::Constant(b) => assert_eq!(*b, tmp & 1 == 1),
                                _ => unreachable!(),
                            }

                            tmp >>= 1;
                        }

                        num = num.rotate_right(1);
                    }
                    Ok(())
                }
            }
        }
    };
}
