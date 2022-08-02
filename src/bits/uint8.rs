use ark_ff::{Field, PrimeField, ToConstraintField};

use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};

use crate::{
    fields::fp::{AllocatedFp, FpVar},
    prelude::*,
    Assignment, ToConstraintFieldGadget, Vec,
};
use core::{borrow::Borrow, convert::TryFrom};

/// Represents an interpretation of 8 `Boolean` objects as an
/// unsigned integer.
#[derive(Clone, Debug)]
pub struct UInt8<F: Field> {
    /// Little-endian representation: least significant bit first
    pub(crate) bits: [Boolean<F>; 8],
    pub(crate) value: Option<u8>,
}

impl<F: Field> R1CSVar<F> for UInt8<F> {
    type Value = u8;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.bits.as_ref().cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let mut value = None;
        for (i, bit) in self.bits.iter().enumerate() {
            let b = u8::from(bit.value()?);
            value = match value {
                Some(value) => Some(value + (b << i)),
                None => Some(b << i),
            };
        }
        debug_assert_eq!(self.value, value);
        value.get()
    }
}

impl<F: Field> UInt8<F> {
    /// Construct a constant vector of `UInt8` from a vector of `u8`
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
    pub fn constant_vec(values: &[u8]) -> Vec<Self> {
        let mut result = Vec::new();
        for value in values {
            result.push(UInt8::constant(*value));
        }
        result
    }

    /// Construct a constant `UInt8` from a `u8`
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
    pub fn constant(value: u8) -> Self {
        let mut bits = [Boolean::FALSE; 8];

        let mut tmp = value;
        for i in 0..8 {
            // If last bit is one, push one.
            bits[i] = Boolean::constant((tmp & 1) == 1);
            tmp >>= 1;
        }

        Self {
            bits,
            value: Some(value),
        }
    }

    /// Allocates a slice of `u8`'s as private witnesses.
    pub fn new_witness_vec(
        cs: impl Into<Namespace<F>>,
        values: &[impl Into<Option<u8>> + Copy],
    ) -> Result<Vec<Self>, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let mut output_vec = Vec::with_capacity(values.len());
        for value in values {
            let byte: Option<u8> = Into::into(*value);
            output_vec.push(Self::new_witness(cs.clone(), || byte.get())?);
        }
        Ok(output_vec)
    }

    /// Allocates a slice of `u8`'s as public inputs by first packing them into
    /// elements of `F`, (thus reducing the number of input allocations),
    /// allocating these elements as public inputs, and then converting
    /// these field variables `FpVar<F>` variables back into bytes.
    ///
    /// From a user perspective, this trade-off adds constraints, but improves
    /// verifier time and verification key size.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let two = UInt8::new_witness(cs.clone(), || Ok(2))?;
    /// let var = vec![two.clone(); 32];
    ///
    /// let c = UInt8::new_input_vec(cs.clone(), &[2; 32])?;
    /// var.enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    pub fn new_input_vec(
        cs: impl Into<Namespace<F>>,
        values: &[u8],
    ) -> Result<Vec<Self>, SynthesisError>
    where
        F: PrimeField,
    {
        let ns = cs.into();
        let cs = ns.cs();
        let values_len = values.len();
        let field_elements: Vec<F> = ToConstraintField::<F>::to_field_elements(values).unwrap();

        let max_size = 8 * ((F::MODULUS_BIT_SIZE - 1) / 8) as usize;
        let mut allocated_bits = Vec::new();
        for field_element in field_elements.into_iter() {
            let fe = AllocatedFp::new_input(cs.clone(), || Ok(field_element))?;
            let fe_bits = fe.to_bits_le()?;

            // Remove the most significant bit, because we know it should be zero
            // because `values.to_field_elements()` only
            // packs field elements up to the penultimate bit.
            // That is, the most significant bit (`ConstraintF::NUM_BITS`-th bit) is
            // unset, so we can just pop it off.
            allocated_bits.extend_from_slice(&fe_bits[0..max_size]);
        }

        // Chunk up slices of 8 bit into bytes.
        Ok(allocated_bits[0..(8 * values_len)]
            .chunks(8)
            .map(Self::from_bits_le)
            .collect())
    }

    /// Converts a little-endian byte order representation of bits into a
    /// `UInt8`.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let var = UInt8::new_witness(cs.clone(), || Ok(128))?;
    ///
    /// let f = Boolean::FALSE;
    /// let t = Boolean::TRUE;
    ///
    /// // Construct [0, 0, 0, 0, 0, 0, 0, 1]
    /// let mut bits = vec![f.clone(); 7];
    /// bits.push(t);
    ///
    /// let mut c = UInt8::from_bits_le(&bits);
    /// var.enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs")]
    pub fn from_bits_le(bits: &[Boolean<F>]) -> Self {
        assert_eq!(bits.len(), 8);
        let bits = <&[Boolean<F>; 8]>::try_from(bits).unwrap().clone();

        let mut value = Some(0u8);
        for (i, b) in bits.iter().enumerate() {
            value = match b.value().ok() {
                Some(b) => value.map(|v| v + (u8::from(b) << i)),
                None => None,
            }
        }

        Self { value, bits }
    }

    /// Outputs `self ^ other`.
    ///
    /// If at least one of `self` and `other` are constants, then this method
    /// *does not* create any constraints or variables.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let a = UInt8::new_witness(cs.clone(), || Ok(16))?;
    /// let b = UInt8::new_witness(cs.clone(), || Ok(17))?;
    /// let c = UInt8::new_witness(cs.clone(), || Ok(1))?;
    ///
    /// a.xor(&b)?.enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs")]
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
}

impl<ConstraintF: Field> EqGadget<ConstraintF> for UInt8<ConstraintF> {
    #[tracing::instrument(target = "r1cs")]
    fn is_eq(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        self.bits.as_ref().is_eq(&other.bits)
    }

    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        self.bits.conditional_enforce_equal(&other.bits, condition)
    }

    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        condition: &Boolean<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        self.bits
            .conditional_enforce_not_equal(&other.bits, condition)
    }
}

impl<ConstraintF: Field> CondSelectGadget<ConstraintF> for UInt8<ConstraintF> {
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
        let mut bits = [Boolean::FALSE; 8];
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

impl<ConstraintF: Field> AllocVar<u8, ConstraintF> for UInt8<ConstraintF> {
    fn new_variable<T: Borrow<u8>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let value = f().map(|f| *f.borrow()).ok();

        let mut values = [None; 8];
        if let Some(val) = value {
            values
                .iter_mut()
                .enumerate()
                .for_each(|(i, v)| *v = Some((val >> i) & 1 == 1));
        }

        let mut bits = [Boolean::FALSE; 8];
        for (b, v) in bits.iter_mut().zip(&values) {
            *b = Boolean::new_variable(cs.clone(), || v.get(), mode)?;
        }
        Ok(Self { bits, value })
    }
}

/// Parses the `Vec<UInt8<ConstraintF>>` in fixed-sized
/// `ConstraintF::MODULUS_BIT_SIZE - 1` chunks and converts each chunk, which is
/// assumed to be little-endian, to its `FpVar<ConstraintF>` representation.
/// This is the gadget counterpart to the `[u8]` implementation of
/// [ToConstraintField](ark_ff::ToConstraintField).
impl<ConstraintF: PrimeField> ToConstraintFieldGadget<ConstraintF> for [UInt8<ConstraintF>] {
    #[tracing::instrument(target = "r1cs")]
    fn to_constraint_field(&self) -> Result<Vec<FpVar<ConstraintF>>, SynthesisError> {
        let max_size = ((ConstraintF::MODULUS_BIT_SIZE - 1) / 8) as usize;
        self.chunks(max_size)
            .map(|chunk| Boolean::le_bits_to_fp_var(chunk.to_bits_le()?.as_slice()))
            .collect::<Result<Vec<_>, SynthesisError>>()
    }
}

impl<ConstraintF: PrimeField> ToConstraintFieldGadget<ConstraintF> for Vec<UInt8<ConstraintF>> {
    #[tracing::instrument(target = "r1cs")]
    fn to_constraint_field(&self) -> Result<Vec<FpVar<ConstraintF>>, SynthesisError> {
        self.as_slice().to_constraint_field()
    }
}

#[cfg(test)]
mod test {
    use super::UInt8;
    use crate::{
        fields::fp::FpVar,
        prelude::{
            AllocationMode::{Constant, Input, Witness},
            *,
        },
        ToConstraintFieldGadget, Vec,
    };
    use ark_ff::{PrimeField, ToConstraintField};
    use ark_relations::r1cs::{ConstraintSystem, SynthesisError};
    use ark_std::rand::{distributions::Uniform, Rng};
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn test_uint8_from_bits_to_bits() -> Result<(), SynthesisError> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let byte_val = 0b01110001;
        let byte =
            UInt8::new_witness(ark_relations::ns!(cs, "alloc value"), || Ok(byte_val)).unwrap();
        let bits = byte.to_bits_le()?;
        for (i, bit) in bits.iter().enumerate() {
            assert_eq!(bit.value()?, (byte_val >> i) & 1 == 1)
        }
        Ok(())
    }

    #[test]
    fn test_uint8_new_input_vec() -> Result<(), SynthesisError> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let byte_vals = (64u8..128u8).collect::<Vec<_>>();
        let bytes =
            UInt8::new_input_vec(ark_relations::ns!(cs, "alloc value"), &byte_vals).unwrap();
        dbg!(bytes.value())?;
        for (native, variable) in byte_vals.into_iter().zip(bytes) {
            let bits = variable.to_bits_le()?;
            for (i, bit) in bits.iter().enumerate() {
                assert_eq!(
                    bit.value()?,
                    (native >> i) & 1 == 1,
                    "native value {}: bit {:?}",
                    native,
                    i
                )
            }
        }
        Ok(())
    }

    #[test]
    fn test_uint8_from_bits() -> Result<(), SynthesisError> {
        let mut rng = ark_std::test_rng();

        for _ in 0..1000 {
            let v = (0..8)
                .map(|_| Boolean::<Fr>::Constant(rng.gen()))
                .collect::<Vec<_>>();

            let val = UInt8::from_bits_le(&v);

            for (i, bit) in val.bits.iter().enumerate() {
                match bit {
                    Boolean::Constant(b) => assert!(*b == ((val.value()? >> i) & 1 == 1)),
                    _ => unreachable!(),
                }
            }

            let expected_to_be_same = val.to_bits_le()?;

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
    fn test_uint8_xor() -> Result<(), SynthesisError> {
        let mut rng = ark_std::test_rng();

        for _ in 0..1000 {
            let cs = ConstraintSystem::<Fr>::new_ref();

            let a: u8 = rng.gen();
            let b: u8 = rng.gen();
            let c: u8 = rng.gen();

            let mut expected = a ^ b ^ c;

            let a_bit = UInt8::new_witness(ark_relations::ns!(cs, "a_bit"), || Ok(a)).unwrap();
            let b_bit = UInt8::constant(b);
            let c_bit = UInt8::new_witness(ark_relations::ns!(cs, "c_bit"), || Ok(c)).unwrap();

            let r = a_bit.xor(&b_bit).unwrap();
            let r = r.xor(&c_bit).unwrap();

            assert!(cs.is_satisfied().unwrap());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    Boolean::Is(b) => assert!(b.value()? == (expected & 1 == 1)),
                    Boolean::Not(b) => assert!(!b.value()? == (expected & 1 == 1)),
                    Boolean::Constant(b) => assert!(*b == (expected & 1 == 1)),
                }

                expected >>= 1;
            }
        }
        Ok(())
    }

    #[test]
    fn test_uint8_to_constraint_field() -> Result<(), SynthesisError> {
        let mut rng = ark_std::test_rng();
        let max_size = ((<Fr as PrimeField>::MODULUS_BIT_SIZE - 1) / 8) as usize;

        let modes = [Input, Witness, Constant];
        for mode in &modes {
            for _ in 0..1000 {
                let cs = ConstraintSystem::<Fr>::new_ref();

                let bytes: Vec<u8> = (&mut rng)
                    .sample_iter(&Uniform::new_inclusive(0, u8::max_value()))
                    .take(max_size * 3 + 5)
                    .collect();

                let bytes_var = bytes
                    .iter()
                    .map(|byte| UInt8::new_variable(cs.clone(), || Ok(*byte), *mode))
                    .collect::<Result<Vec<_>, SynthesisError>>()?;

                let f_vec: Vec<Fr> = bytes.to_field_elements().unwrap();
                let f_var_vec: Vec<FpVar<Fr>> = bytes_var.to_constraint_field()?;

                assert!(cs.is_satisfied().unwrap());
                assert_eq!(f_vec, f_var_vec.value()?);
            }
        }

        Ok(())
    }

    #[test]
    fn test_uint8_random_access() {
        let mut rng = ark_std::test_rng();

        for _ in 0..100 {
            let cs = ConstraintSystem::<Fr>::new_ref();

            // value array
            let values: Vec<u8> = (0..128).map(|_| rng.gen()).collect();
            let values_const: Vec<UInt8<Fr>> = values.iter().map(|x| UInt8::constant(*x)).collect();

            // index array
            let position: Vec<bool> = (0..7).map(|_| rng.gen()).collect();
            let position_var: Vec<Boolean<Fr>> = position
                .iter()
                .map(|b| {
                    Boolean::new_witness(ark_relations::ns!(cs, "index_arr_element"), || Ok(*b))
                        .unwrap()
                })
                .collect();

            // index
            let mut index = 0;
            for x in position {
                index *= 2;
                index += if x { 1 } else { 0 };
            }

            assert_eq!(
                UInt8::conditionally_select_power_of_two_vector(&position_var, &values_const)
                    .unwrap()
                    .value()
                    .unwrap(),
                values[index]
            )
        }
    }
}
