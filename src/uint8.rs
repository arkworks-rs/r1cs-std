use ark_ff::{Field, PrimeField, ToConstraintField};

use ark_relations::r1cs::{Namespace, SynthesisError};

use crate::{
    convert::{ToBitsGadget, ToConstraintFieldGadget},
    fields::fp::{AllocatedFp, FpVar},
    prelude::*,
    Vec,
};

pub type UInt8<F> = super::uint::UInt<8, u8, F>;

impl<F: Field> UInt8<F> {
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
}

/// Parses the `Vec<UInt8<ConstraintF>>` in fixed-sized
/// `ConstraintF::MODULUS_BIT_SIZE - 1` chunks and converts each chunk, which is
/// assumed to be little-endian, to its `FpVar<ConstraintF>` representation.
/// This is the gadget counterpart to the `[u8]` implementation of
/// [`ToConstraintField``].
impl<ConstraintF: PrimeField> ToConstraintFieldGadget<ConstraintF> for [UInt8<ConstraintF>] {
    #[tracing::instrument(target = "r1cs")]
    fn to_constraint_field(&self) -> Result<Vec<FpVar<ConstraintF>>, SynthesisError> {
        let max_size = ((ConstraintF::MODULUS_BIT_SIZE - 1) / 8) as usize;
        self.chunks(max_size)
            .map(|chunk| Boolean::le_bits_to_fp(chunk.to_bits_le()?.as_slice()))
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
        convert::{ToBitsGadget, ToConstraintFieldGadget},
        fields::fp::FpVar,
        prelude::{
            AllocationMode::{Constant, Input, Witness},
            *,
        },
        Vec,
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

            let value = val.value()?;
            for (i, bit) in val.bits.iter().enumerate() {
                match bit {
                    Boolean::Constant(b) => assert_eq!(*b, ((value >> i) & 1 == 1)),
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

            let mut r = a_bit ^ b_bit;
            r ^= &c_bit;

            assert!(cs.is_satisfied().unwrap());

            assert_eq!(r.value, Some(expected));

            for b in r.bits.iter() {
                match b {
                    Boolean::Var(b) => assert!(b.value()? == (expected & 1 == 1)),
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
