use crate::convert::*;
use crate::fields::fp::FpVar;

use super::*;

impl<const N: usize, F: Field, T: PrimUInt> UInt<N, T, F> {
    /// Converts `self` into a field element. The elements comprising `self` are
    /// interpreted as a little-endian bit order representation of a field element.
    ///
    /// # Panics
    /// Assumes that `N` is equal to at most the number of bits in `F::MODULUS_BIT_SIZE - 1`, and panics otherwise.
    pub fn to_fp(&self) -> Result<FpVar<F>, SynthesisError>
    where
        F: PrimeField,
    {
        assert!(N <= F::MODULUS_BIT_SIZE as usize - 1);

        Boolean::le_bits_to_fp(&self.bits)
    }

    /// Converts a field element into its little-endian bit order representation.
    ///
    /// # Panics
    ///
    /// Assumes that `N` is at most the number of bits in `F::MODULUS_BIT_SIZE - 1`, and panics otherwise.
    pub fn from_fp(other: &FpVar<F>) -> Result<(Self, FpVar<F>), SynthesisError>
    where
        F: PrimeField,
    {
        let (bits, rest) = other.to_bits_le_with_top_bits_zero(N)?;
        let result = Self::from_bits_le(&bits);
        Ok((result, rest))
    }

    /// Converts a little-endian byte order representation of bits into a
    /// `UInt`.
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
        assert_eq!(bits.len(), N);
        let bits = <&[Boolean<F>; N]>::try_from(bits).unwrap().clone();
        let value_exists = bits.iter().all(|b| b.value().is_ok());
        let mut value = T::zero();
        for (i, b) in bits.iter().enumerate() {
            if let Ok(b) = b.value() {
                value = value + (T::from(b as u8).unwrap() << i);
            }
        }
        let value = value_exists.then_some(value);
        Self { bits, value }
    }

    /// Converts a big-endian list of bytes into a `UInt`.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let var = UInt16::new_witness(cs.clone(), || Ok(2 * (u8::MAX as u16)))?;
    ///
    /// // Construct u8::MAX * 2
    /// let bytes = UInt8::constant_vec(&(2 * (u8::MAX as u16)).to_be_bytes());
    ///
    /// let c = UInt16::from_bytes_be(&bytes)?;
    /// var.enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_bytes_be(bytes: &[UInt8<F>]) -> Result<Self, SynthesisError> {
        let bits = bytes
            .iter()
            .rev()
            .flat_map(|b| b.to_bits_le().unwrap())
            .collect::<Vec<_>>();
        Ok(Self::from_bits_le(&bits))
    }

    /// Converts a little-endian byte order list of bytes into a `UInt`.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let var = UInt16::new_witness(cs.clone(), || Ok(2 * (u8::MAX as u16)))?;
    ///
    /// // Construct u8::MAX * 2
    /// let bytes = UInt8::constant_vec(&(2 * (u8::MAX as u16)).to_le_bytes());
    ///
    /// let c = UInt16::from_bytes_le(&bytes)?;
    /// var.enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_bytes_le(bytes: &[UInt8<F>]) -> Result<Self, SynthesisError> {
        let bits = bytes
            .iter()
            .flat_map(|b| b.to_bits_le().unwrap())
            .collect::<Vec<_>>();
        Ok(Self::from_bits_le(&bits))
    }

    pub fn to_bytes_be(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let mut bytes = self.to_bytes_le()?;
        bytes.reverse();
        Ok(bytes)
    }
}

impl<const N: usize, T: PrimUInt, F: Field> ToBitsGadget<F> for UInt<N, T, F> {
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        Ok(self.bits.to_vec())
    }
}

impl<const N: usize, T: PrimUInt, F: Field> ToBitsGadget<F> for [UInt<N, T, F>] {
    /// Interprets `self` as an integer, and outputs the little-endian
    /// bit-wise decomposition of that integer.
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let bits = self.iter().flat_map(|b| &b.bits).cloned().collect();
        Ok(bits)
    }
}

/*****************************************************************************************/
/********************************* Conversions to bytes. *********************************/
/*****************************************************************************************/

impl<const N: usize, T: PrimUInt, ConstraintF: Field> ToBytesGadget<ConstraintF>
    for UInt<N, T, ConstraintF>
{
    #[tracing::instrument(target = "r1cs", skip(self))]
    fn to_bytes_le(&self) -> Result<Vec<UInt8<ConstraintF>>, SynthesisError> {
        Ok(self
            .to_bits_le()?
            .chunks(8)
            .map(UInt8::from_bits_le)
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        prelude::EqGadget,
        uint::test_utils::{run_unary_exhaustive, run_unary_random},
        R1CSVar,
    };
    use ark_ff::PrimeField;
    use ark_test_curves::bls12_381::Fr;

    fn uint_to_bytes_le<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs();
        let computed = a.to_bytes_le()?;
        let expected = UInt8::constant_vec(a.value()?.to_le_bytes().as_ref());
        assert_eq!(expected.len(), computed.len());
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !a.is_constant() {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    fn uint_to_bytes_be<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs();
        let computed = a.to_bytes_be()?;
        let expected = UInt8::constant_vec(a.value()?.to_be_bytes().as_ref());
        assert_eq!(expected.len(), computed.len());
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !a.is_constant() {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    fn uint_from_bytes_le<T: PrimUInt, const N: usize, F: PrimeField>(
        expected: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = expected.cs();
        let mode = if expected.is_constant() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let computed = {
            let value = expected.value()?.to_le_bytes();
            let a = Vec::<UInt8<F>>::new_variable(cs.clone(), || Ok(value.as_ref()), mode)?;
            UInt::from_bytes_le(&a)?
        };
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !expected.is_constant() {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    fn uint_from_bytes_be<T: PrimUInt, const N: usize, F: PrimeField>(
        expected: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = expected.cs();
        let mode = if expected.is_constant() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let computed = {
            let value = expected.value()?.to_be_bytes();
            let a = Vec::<UInt8<F>>::new_variable(cs.clone(), || Ok(value.as_ref()), mode)?;
            UInt::from_bytes_be(&a)?
        };
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !expected.is_constant() {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    #[test]
    fn u8_to_bytes_le() {
        run_unary_exhaustive(uint_to_bytes_le::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_to_bytes_le() {
        run_unary_random::<1000, 16, _, _>(uint_to_bytes_le::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_to_bytes_le() {
        run_unary_random::<1000, 32, _, _>(uint_to_bytes_le::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_to_bytes_le() {
        run_unary_random::<1000, 64, _, _>(uint_to_bytes_le::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_to_bytes_le() {
        run_unary_random::<1000, 128, _, _>(uint_to_bytes_le::<u128, 128, Fr>).unwrap()
    }

    #[test]
    fn u8_to_bytes_be() {
        run_unary_exhaustive(uint_to_bytes_be::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_to_bytes_be() {
        run_unary_random::<1000, 16, _, _>(uint_to_bytes_be::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_to_bytes_be() {
        run_unary_random::<1000, 32, _, _>(uint_to_bytes_be::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_to_bytes_be() {
        run_unary_random::<1000, 64, _, _>(uint_to_bytes_be::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_to_bytes_be() {
        run_unary_random::<1000, 128, _, _>(uint_to_bytes_be::<u128, 128, Fr>).unwrap()
    }

    #[test]
    fn u8_from_bytes_le() {
        run_unary_exhaustive(uint_from_bytes_le::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_from_bytes_le() {
        run_unary_random::<1000, 16, _, _>(uint_from_bytes_le::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_from_bytes_le() {
        run_unary_random::<1000, 32, _, _>(uint_from_bytes_le::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_from_bytes_le() {
        run_unary_random::<1000, 64, _, _>(uint_from_bytes_le::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_from_bytes_le() {
        run_unary_random::<1000, 128, _, _>(uint_from_bytes_le::<u128, 128, Fr>).unwrap()
    }

    #[test]
    fn u8_from_bytes_be() {
        run_unary_exhaustive(uint_from_bytes_be::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_from_bytes_be() {
        run_unary_random::<1000, 16, _, _>(uint_from_bytes_be::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_from_bytes_be() {
        run_unary_random::<1000, 32, _, _>(uint_from_bytes_be::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_from_bytes_be() {
        run_unary_random::<1000, 64, _, _>(uint_from_bytes_be::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_from_bytes_be() {
        run_unary_random::<1000, 128, _, _>(uint_from_bytes_be::<u128, 128, Fr>).unwrap()
    }
}
