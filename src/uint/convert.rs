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
    fn to_bytes(&self) -> Result<Vec<UInt8<ConstraintF>>, SynthesisError> {
        Ok(self
            .to_bits_le()?
            .chunks(8)
            .map(UInt8::from_bits_le)
            .collect())
    }
}

impl<const N: usize, T: PrimUInt, F: Field> ToBytesGadget<F> for [UInt<N, T, F>] {
    fn to_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let mut bytes = Vec::with_capacity(self.len() * (N / 8));
        for elem in self {
            bytes.extend_from_slice(&elem.to_bytes()?);
        }
        Ok(bytes)
    }
}

impl<const N: usize, T: PrimUInt, F: Field> ToBytesGadget<F> for Vec<UInt<N, T, F>> {
    fn to_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        self.as_slice().to_bytes()
    }
}

impl<'a, const N: usize, T: PrimUInt, F: Field> ToBytesGadget<F> for &'a [UInt<N, T, F>] {
    fn to_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        (*self).to_bytes()
    }
}
