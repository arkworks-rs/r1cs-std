use ark_ff::BigInteger;

use crate::fields::fp::FpVar;

use super::*;

impl<const N: usize, F: Field, T: PrimInt + Debug> UInt<N, T, F> {
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

        Boolean::le_bits_to_fp_var(&self.bits)
    }

    pub(super) fn from_fp_to_parts(other: &FpVar<F>) -> Result<(Self, FpVar<F>), SynthesisError>
    where
        F: PrimeField,
    {
        assert!(N <= F::MODULUS_BIT_SIZE as usize - 1);
        let value = other.value()?.into_bigint().to_bits_le();
        let cs = other.cs();
        let mode = if other.is_constant() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let lower_bits = value
            .iter()
            .take(N)
            .map(|b| Boolean::new_variable(cs.clone(), || Ok(*b), mode))
            .collect::<Result<Vec<_>, _>>()?;
        let result = Self::from_bits_le(&lower_bits);
        let rest: FpVar<F> = other - &result.to_fp()?;
        (result.to_fp()? + &rest).enforce_equal(&other)?;
        Ok((result, rest))
    }

    /// Converts a field element into its little-endian bit order representation.
    ///
    /// # Panics
    ///
    /// Assumes that `N` is equal to at most the number of bits in `F::MODULUS_BIT_SIZE - 1`, and panics otherwise.
    pub fn from_fp(other: &FpVar<F>) -> Result<Self, SynthesisError>
    where
        F: PrimeField,
    {
        let (result, rest) = Self::from_fp_to_parts(other)?;
        rest.enforce_equal(&FpVar::zero())?;
        Ok(result)
    }

    /// Turns `self` into the underlying little-endian bits.
    pub fn to_bits_le(&self) -> Vec<Boolean<F>> {
        self.bits.to_vec()
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

impl<const N: usize, T: PrimInt + Debug, ConstraintF: Field> ToBytesGadget<ConstraintF>
    for UInt<N, T, ConstraintF>
{
    #[tracing::instrument(target = "r1cs", skip(self))]
    fn to_bytes(&self) -> Result<Vec<UInt8<ConstraintF>>, SynthesisError> {
        Ok(self
            .to_bits_le()
            .chunks(8)
            .map(UInt8::from_bits_le)
            .collect())
    }
}
