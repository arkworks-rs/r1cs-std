use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use ark_std::{ops::Shr, ops::ShrAssign};

use crate::boolean::Boolean;

use super::{PrimUInt, UInt};

impl<const N: usize, T: PrimUInt, F: PrimeField> UInt<N, T, F> {
    fn _shr_u128(&self, other: u128) -> Result<Self, SynthesisError> {
        if other < N as u128 {
            let mut bits = [Boolean::FALSE; N];
            for (a, b) in bits.iter_mut().zip(&self.bits[other as usize..]) {
                *a = b.clone();
            }

            let value = self.value.and_then(|a| Some(a >> other));
            Ok(Self { bits, value })
        } else {
            panic!("attempt to shift right with overflow")
        }
    }
}

impl<const N: usize, T: PrimUInt, F: PrimeField, T2: PrimUInt> Shr<T2> for UInt<N, T, F> {
    type Output = Self;

    /// Output `self >> other`.
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
    /// let b = 1u8;
    /// let c = UInt8::new_witness(cs.clone(), || Ok(16 >> 1))?;
    ///
    /// (a >> b).enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn shr(self, other: T2) -> Self::Output {
        self._shr_u128(other.into()).unwrap()
    }
}

impl<'a, const N: usize, T: PrimUInt, F: PrimeField, T2: PrimUInt> Shr<T2> for &'a UInt<N, T, F> {
    type Output = UInt<N, T, F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn shr(self, other: T2) -> Self::Output {
        self._shr_u128(other.into()).unwrap()
    }
}

impl<const N: usize, T: PrimUInt, F: PrimeField, T2: PrimUInt> ShrAssign<T2> for UInt<N, T, F> {
    /// Sets `self = self >> other`.
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
    /// let mut a = UInt8::new_witness(cs.clone(), || Ok(16))?;
    /// let b = 1u8;
    /// let c = UInt8::new_witness(cs.clone(), || Ok(16 >> 1))?;
    ///
    /// a >>= b;
    /// a.enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn shr_assign(&mut self, other: T2) {
        let result = self._shr_u128(other.into()).unwrap();
        *self = result;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        alloc::{AllocVar, AllocationMode},
        prelude::EqGadget,
        uint::test_utils::{run_binary_exhaustive_native_only, run_binary_random_native_only},
        R1CSVar,
    };
    use ark_ff::PrimeField;
    use ark_test_curves::bls12_381::Fr;

    fn uint_shr<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
        b: T,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs();
        let b = b.into() % (N as u128);
        let computed = &a >> b;
        let expected_mode = if a.is_constant() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let expected =
            UInt::<N, T, F>::new_variable(cs.clone(), || Ok(a.value()? >> b), expected_mode)?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !a.is_constant() {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    #[test]
    fn u8_shr() {
        run_binary_exhaustive_native_only(uint_shr::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_shr() {
        run_binary_random_native_only::<1000, 16, _, _>(uint_shr::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_shr() {
        run_binary_random_native_only::<1000, 32, _, _>(uint_shr::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_shr() {
        run_binary_random_native_only::<1000, 64, _, _>(uint_shr::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_shr() {
        run_binary_random_native_only::<1000, 128, _, _>(uint_shr::<u128, 128, Fr>).unwrap()
    }
}
