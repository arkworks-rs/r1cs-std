use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;
use ark_std::{fmt::Debug, ops::BitXor, ops::BitXorAssign};
use num_traits::PrimInt;

use super::UInt;

impl<const N: usize, T: PrimInt + Debug, F: Field> UInt<N, T, F> {
    fn _xor(&self, other: &Self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        for (a, b) in result.bits.iter_mut().zip(&other.bits) {
            *a = a.xor(b)?
        }
        result.value = self.value.and_then(|a| Some(a ^ other.value?));
        dbg!(result.value);
        Ok(result)
    }
}

impl<'a, const N: usize, T: PrimInt + Debug, F: Field> BitXor<Self> for &'a UInt<N, T, F> {
    type Output = UInt<N, T, F>;
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
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitxor(self, other: Self) -> Self::Output {
        self._xor(other).unwrap()
    }
}

impl<'a, const N: usize, T: PrimInt + Debug, F: Field> BitXor<&'a Self> for UInt<N, T, F> {
    type Output = UInt<N, T, F>;
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
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitxor(self, other: &Self) -> Self::Output {
        self._xor(&other).unwrap()
    }
}

impl<'a, const N: usize, T: PrimInt + Debug, F: Field> BitXor<UInt<N, T, F>> for &'a UInt<N, T, F> {
    type Output = UInt<N, T, F>;
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
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitxor(self, other: UInt<N, T, F>) -> Self::Output {
        self._xor(&other).unwrap()
    }
}

impl<const N: usize, T: PrimInt + Debug, F: Field> BitXor<Self> for UInt<N, T, F> {
    type Output = Self;
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
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitxor(self, other: Self) -> Self::Output {
        self._xor(&other).unwrap()
    }
}

impl<const N: usize, T: PrimInt + Debug, F: Field> BitXorAssign<Self> for UInt<N, T, F> {
    /// Sets `self = self ^ other`.
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
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitxor_assign(&mut self, other: Self) {
        let result = self._xor(&other).unwrap();
        *self = result;
    }
}

impl<'a, const N: usize, T: PrimInt + Debug, F: Field> BitXorAssign<&'a Self> for UInt<N, T, F> {
    /// Sets `self = self ^ other`.
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
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitxor_assign(&mut self, other: &'a Self) {
        let result = self._xor(other).unwrap();
        *self = result;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        alloc::AllocVar,
        prelude::EqGadget,
        uint::test_utils::{run_binary_exhaustive, run_binary_random},
        R1CSVar,
    };
    use ark_ff::PrimeField;
    use ark_test_curves::bls12_381::Fr;

    fn uint_xor<T: PrimInt + Debug, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
        b: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs().or(b.cs());
        let computed = a ^ b;
        let expected = UInt::new_witness(ark_relations::ns!(cs, "xor"), || {
            Ok(a.value().unwrap() ^ b.value().unwrap())
        })?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&expected)?;
        assert!(cs.is_satisfied().unwrap());
        Ok(())
    }

    #[test]
    fn u8_xor() {
        run_binary_exhaustive(uint_xor::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_xor() {
        run_binary_random::<1000, 16, _, _>(uint_xor::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_xor() {
        run_binary_random::<1000, 32, _, _>(uint_xor::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_xor() {
        run_binary_random::<1000, 64, _, _>(uint_xor::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128() {
        run_binary_random::<1000, 128, _, _>(uint_xor::<u128, 128, Fr>).unwrap()
    }
}
