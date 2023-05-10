use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;
use ark_std::{fmt::Debug, ops::BitAnd, ops::BitAndAssign};
use num_traits::PrimInt;

use super::UInt;

impl<const N: usize, T: PrimInt + Debug, F: Field> UInt<N, T, F> {
    fn _and(&self, other: &Self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        for (a, b) in result.bits.iter_mut().zip(&other.bits) {
            *a = a.and(b)?
        }
        result.value = self.value.and_then(|a| Some(a & other.value?));
        dbg!(result.value);
        Ok(result)
    }
}

impl<'a, const N: usize, T: PrimInt + Debug, F: Field> BitAnd<Self> for &'a UInt<N, T, F> {
    type Output = UInt<N, T, F>;
    /// Outputs `self & other`.
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
    /// let c = UInt8::new_witness(cs.clone(), || Ok(16 & 17))?;
    ///
    /// (a & &b).enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand(self, other: Self) -> Self::Output {
        self._and(other).unwrap()
    }
}

impl<'a, const N: usize, T: PrimInt + Debug, F: Field> BitAnd<&'a Self> for UInt<N, T, F> {
    type Output = UInt<N, T, F>;
    /// Outputs `self & other`.
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
    /// let c = UInt8::new_witness(cs.clone(), || Ok(16 & 17))?;
    ///
    /// (a & &b).enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand(self, other: &Self) -> Self::Output {
        self._and(&other).unwrap()
    }
}

impl<'a, const N: usize, T: PrimInt + Debug, F: Field> BitAnd<UInt<N, T, F>> for &'a UInt<N, T, F> {
    type Output = UInt<N, T, F>;

    /// Outputs `self & other`.
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
    /// let c = UInt8::new_witness(cs.clone(), || Ok(16 & 17))?;
    ///
    /// (a & &b).enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand(self, other: UInt<N, T, F>) -> Self::Output {
        self._and(&other).unwrap()
    }
}

impl<const N: usize, T: PrimInt + Debug, F: Field> BitAnd<Self> for UInt<N, T, F> {
    type Output = Self;

    /// Outputs `self & other`.
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
    /// let c = UInt8::new_witness(cs.clone(), || Ok(16 & 17))?;
    ///
    /// (a & &b).enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand(self, other: Self) -> Self::Output {
        self._and(&other).unwrap()
    }
}

impl<const N: usize, T: PrimInt + Debug, F: Field> BitAndAssign<Self> for UInt<N, T, F> {
    /// Sets `self = self & other`.
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
    /// let b = UInt8::new_witness(cs.clone(), || Ok(17))?;
    /// let c = UInt8::new_witness(cs.clone(), || Ok(16 & 17))?;
    ///
    /// a &= &b;
    /// a.enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand_assign(&mut self, other: Self) {
        let result = self._and(&other).unwrap();
        *self = result;
    }
}

impl<'a, const N: usize, T: PrimInt + Debug, F: Field> BitAndAssign<&'a Self> for UInt<N, T, F> {
    /// Sets `self = self & other`.
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
    /// let b = UInt8::new_witness(cs.clone(), || Ok(17))?;
    /// let c = UInt8::new_witness(cs.clone(), || Ok(16 & 17))?;
    ///
    /// a &= &b;
    /// a.enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitand_assign(&mut self, other: &'a Self) {
        let result = self._and(other).unwrap();
        *self = result;
    }
}
