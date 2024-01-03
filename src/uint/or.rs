use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use ark_std::{ops::BitOr, ops::BitOrAssign};

use super::{PrimUInt, UInt};

impl<const N: usize, T: PrimUInt, F: PrimeField> UInt<N, T, F> {
    fn _or(&self, other: &Self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result._or_in_place(other)?;
        Ok(result)
    }

    fn _or_in_place(&mut self, other: &Self) -> Result<(), SynthesisError> {
        for (a, b) in self.bits.iter_mut().zip(&other.bits) {
            *a |= b;
        }
        self.value = self.value.and_then(|a| Some(a | other.value?));
        Ok(())
    }
}

impl<'a, const N: usize, T: PrimUInt, F: PrimeField> BitOr<Self> for &'a UInt<N, T, F> {
    type Output = UInt<N, T, F>;

    /// Output `self | other`.
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
    /// let c = UInt8::new_witness(cs.clone(), || Ok(16 | 17))?;
    ///
    /// (a | b).enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: Self) -> Self::Output {
        self._or(other).unwrap()
    }
}

impl<'a, const N: usize, T: PrimUInt, F: PrimeField> BitOr<&'a Self> for UInt<N, T, F> {
    type Output = UInt<N, T, F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(mut self, other: &Self) -> Self::Output {
        self._or_in_place(&other).unwrap();
        self
    }
}

impl<'a, const N: usize, T: PrimUInt, F: PrimeField> BitOr<UInt<N, T, F>> for &'a UInt<N, T, F> {
    type Output = UInt<N, T, F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: UInt<N, T, F>) -> Self::Output {
        other | self
    }
}

impl<const N: usize, T: PrimUInt, F: PrimeField> BitOr<Self> for UInt<N, T, F> {
    type Output = Self;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: Self) -> Self::Output {
        self | &other
    }
}

impl<'a, const N: usize, T: PrimUInt, F: PrimeField> BitOr<T> for UInt<N, T, F> {
    type Output = UInt<N, T, F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: T) -> Self::Output {
        self | &UInt::constant(other)
    }
}

impl<'a, const N: usize, T: PrimUInt, F: PrimeField> BitOr<&'a T> for UInt<N, T, F> {
    type Output = UInt<N, T, F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: &'a T) -> Self::Output {
        self | &UInt::constant(*other)
    }
}

impl<'a, const N: usize, T: PrimUInt, F: PrimeField> BitOr<&'a T> for &'a UInt<N, T, F> {
    type Output = UInt<N, T, F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: &'a T) -> Self::Output {
        self | &UInt::constant(*other)
    }
}

impl<'a, const N: usize, T: PrimUInt, F: PrimeField> BitOr<T> for &'a UInt<N, T, F> {
    type Output = UInt<N, T, F>;

    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor(self, other: T) -> Self::Output {
        self | &UInt::constant(other)
    }
}

impl<const N: usize, T: PrimUInt, F: PrimeField> BitOrAssign<Self> for UInt<N, T, F> {
    /// Sets `self = self | other`.
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
    /// let c = UInt8::new_witness(cs.clone(), || Ok(16 | 17))?;
    ///
    /// a |= b;
    /// a.enforce_equal(&c)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor_assign(&mut self, other: Self) {
        self._or_in_place(&other).unwrap();
    }
}

impl<'a, const N: usize, T: PrimUInt, F: PrimeField> BitOrAssign<&'a Self> for UInt<N, T, F> {
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor_assign(&mut self, other: &'a Self) {
        self._or_in_place(other).unwrap();
    }
}

impl<const N: usize, T: PrimUInt, F: PrimeField> BitOrAssign<T> for UInt<N, T, F> {
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor_assign(&mut self, other: T) {
        *self |= &UInt::constant(other);
    }
}

impl<'a, const N: usize, T: PrimUInt, F: PrimeField> BitOrAssign<&'a T> for UInt<N, T, F> {
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    fn bitor_assign(&mut self, other: &'a T) {
        *self |= &UInt::constant(*other);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        alloc::{AllocVar, AllocationMode},
        prelude::EqGadget,
        uint::test_utils::{run_binary_exhaustive_both, run_binary_random_both},
        R1CSVar,
    };
    use ark_ff::PrimeField;
    use ark_test_curves::bls12_381::Fr;

    fn uint_or<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
        b: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs().or(b.cs());
        let both_constant = a.is_constant() && b.is_constant();
        let computed = &a | &b;
        let expected_mode = if both_constant {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let expected = UInt::<N, T, F>::new_variable(
            cs.clone(),
            || Ok(a.value()? | b.value()?),
            expected_mode,
        )?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !both_constant {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    fn uint_or_native<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
        b: T,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs();
        let computed = &a | &b;
        let expected_mode = if a.is_constant() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let expected =
            UInt::<N, T, F>::new_variable(cs.clone(), || Ok(a.value()? | b), expected_mode)?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !a.is_constant() {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    #[test]
    fn u8_or() {
        run_binary_exhaustive_both(uint_or::<u8, 8, Fr>, uint_or_native::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_or() {
        run_binary_random_both::<1000, 16, _, _>(
            uint_or::<u16, 16, Fr>,
            uint_or_native::<u16, 16, Fr>,
        )
        .unwrap()
    }

    #[test]
    fn u32_or() {
        run_binary_random_both::<1000, 32, _, _>(
            uint_or::<u32, 32, Fr>,
            uint_or_native::<u32, 32, Fr>,
        )
        .unwrap()
    }

    #[test]
    fn u64_or() {
        run_binary_random_both::<1000, 64, _, _>(
            uint_or::<u64, 64, Fr>,
            uint_or_native::<u64, 64, Fr>,
        )
        .unwrap()
    }

    #[test]
    fn u128_or() {
        run_binary_random_both::<1000, 128, _, _>(
            uint_or::<u128, 128, Fr>,
            uint_or_native::<u128, 128, Fr>,
        )
        .unwrap()
    }
}
