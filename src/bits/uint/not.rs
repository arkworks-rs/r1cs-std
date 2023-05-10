use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;
use ark_std::{fmt::Debug, ops::Not};
use num_traits::PrimInt;

use super::UInt;

impl<const N: usize, T: PrimInt + Debug, F: Field> UInt<N, T, F> {
    fn _not(&self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        for a in &mut result.bits {
            *a = a.not()
        }
        result.value = self.value.map(Not::not);
        dbg!(result.value);
        Ok(result)
    }
}

impl<'a, const N: usize, T: PrimInt + Debug, F: Field> Not for &'a UInt<N, T, F> {
    type Output = UInt<N, T, F>;
    /// Outputs `!self`.
    ///
    /// If `self` is a constant, then this method *does not* create any constraints or variables.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let a = UInt8::new_witness(cs.clone(), || Ok(2))?;
    /// let b = UInt8::new_witness(cs.clone(), || Ok(!2))?;
    ///
    /// (!a).enforce_equal(&b)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self))]
    fn not(self) -> Self::Output {
        self._not().unwrap()
    }
}

impl<'a, const N: usize, T: PrimInt + Debug, F: Field> Not for UInt<N, T, F> {
    type Output = UInt<N, T, F>;

    /// Outputs `!self`.
    ///
    /// If `self` is a constant, then this method *does not* create any constraints or variables.
    ///
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let a = UInt8::new_witness(cs.clone(), || Ok(2))?;
    /// let b = UInt8::new_witness(cs.clone(), || Ok(!2))?;
    ///
    /// (!a).enforce_equal(&b)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self))]
    fn not(self) -> Self::Output {
        self._not().unwrap()
    }
}
