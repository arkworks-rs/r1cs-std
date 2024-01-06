use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;
use ark_std::ops::Not;

use super::*;

impl<const N: usize, T: PrimUInt, F: Field> UInt<N, T, F> {
    fn _not(&self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result._not_in_place()?;
        Ok(result)
    }

    fn _not_in_place(&mut self) -> Result<(), SynthesisError> {
        for a in &mut self.bits {
            a.not_in_place()?;
        }
        self.value = self.value.map(Not::not);
        Ok(())
    }
}

impl<'a, const N: usize, T: PrimUInt, F: Field> Not for &'a UInt<N, T, F> {
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

impl<'a, const N: usize, T: PrimUInt, F: Field> Not for UInt<N, T, F> {
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
    fn not(mut self) -> Self::Output {
        self._not_in_place().unwrap();
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        alloc::{AllocVar, AllocationMode},
        prelude::EqGadget,
        uint::test_utils::{run_unary_exhaustive, run_unary_random},
        R1CSVar,
    };
    use ark_ff::PrimeField;
    use ark_test_curves::bls12_381::Fr;

    fn uint_not<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs();
        let computed = !&a;
        let expected_mode = if a.is_constant() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let expected =
            UInt::<N, T, F>::new_variable(cs.clone(), || Ok(!a.value()?), expected_mode)?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !a.is_constant() {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    #[test]
    fn u8_not() {
        run_unary_exhaustive(uint_not::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_not() {
        run_unary_random::<1000, 16, _, _>(uint_not::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_not() {
        run_unary_random::<1000, 32, _, _>(uint_not::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_not() {
        run_unary_random::<1000, 64, _, _>(uint_not::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128() {
        run_unary_random::<1000, 128, _, _>(uint_not::<u128, 128, Fr>).unwrap()
    }
}
