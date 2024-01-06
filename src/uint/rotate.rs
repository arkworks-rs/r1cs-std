use super::*;

impl<const N: usize, T: PrimUInt, ConstraintF: Field> UInt<N, T, ConstraintF> {
    /// Rotates `self` to the right by `by` steps, wrapping around.
    ///
    /// # Examples
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let a = UInt32::new_witness(cs.clone(), || Ok(0xb301u32))?;
    /// let b = UInt32::new_witness(cs.clone(), || Ok(0x10000b3))?;
    ///
    /// a.rotate_right(8).enforce_equal(&b)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self))]
    pub fn rotate_right(&self, by: usize) -> Self {
        let mut result = self.clone();
        result.rotate_right_in_place(by);
        result
    }
    /// Rotates `self` to the right *in place* by `by` steps, wrapping around.
    ///
    /// # Examples
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let mut a = UInt32::new_witness(cs.clone(), || Ok(0xb301u32))?;
    /// let b = UInt32::new_witness(cs.clone(), || Ok(0x10000b3))?;
    ///
    /// a.rotate_right_in_place(8);
    /// a.enforce_equal(&b)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self))]
    pub fn rotate_right_in_place(&mut self, by: usize) {
        let by = by % N;
        // `[T]::rotate_left` corresponds to a `rotate_right` of the bits.
        self.bits.rotate_left(by);
        self.value = self.value.map(|v| v.rotate_right(by as u32));
    }

    /// Rotates `self` to the left by `by` steps, wrapping around.
    ///
    /// # Examples
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let a = UInt32::new_witness(cs.clone(), || Ok(0x10000b3))?;
    /// let b = UInt32::new_witness(cs.clone(), || Ok(0xb301u32))?;
    ///
    /// a.rotate_left(8).enforce_equal(&b)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[tracing::instrument(target = "r1cs", skip(self))]
    pub fn rotate_left(&self, by: usize) -> Self {
        let mut result = self.clone();
        result.rotate_left_in_place(by);
        result
    }

    /// Rotates `self` to the left *in place* by `by` steps, wrapping around.
    ///
    /// # Examples
    /// ```
    /// # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
    /// // We'll use the BLS12-381 scalar field for our constraints.
    /// use ark_test_curves::bls12_381::Fr;
    /// use ark_relations::r1cs::*;
    /// use ark_r1cs_std::prelude::*;
    ///
    /// let cs = ConstraintSystem::<Fr>::new_ref();
    /// let mut a = UInt32::new_witness(cs.clone(), || Ok(0x10000b3))?;
    /// let b = UInt32::new_witness(cs.clone(), || Ok(0xb301u32))?;
    ///
    /// a.rotate_left_in_place(8);
    /// a.enforce_equal(&b)?;
    /// assert!(cs.is_satisfied().unwrap());
    /// # Ok(())
    /// # }
    /// ```
    pub fn rotate_left_in_place(&mut self, by: usize) {
        let by = by % N;
        // `[T]::rotate_right` corresponds to a `rotate_left` of the bits.
        self.bits.rotate_right(by);
        self.value = self.value.map(|v| v.rotate_left(by as u32));
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

    fn uint_rotate_left<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs();
        let expected_mode = if a.is_constant() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        for shift in 0..N {
            let computed = a.rotate_left(shift);
            let expected = UInt::<N, T, F>::new_variable(
                cs.clone(),
                || Ok(a.value()?.rotate_left(shift as u32)),
                expected_mode,
            )?;
            assert_eq!(expected.value(), computed.value());
            expected.enforce_equal(&computed)?;
            if !a.is_constant() {
                assert!(cs.is_satisfied().unwrap());
            }
        }
        Ok(())
    }

    fn uint_rotate_right<T: PrimUInt, const N: usize, F: PrimeField>(
        a: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs();
        let expected_mode = if a.is_constant() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        for shift in 0..N {
            let computed = a.rotate_right(shift);
            let expected = UInt::<N, T, F>::new_variable(
                cs.clone(),
                || Ok(a.value()?.rotate_right(shift as u32)),
                expected_mode,
            )?;
            assert_eq!(expected.value(), computed.value());
            expected.enforce_equal(&computed)?;
            if !a.is_constant() {
                assert!(cs.is_satisfied().unwrap());
            }
        }
        Ok(())
    }

    #[test]
    fn u8_rotate_left() {
        run_unary_exhaustive(uint_rotate_left::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_rotate_left() {
        run_unary_random::<1000, 16, _, _>(uint_rotate_left::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_rotate_left() {
        run_unary_random::<1000, 32, _, _>(uint_rotate_left::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_rotate_left() {
        run_unary_random::<200, 64, _, _>(uint_rotate_left::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_rotate_left() {
        run_unary_random::<100, 128, _, _>(uint_rotate_left::<u128, 128, Fr>).unwrap()
    }

    #[test]
    fn u8_rotate_right() {
        run_unary_exhaustive(uint_rotate_right::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_rotate_right() {
        run_unary_random::<1000, 16, _, _>(uint_rotate_right::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_rotate_right() {
        run_unary_random::<1000, 32, _, _>(uint_rotate_right::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_rotate_right() {
        run_unary_random::<200, 64, _, _>(uint_rotate_right::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_rotate_right() {
        run_unary_random::<100, 128, _, _>(uint_rotate_right::<u128, 128, Fr>).unwrap()
    }
}
