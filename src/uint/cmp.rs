use crate::cmp::CmpGadget;

use super::*;

impl<const N: usize, T: PrimUInt, F: PrimeField + From<T>> CmpGadget<F> for UInt<N, T, F> {
    fn is_ge(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        if N + 1 < ((F::MODULUS_BIT_SIZE - 1) as usize) {
            let a = self.to_fp()?;
            let b = other.to_fp()?;
            let (bits, _) = (a - b + F::from(T::max_value()) + F::one())
                .to_bits_le_with_top_bits_zero(N + 1)?;
            Ok(bits.last().unwrap().clone())
        } else {
            unimplemented!("bit sizes larger than modulus size not yet supported")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        alloc::{AllocVar, AllocationMode},
        prelude::EqGadget,
        uint::test_utils::{run_binary_exhaustive, run_binary_random},
        R1CSVar,
    };
    use ark_ff::PrimeField;
    use ark_test_curves::bls12_381::Fr;

    fn uint_gt<T: PrimUInt, const N: usize, F: PrimeField + From<T>>(
        a: UInt<N, T, F>,
        b: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs().or(b.cs());
        let both_constant = a.is_constant() && b.is_constant();
        let expected_mode = if both_constant {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let computed = a.is_gt(&b)?;
        let expected =
            Boolean::new_variable(cs.clone(), || Ok(a.value()? > b.value()?), expected_mode)?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !both_constant {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    fn uint_lt<T: PrimUInt, const N: usize, F: PrimeField + From<T>>(
        a: UInt<N, T, F>,
        b: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs().or(b.cs());
        let both_constant = a.is_constant() && b.is_constant();
        let expected_mode = if both_constant {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let computed = a.is_lt(&b)?;
        let expected =
            Boolean::new_variable(cs.clone(), || Ok(a.value()? < b.value()?), expected_mode)?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !both_constant {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    fn uint_ge<T: PrimUInt, const N: usize, F: PrimeField + From<T>>(
        a: UInt<N, T, F>,
        b: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs().or(b.cs());
        let both_constant = a.is_constant() && b.is_constant();
        let expected_mode = if both_constant {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let computed = a.is_ge(&b)?;
        let expected =
            Boolean::new_variable(cs.clone(), || Ok(a.value()? >= b.value()?), expected_mode)?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !both_constant {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    fn uint_le<T: PrimUInt, const N: usize, F: PrimeField + From<T>>(
        a: UInt<N, T, F>,
        b: UInt<N, T, F>,
    ) -> Result<(), SynthesisError> {
        let cs = a.cs().or(b.cs());
        let both_constant = a.is_constant() && b.is_constant();
        let expected_mode = if both_constant {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let computed = a.is_le(&b)?;
        let expected =
            Boolean::new_variable(cs.clone(), || Ok(a.value()? <= b.value()?), expected_mode)?;
        assert_eq!(expected.value(), computed.value());
        expected.enforce_equal(&computed)?;
        if !both_constant {
            assert!(cs.is_satisfied().unwrap());
        }
        Ok(())
    }

    #[test]
    fn u8_gt() {
        run_binary_exhaustive(uint_gt::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_gt() {
        run_binary_random::<1000, 16, _, _>(uint_gt::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_gt() {
        run_binary_random::<1000, 32, _, _>(uint_gt::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_gt() {
        run_binary_random::<1000, 64, _, _>(uint_gt::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_gt() {
        run_binary_random::<1000, 128, _, _>(uint_gt::<u128, 128, Fr>).unwrap()
    }

    #[test]
    fn u8_lt() {
        run_binary_exhaustive(uint_lt::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_lt() {
        run_binary_random::<1000, 16, _, _>(uint_lt::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_lt() {
        run_binary_random::<1000, 32, _, _>(uint_lt::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_lt() {
        run_binary_random::<1000, 64, _, _>(uint_lt::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_lt() {
        run_binary_random::<1000, 128, _, _>(uint_lt::<u128, 128, Fr>).unwrap()
    }

    #[test]
    fn u8_le() {
        run_binary_exhaustive(uint_le::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_le() {
        run_binary_random::<1000, 16, _, _>(uint_le::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_le() {
        run_binary_random::<1000, 32, _, _>(uint_le::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_le() {
        run_binary_random::<1000, 64, _, _>(uint_le::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_le() {
        run_binary_random::<1000, 128, _, _>(uint_le::<u128, 128, Fr>).unwrap()
    }

    #[test]
    fn u8_ge() {
        run_binary_exhaustive(uint_ge::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_ge() {
        run_binary_random::<1000, 16, _, _>(uint_ge::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_ge() {
        run_binary_random::<1000, 32, _, _>(uint_ge::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_ge() {
        run_binary_random::<1000, 64, _, _>(uint_ge::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_ge() {
        run_binary_random::<1000, 128, _, _>(uint_ge::<u128, 128, Fr>).unwrap()
    }
}
