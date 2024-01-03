use super::*;
use crate::select::CondSelectGadget;

impl<const N: usize, T: PrimUInt, ConstraintF: PrimeField> CondSelectGadget<ConstraintF>
    for UInt<N, T, ConstraintF>
{
    #[tracing::instrument(target = "r1cs", skip(cond, true_value, false_value))]
    fn conditionally_select(
        cond: &Boolean<ConstraintF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let selected_bits = true_value
            .bits
            .iter()
            .zip(&false_value.bits)
            .map(|(t, f)| cond.select(t, f));
        let mut bits = [Boolean::FALSE; N];
        for (result, new) in bits.iter_mut().zip(selected_bits) {
            *result = new?;
        }

        let value = cond.value().ok().and_then(|cond| {
            if cond {
                true_value.value().ok()
            } else {
                false_value.value().ok()
            }
        });
        Ok(Self { bits, value })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        alloc::{AllocVar, AllocationMode},
        prelude::EqGadget,
        uint::test_utils::{run_binary_exhaustive, run_binary_random},
    };
    use ark_ff::PrimeField;
    use ark_test_curves::bls12_381::Fr;

    fn uint_select<T: PrimUInt, const N: usize, F: PrimeField>(
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
        for cond in [true, false] {
            let expected = UInt::new_variable(
                cs.clone(),
                || Ok(if cond { a.value()? } else { b.value()? }),
                expected_mode,
            )?;
            let cond = Boolean::new_variable(cs.clone(), || Ok(cond), expected_mode)?;
            let computed = cond.select(&a, &b)?;

            assert_eq!(expected.value(), computed.value());
            expected.enforce_equal(&computed)?;
            if !both_constant {
                assert!(cs.is_satisfied().unwrap());
            }
        }
        Ok(())
    }

    #[test]
    fn u8_select() {
        run_binary_exhaustive(uint_select::<u8, 8, Fr>).unwrap()
    }

    #[test]
    fn u16_select() {
        run_binary_random::<1000, 16, _, _>(uint_select::<u16, 16, Fr>).unwrap()
    }

    #[test]
    fn u32_select() {
        run_binary_random::<1000, 32, _, _>(uint_select::<u32, 32, Fr>).unwrap()
    }

    #[test]
    fn u64_select() {
        run_binary_random::<1000, 64, _, _>(uint_select::<u64, 64, Fr>).unwrap()
    }

    #[test]
    fn u128_select() {
        run_binary_random::<1000, 128, _, _>(uint_select::<u128, 128, Fr>).unwrap()
    }
}
