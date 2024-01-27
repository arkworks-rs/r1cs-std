use crate::cmp::CmpGadget;

use super::*;
use ark_ff::PrimeField;

impl<F: PrimeField> CmpGadget<F> for Boolean<F> {
    fn is_ge(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        // a | b | (a | !b) | a >= b
        // --|---|--------|--------
        // 0 | 0 |    1     |   1
        // 1 | 0 |    1     |   1
        // 0 | 1 |    0     |   0
        // 1 | 1 |    1     |   1
        Ok(self | &(!other))
    }
}

impl<F: PrimeField> Boolean<F> {
    /// Enforces that `bits`, when interpreted as a integer, is less than
    /// `F::characteristic()`, That is, interpret bits as a little-endian
    /// integer, and enforce that this integer is "in the field Z_p", where
    /// `p = F::characteristic()` .
    #[tracing::instrument(target = "r1cs")]
    pub fn enforce_in_field_le(bits: &[Self]) -> Result<(), SynthesisError> {
        // `bits` < F::characteristic() <==> `bits` <= F::characteristic() -1
        let mut b = F::characteristic().to_vec();
        assert_eq!(b[0] % 2, 1);
        b[0] -= 1; // This works, because the LSB is one, so there's no borrows.
        let run = Self::enforce_smaller_or_equal_than_le(bits, b)?;

        // We should always end in a "run" of zeros, because
        // the characteristic is an odd prime. So, this should
        // be empty.
        assert!(run.is_empty());

        Ok(())
    }

    /// Enforces that `bits` is less than or equal to `element`,
    /// when both are interpreted as (little-endian) integers.
    #[tracing::instrument(target = "r1cs", skip(element))]
    pub fn enforce_smaller_or_equal_than_le(
        bits: &[Self],
        element: impl AsRef<[u64]>,
    ) -> Result<Vec<Self>, SynthesisError> {
        let b: &[u64] = element.as_ref();

        let mut bits_iter = bits.iter().rev(); // Iterate in big-endian

        // Runs of ones in r
        let mut last_run = Boolean::TRUE;
        let mut current_run = vec![];

        let mut element_num_bits = 0;
        for _ in BitIteratorBE::without_leading_zeros(b) {
            element_num_bits += 1;
        }

        if bits.len() > element_num_bits {
            let mut or_result = Boolean::FALSE;
            for should_be_zero in &bits[element_num_bits..] {
                or_result |= should_be_zero;
                let _ = bits_iter.next().unwrap();
            }
            or_result.enforce_equal(&Boolean::FALSE)?;
        }

        for (b, a) in BitIteratorBE::without_leading_zeros(b).zip(bits_iter.by_ref()) {
            if b {
                // This is part of a run of ones.
                current_run.push(a.clone());
            } else {
                if !current_run.is_empty() {
                    // This is the start of a run of zeros, but we need
                    // to k-ary AND against `last_run` first.

                    current_run.push(last_run.clone());
                    last_run = Self::kary_and(&current_run)?;
                    current_run.truncate(0);
                }

                // If `last_run` is true, `a` must be false, or it would
                // not be in the field.
                //
                // If `last_run` is false, `a` can be true or false.
                //
                // Ergo, at least one of `last_run` and `a` must be false.
                Self::enforce_kary_nand(&[last_run.clone(), a.clone()])?;
            }
        }
        assert!(bits_iter.next().is_none());

        Ok(current_run)
    }
}
