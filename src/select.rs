use crate::prelude::*;
use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;
use ark_std::vec::Vec;
/// Generates constraints for selecting between one of two values.
pub trait CondSelectGadget<ConstraintF: Field>
where
    Self: Sized,
    Self: Clone,
{
    /// If `cond == &Boolean::TRUE`, then this returns `true_value`; else,
    /// returns `false_value`.
    ///
    /// # Note
    /// `Self::conditionally_select(cond, true_value, false_value)?` can be more
    /// succinctly written as `cond.select(&true_value, &false_value)?`.
    fn conditionally_select(
        cond: &Boolean<ConstraintF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError>;

    /// Returns an element of `values` whose index in represented by `position`.
    /// `position` is an array of boolean that represents an unsigned integer in
    /// big endian order.
    ///
    /// # Example
    /// To get the 6th element of `values`, convert unsigned integer 6 (`0b110`)
    /// to `position = [True, True, False]`,
    /// and call `conditionally_select_power_of_two_vector(position, values)`.
    fn conditionally_select_power_of_two_vector(
        position: &[Boolean<ConstraintF>],
        values: &[Self],
    ) -> Result<Self, SynthesisError> {
        let m = values.len();
        let n = position.len();

        // Assert m is a power of 2, and n = log(m)
        assert!(m.is_power_of_two());
        assert_eq!(1 << n, m);

        let mut cur_mux_values = values.to_vec();

        // Traverse the evaluation tree from bottom to top in level order traversal.
        // This is method 5.1 from https://github.com/mir-protocol/r1cs-workshop/blob/master/workshop.pdf
        // TODO: Add method 5.2/5.3
        for i in 0..n {
            // Size of current layer.
            let cur_size = 1 << (n - i);
            assert_eq!(cur_mux_values.len(), cur_size);

            let mut next_mux_values = Vec::new();
            for j in (0..cur_size).step_by(2) {
                let cur = Self::conditionally_select(
                    &position[n - 1 - i],
                    // true case
                    &cur_mux_values[j + 1],
                    // false case
                    &cur_mux_values[j],
                )?;
                next_mux_values.push(cur);
            }
            cur_mux_values = next_mux_values;
        }

        Ok(cur_mux_values[0].clone())
    }
}

/// Performs a lookup in a 4-element table using two bits.
pub trait TwoBitLookupGadget<ConstraintF: Field>
where
    Self: Sized,
{
    /// The type of values being looked up.
    type TableConstant;

    /// Interprets the slice `bits` as a two-bit integer `b = bits[0] + (bits[1]
    /// << 1)`, and then outputs `constants[b]`.
    ///
    /// For example, if `bits == [0, 1]`, and `constants == [0, 1, 2, 3]`, this
    /// method should output a variable corresponding to `2`.
    ///
    /// # Panics
    ///
    /// This method panics if `bits.len() != 2` or `constants.len() != 4`.
    fn two_bit_lookup(
        bits: &[Boolean<ConstraintF>],
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError>;
}

/// Uses three bits to perform a lookup into a table, where the last bit
/// conditionally negates the looked-up value.
pub trait ThreeBitCondNegLookupGadget<ConstraintF: Field>
where
    Self: Sized,
{
    /// The type of values being looked up.
    type TableConstant;

    /// Interprets the slice `bits` as a two-bit integer `b = bits[0] + (bits[1]
    /// << 1)`, and then outputs `constants[b] * c`, where `c = if bits[2] {
    /// -1 } else { 1 };`.
    ///
    /// That is, `bits[2]` conditionally negates the looked-up value.
    ///
    /// For example, if `bits == [1, 0, 1]`, and `constants == [0, 1, 2, 3]`,
    /// this method should output a variable corresponding to `-1`.
    ///
    /// # Panics
    ///
    /// This method panics if `bits.len() != 3` or `constants.len() != 4`.
    fn three_bit_cond_neg_lookup(
        bits: &[Boolean<ConstraintF>],
        b0b1: &Boolean<ConstraintF>,
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError>;
}
