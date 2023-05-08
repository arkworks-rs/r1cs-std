use crate::prelude::*;
use ark_ff::Field;
use ark_relations::r1cs::{ConstraintSystemRef, LinearCombination, SynthesisError};
use ark_std::vec::Vec;
/// Generates constraints for selecting between one of many values.
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

    #[allow(unused_variables)]
    /// Given a:
    /// - vector of leaf values `values`
    /// - vector of values `root_vals`, where each element is the expected value
    ///   of a root of a subtree corresponding to the lowest `l` bits
    /// - list of linear combination `sub_tree` for bottom tree of `2^l` leaves,
    ///   represnting the sum-of-condidtions of elements.
    /// Return:
    /// - a vector of allocated values of `Self`, TODO
    fn hybrid_selection(
        values: &[Self],
        root_vals: Vec<Self>,
        two_to_l: usize,
        two_to_m: usize,
        sub_tree: Vec<LinearCombination<ConstraintF>>,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<Vec<Self>, SynthesisError> {
        unimplemented!()
    }

    /// Returns an element of `values` whose index in represented by `position`.
    /// `position` is an array of boolean that represents an unsigned integer in
    /// big endian order. This is hybrid method 5.3 from <https://github.com/mir-protocol/r1cs-workshop/blob/master/workshop.pdf>.
    ///
    /// # Example
    /// To get the 6th element of `values`, convert unsigned integer 6 (`0b110`)
    /// to `position = [True, True, False]`,
    /// and call `conditionally_select_power_of_two_vector(position, values)`.
    fn conditionally_select_power_of_two_vector(
        position: &[Boolean<ConstraintF>],
        values: &[Self],
    ) -> Result<Self, SynthesisError> {
        let cs = position[0].cs();
        let n = position.len();

        // split n into l and m, where l + m = n
        // total cost is 2^m + 2^l - l - 2, so we'd rather maximize l than m
        let m = n / 2;
        let l = n - m;

        let two_to_l = 1 << l;
        let two_to_m = 1 << m;

        // we only need the lower L bits
        let lower_bits = &mut position[m..].to_vec();
        let sub_tree = sum_of_conditions(lower_bits)?;

        // index for the chunk
        let mut index = 0;
        for x in lower_bits {
            index *= 2;
            index += if x.value()? { 1 } else { 0 };
        }
        let chunk_size = 1 << l;
        let root_vals: Vec<Self> = values
            .chunks(chunk_size)
            .map(|chunk| chunk[index].clone())
            .collect();

        let upper_elems =
            Self::hybrid_selection(values, root_vals, two_to_l, two_to_m, sub_tree, cs)?;

        // apply the repeated selection method, to select one of 2^m subtree results
        let upper_bits = &mut position[..m].to_vec();
        repeated_selection(upper_bits, upper_elems)
    }
}

/// Sum of conditions method 5.2 from <https://github.com/mir-protocol/r1cs-workshop/blob/master/workshop.pdf>
/// Use this to generate the selector sums.
fn sum_of_conditions<ConstraintF: Field>(
    position: &[Boolean<ConstraintF>],
) -> Result<Vec<LinearCombination<ConstraintF>>, SynthesisError> {
    let n = position.len();
    let m = 1 << n;

    let mut selectors: Vec<Boolean<ConstraintF>> = vec![Boolean::constant(true); m];
    // let's construct the table of selectors.
    // for a bit-decomposition (b_{n-1}, b_{n-2}, ..., b_0) of `power`:
    // [
    //      (b_{n-1} * b_{n-2} * ... * b_1 * b_0),
    //      (b_{n-1} * b_{n-2} * ... * b_1),
    //      (b_{n-1} * b_{n-2} * ... * b_0),
    //      ...
    //      (b_1 * b_0),
    //      b_1,
    //      b_0,
    //      1,
    // ]
    //
    // the element of the selector table at index i is a product of `bits`
    // e.g. for i = 5 == (101)_binary
    // `selectors[5]` <== b_2 * b_0`
    // we can construct the first `max_bits_in_power - 1` elements without products,
    // directly from `bits`:
    // e.g.:
    // `selectors[0] <== 1`
    // `selectors[1] <== b_0`
    // `selectors[2] <== b_1`
    // `selectors[4] <== b_2`
    // `selectors[8] <== b_3`

    // First element is 1==true, but we've already initialized the vector with
    // `true`.
    for i in 0..n {
        selectors[1 << i] = position[n - i - 1].clone();
        for j in (1 << i) + 1..(1 << (i + 1)) {
            selectors[j] = selectors[1 << i].and(&selectors[j - (1 << i)])?;
        }
    }

    fn count_ones(x: usize) -> usize {
        // count the number of 1s in the binary representation of x
        let mut count = 0;
        let mut y = x;
        while y > 0 {
            count += y & 1;
            y >>= 1;
        }
        count
    }

    // Selector sums for each leaf node
    // E.g. for n = 2, m = 4 we have:
    // `selectors[0] <== 1`
    // `selectors[1] <== b_0`
    // `selectors[2] <== b_1`
    // `selectors[3] <== b_1 * b_0`
    // Then the selector_sums for i = 0, 1, 2, 3 are:
    // i = 0 = (00) = (1-b_1)*(1-b_0) = 1 - b_0 - b_1 + b_0*b_1 = selectors[0] -
    // selectors[1] - selectors[2] + selectors[3] i = 1 = (01) = (1-b_1)*b_0 =
    // b_0 - b_0*b_1               =                selectors[1]                -
    // selectors[3] i = 2 = (10) = b_1*(1-b_0) = b_1 - b_0*b_1               =
    // selectors[2] - selectors[3] i = 3 = (11) = b_1*b_0
    // =                                              selectors[3]
    let mut selector_sums: Vec<LinearCombination<ConstraintF>> = vec![LinearCombination::zero(); m];
    for i in 0..m {
        for j in 0..m {
            if i | j == j {
                let counts = count_ones(j - i);
                if counts % 2 == 0 {
                    selector_sums[i] = &selector_sums[i] + &selectors[j].lc();
                } else {
                    selector_sums[i] = &selector_sums[i] - &selectors[j].lc();
                };
            }
        }
    }
    Ok(selector_sums)
}

/// Repeated selection method 5.1 from <https://github.com/mir-protocol/r1cs-workshop/blob/master/workshop.pdf>
fn repeated_selection<ConstraintF: Field, CondG: CondSelectGadget<ConstraintF>>(
    position: &[Boolean<ConstraintF>],
    values: Vec<CondG>,
) -> Result<CondG, SynthesisError> {
    let m = values.len();
    let n = position.len();

    // Assert m is a power of 2, and n = log(m)
    assert!(m.is_power_of_two());
    assert_eq!(1 << n, m);

    let mut cur_mux_values = values;

    // Traverse the evaluation tree from bottom to top in level order traversal.
    for i in 0..n {
        // Size of current layer.
        let cur_size = 1 << (n - i);
        assert_eq!(cur_mux_values.len(), cur_size);

        let mut next_mux_values = Vec::new();
        for j in (0..cur_size).step_by(2) {
            let cur = CondG::conditionally_select(
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
