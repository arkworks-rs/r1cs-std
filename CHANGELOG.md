## Pending

### Breaking changes
- #12 Make FpVar's ToBitsGadget output constant length bit vectors.

### Features


### Improvements
- #5 Speedup BLS-12 pairing
- #13 Add ToConstraintFieldGadget to ProjectiveVar
- #15, #16 Allow cs to be none when converting a montgomery point into a twisted edwards point
- #20 Add conditional select gadget to Uints
- #21 Add Uint128
- #22 Reduce density of `three_bit_cond_neg_lookup`
- #23 Reduce allocations in Uints
- #33 Speedup scalar multiplication by a constant
- #35 Construct a FpVar from bits
- #36 ImplementToConstraintFieldGadget for `Vec<Uint8>`

### Bug fixes
- #8 Fix bug in three_bit_cond_neg_lookup when using a constant lookup bit
- #9 Fix bug in short weierstrass projective curve point's to_affine method
- #29 Fix `to_non_unique_bytes` for `BLS12::G1Prepared`
- #34 Fix `mul_by_inverse` for constants
- #42 Fix regression in `mul_by_inverse` constraint count

## v0.1.0

Initial release