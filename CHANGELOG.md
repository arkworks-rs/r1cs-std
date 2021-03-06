## Pending

### Breaking changes
- #12 Make the output of the `ToBitsGadget` impl for `FpVar` fixed-size
- #48 Add `Clone` trait bound to `CondSelectGadget`.

### Features
- #21 Add `UInt128`
- #50 Add `DensePolynomialVar`

### Improvements
- #5 Speedup BLS-12 pairing
- #13 Add `ToConstraintFieldGadget` to `ProjectiveVar`
- #15, #16 Allow `cs` to be `None` when converting a Montgomery point into a Twisted Edwards point
- #20 Add `CondSelectGadget` impl for `UInt`s
- #22 Reduce density of `three_bit_cond_neg_lookup`
- #23 Reduce allocations in `UInt`s
- #33 Speedup scalar multiplication by a constant
- #35 Construct a `FpVar` from bits
- #36 Implement `ToConstraintFieldGadget` for `Vec<Uint8>`
- #40, #43 Faster scalar multiplication for Short Weierstrass curves by relying on affine formulae
- #46 Add mux gadget as an auto-impl in `CondSelectGadget` to support random access of an array

### Bug fixes
- #8 Fix bug in `three_bit_cond_neg_lookup` when using a constant lookup bit
- #9 Fix bug in `short_weierstrass::ProjectiveVar::to_affine` 
- #29 Fix `to_non_unique_bytes` for `BLS12::G1Prepared`
- #34 Fix `mul_by_inverse` for constants
- #42 Fix regression in `mul_by_inverse` constraint count
- #47 Compile with `panic='abort'` in release mode, for safety of the library across FFI boundaries.

## v0.1.0

Initial release