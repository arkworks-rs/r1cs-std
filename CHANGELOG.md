## v0.2.0

### Breaking changes
- [\#12](https://github.com/arkworks-rs/r1cs-std/pull/12) Make the output of the `ToBitsGadget` impl for `FpVar` fixed-size
- [\#48](https://github.com/arkworks-rs/r1cs-std/pull/48) Add `Clone` trait bound to `CondSelectGadget`.

### Features
- [\#21](https://github.com/arkworks-rs/r1cs-std/pull/21) Add `UInt128`
- [\#50](https://github.com/arkworks-rs/r1cs-std/pull/50) Add `DensePolynomialVar`

### Improvements
- [\#5](https://github.com/arkworks-rs/r1cs-std/pull/5) Speedup BLS-12 pairing
- [\#13](https://github.com/arkworks-rs/r1cs-std/pull/13) Add `ToConstraintFieldGadget` to `ProjectiveVar`
- [\#15](https://github.com/arkworks-rs/r1cs-std/pull/15), #16 Allow `cs` to be `None` when converting a Montgomery point into a Twisted Edwards point
- [\#20](https://github.com/arkworks-rs/r1cs-std/pull/20) Add `CondSelectGadget` impl for `UInt`s
- [\#22](https://github.com/arkworks-rs/r1cs-std/pull/22) Reduce density of `three_bit_cond_neg_lookup`
- [\#23](https://github.com/arkworks-rs/r1cs-std/pull/23) Reduce allocations in `UInt`s
- [\#33](https://github.com/arkworks-rs/r1cs-std/pull/33) Speedup scalar multiplication by a constant
- [\#35](https://github.com/arkworks-rs/r1cs-std/pull/35) Construct a `FpVar` from bits
- [\#36](https://github.com/arkworks-rs/r1cs-std/pull/36) Implement `ToConstraintFieldGadget` for `Vec<Uint8>`
- [\#40](https://github.com/arkworks-rs/r1cs-std/pull/40), #43 Faster scalar multiplication for Short Weierstrass curves by relying on affine formulae
- [\#46](https://github.com/arkworks-rs/r1cs-std/pull/46) Add mux gadget as an auto-impl in `CondSelectGadget` to support random access of an array

### Bug fixes
- [\#8](https://github.com/arkworks-rs/r1cs-std/pull/8) Fix bug in `three_bit_cond_neg_lookup` when using a constant lookup bit
- [\#9](https://github.com/arkworks-rs/r1cs-std/pull/9) Fix bug in `short_weierstrass::ProjectiveVar::to_affine`
- [\#29](https://github.com/arkworks-rs/r1cs-std/pull/29) Fix `to_non_unique_bytes` for `BLS12::G1Prepared`
- [\#34](https://github.com/arkworks-rs/r1cs-std/pull/34) Fix `mul_by_inverse` for constants
- [\#42](https://github.com/arkworks-rs/r1cs-std/pull/42) Fix regression in `mul_by_inverse` constraint count
- [\#47](https://github.com/arkworks-rs/r1cs-std/pull/47) Compile with `panic='abort'` in release mode, for safety of the library across FFI boundaries
- [\#57](https://github.com/arkworks-rs/r1cs-std/pull/57) Clean up `UInt` docs

## v0.1.0

Initial release
