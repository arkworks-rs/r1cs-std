# CHANGELOG

## Pending

### Breaking changes

- [\#86](https://github.com/arkworks-rs/r1cs-std/pull/86) Change the API for domains for coset.

### Features

- [\#84](https://github.com/arkworks-rs/r1cs-std/pull/84) Expose `short_weierstrass::non_zero_affine` module
  and implement `EqGadget` for `NonZeroAffineVar`.
- [\#79](https://github.com/arkworks-rs/r1cs-std/pull/79) Move `NonNativeFieldVar` from `ark-nonnative` to `ark-r1cs-std`.
- [\#76](https://github.com/arkworks-rs/r1cs-std/pull/76) Implement `ToBytesGadget` for `Vec<UInt8>`.
- [nonnative/\#45](https://github.com/arkworks-rs/nonnative/pull/45) Add `new_witness_with_le_bits` which returns the bits used during variable allocation.

### Improvements

### Bug Fixes

- [\#86](https://github.com/arkworks-rs/r1cs-std/pull/86) Make result of `query_position_to_coset` consistent with `ark-ldt`.
- [\#77](https://github.com/arkworks-rs/r1cs-std/pull/77) Fix BLS12 `G2PreparedGadget`'s `AllocVar` when G2 uses a divisive twist.

## v0.3.1

### Features

- [\#71](https://github.com/arkworks-rs/r1cs-std/pull/71) Implement the `Sum` trait for `FpVar`.
- [\#75](https://github.com/arkworks-rs/r1cs-std/pull/71) Introduce `mul_by_inverse_unchecked` for `FieldVar`. This accompanies the bug fix in [\#70](https://github.com/arkworks-rs/r1cs-std/pull/70).

### Bug Fixes

- [\#70](https://github.com/arkworks-rs/r1cs-std/pull/70) Fix soundness issues of `mul_by_inverse` for field gadgets.

## v0.3.0

### Breaking changes

- [\#60](https://github.com/arkworks-rs/r1cs-std/pull/60) Rename `AllocatedBit` to `AllocatedBool` for consistency with the `Boolean` variable.
  You can update downstream usage with `grep -rl 'AllocatedBit' . | xargs env LANG=C env LC_CTYPE=C sed -i '' 's/AllocatedBit/AllocatedBool/g'`.
- [\#65](https://github.com/arkworks-rs/r1cs-std/pull/65) Rename `Radix2Domain` in `r1cs-std` to `Radix2DomainVar`.
- [nonnative/\#43](https://github.com/arkworks-rs/nonnative/pull/43) Add padding to allocated nonnative element's `to_bytes`.

### Features

- [\#53](https://github.com/arkworks-rs/r1cs-std/pull/53) Add univariate evaluation domain and Lagrange interpolation.

### Improvements

- [\#65](https://github.com/arkworks-rs/r1cs-std/pull/65) Add support for non-constant coset offset in `Radix2DomainVar`.

### Bug Fixes

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
