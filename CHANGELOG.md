# CHANGELOG

## Pending

### Breaking changes

### Features

### Improvements

### Bugfixes

## v0.5.0

### Breaking changes

- [\#121](https://github.com/arkworks-rs/r1cs-std/pull/121)
    - Refactor `UInt{8,16,64,128}` into one struct `UInt`.
    - Remove `bits` module.
    - Use `std::ops` traits for `UInt` and `Boolean`.
- [\#134](https://github.com/arkworks-rs/r1cs-std/pull/134) Add `Mul<NonnativeFieldVar>` bounds and impls for `CurveVar`.
- [\#135](https://github.com/arkworks-rs/r1cs-std/pull/135)
    - Rename `NonNativeFieldVar` to `EmulatedFpVar`.
    - Rename `fields::nonnative` to `fields::emulated_fp`.
    - Rename `fields::nonnative::{Allocated}NonNativeMulResultVar` to `fields::emulated_fp::{Allocated}MulResultVar`.
- [\#136](https://github.com/arkworks-rs/r1cs-std/pull/136)
    - Rename `ToBytesGadget::to_{non_unique_}bytes` → `ToBytesGadget::to_{non_unique_}bytes_in_le`.

### Features

- [\#136](https://github.com/arkworks-rs/r1cs-std/pull/136)
    - Add `{BitAnd,BitOr,BitXor,BitAndAssign,BitOrAssign,BitXorAssign}<T> for UInt<N, T, F>`.
    - Add `UInt::rotate_{left,right}_in_place`.
    - Add `{Boolean,UInt}::not_in_place`.
    - Add `UInt::{from_bytes_le, from_bytes_be, to_bytes_be}`.
- [\#143](https://github.com/arkworks-rs/r1cs-std/pull/143) Add `AllocVar::new_variable_with_inferred_mode`.
- [\#144](https://github.com/arkworks-rs/r1cs-std/pull/144) Add `ToConstraintFieldGadget` bounds to `CurveVar` and `FieldVar`

### Improvements

### Bug Fixes

- [\#145](https://github.com/arkworks-rs/r1cs-std/pull/145)
    - Avoid deeply nested `LinearCombinations` in `EvaluationsVar::interpolate_and_evaluate` to fix the stack overflow issue when calling `.value()` on the evaluation result.
- [\#148](https://github.com/arkworks-rs/r1cs-std/pull/148)
    -  Fix panic issues during in-circuit polynomial interpolation.

## 0.4.0

- [\#117](https://github.com/arkworks-rs/r1cs-std/pull/117) Fix result of `precomputed_base_scalar_mul_le` to not discard previous value.
- [\#124](https://github.com/arkworks-rs/r1cs-std/pull/124) Fix `scalar_mul_le` constraints unsatisfiability when short Weierstrass point is zero.
- [\#127](https://github.com/arkworks-rs/r1cs-std/pull/127) Convert `NonNativeFieldVar` constants to little-endian bytes instead of big-endian (`ToBytesGadget`).
- [\#133](https://github.com/arkworks-rs/r1cs-std/pull/133) Save 1 constraint in `FpVar::{is_eq, is_neq}` by removing the unnecessary booleanity check.

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

- [\#101](https://github.com/arkworks-rs/r1cs-std/pull/101) Fix `is_zero` for twisted Edwards curves.
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
