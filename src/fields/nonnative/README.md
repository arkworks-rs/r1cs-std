<h1 align="center">Non-Native Field Gadgets</h1>

<p align="center">
    <a href="https://github.com/scipr-lab/zexe/blob/master/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/scipr-lab/zexe/blob/master/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
</p>

The `nonnative` library provides R1CS constraints for checking computations over a non-native field in a proof system. 
 
The library is based on the constraint-writing framework [arkworks-rs](https://github.com/arkworks-rs) and is released under the MIT License and the Apache v2 License (see [License](#license)).

**WARNING:** This is an academic proof-of-concept prototype; in particular, it has not received careful code review. This implementation is NOT ready for production use.

## Overview

This library implements a field gadget for a prime field `Fp` over another prime field `Fq` where `p != q`.

When writing constraint systems for many cryptographic proofs, we are restricted to a native field (e.g., the scalar field of the pairing-friendly curve).
This can be inconvenient; for example, the recursive composition of proofs via cycles of curves requires the verifier to compute over a non-native field.

The library makes it possible to write computations over a non-native field in the same way one would write computations over the native field. This naturally introduces additional overhead, which we minimize using a variety of optimizations.

## Usage

Because the non-native field implements the `FieldVar` trait in arkworks, we can treat it like a native field variable (`FpVar`).

We can do the standard field operations, such as `+`, `-`, and `*`. See the following example:

```rust
let a = NonNativeFieldVar::<Fr, Fq>::new_witness(ns!(cs, "a"), || Ok(a_value))?;
let b = NonNativeFieldVar::<Fr, Fq>::new_witness(ns!(cs, "b"), || Ok(b_value))?;

// add
let a_plus_b = &a + &b;

// sub
let a_minus_b = &a - &b;

// multiply
let a_times_b = &a * $b;

// enforce equality
a.enforce_equal(&b)?;
```

## Advanced optimization

After each multiplication, our library internally performs a *reduce* operation, which reduces an intermediate type `NonNativeFieldMulResultVar` to the normalized type `NonNativeFieldVar`.
This enables a user to seamlessly perform a sequence of operations without worrying about the underlying details.

However, this operation is expensive and is sometimes avoidable. We can reduce the number of constraints by using this intermediate type, which only supports additions. To multiply, it must be reduced back to `NonNativeFieldVar`. See below for a skeleton example. 

---

To compute `a * b + c * d`, the straightforward (but more expensive) implementation is as follows:

```
let a_times_b = &a * &b;
let c_times_d = &c * &d;
let res = &a_times_b + &c_times_d;
```

This performs two *reduce* operations in total, one for each multiplication.

---

We can save one reduction by using the `NonNativeFieldMulResultGadget`, as follows:

```
let a_times_b = a.mul_without_reduce(&b)?;
let c_times_d = c.mul_without_reduce(&d)?;
let res = (&a_times_b + &c_times_d)?.reduce()?;
```

It performs only one *reduce* operation and is roughly 2x faster than the first implementation.

## Inspiration and basic design

The library employs the standard idea of using multiple **limbs** to represent an element of the target field. For example, an element in the TargetField may be represented by three BaseField elements (i.e., the limbs).

```
TargetField -> limb 1, limb 2, and limb 3 (each is a BaseField element)
```

After some computation, the limbs become overwhelmed and need to be **reduced**, in order to engage in more computation.

We heavily use the optimization techniques in [[KPS18]](https://akosba.github.io/papers/xjsnark.pdf) and [[OWWB20]](https://eprint.iacr.org/2019/1494). Both works have their own open-source libraries: [xJsnark](https://github.com/akosba/xjsnark) and [bellman-bignat](https://github.com/alex-ozdemir/bellman-bignat). Compared with them, this library works with the arkworks environment and is also optimized for density instead of number of constraints, which is useful for holographic zero-knowledge proofs like [Marlin](https://github.com/arkworks-rs/marlin).

## License

The library is licensed under either of the following licenses, at your discretion.

 * Apache License Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

Unless you explicitly state otherwise, any contribution submitted for inclusion in this library by you shall be dual licensed as above (as defined in the Apache v2 License), without any additional terms or conditions.

## References

[KPS18]: A. E. Kosba, C. Papamanthou, and E. Shi. "xJsnark: a framework for efficient verifiable computation," in *Proceedings of the 39th Symposium on Security and Privacy*, ser. S&P ’18, 2018, pp. 944–961.

[OWWB20]: A. Ozdemir, R. S. Wahby, B. Whitehat, and D. Boneh. "Scaling verifiable computation using efficient set accumulators," in *Proceedings of the 29th USENIX Security Symposium*, ser. Security ’20, 2020.
