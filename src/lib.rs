//! This library provides the non-native field gadget for the `arkworks` constraint-writing platform.
//! The non-native field gadget can be used as a standard `FieldVar`, given
//! reasonable non-native gadget parameters.
//!
//! This file contains the implementation of three structs:
//!
//! - `NonNativeFieldParams` specifies the constraint prime field (called `BaseField`),
//!     the simulated prime field (called `TargetField`), and internal parameters
//!     searched by the Python script (see `README.md`).
//! - `NonNativeFieldVar` implements the `FieldVar` for simulating `TargetField`
//!     arithmetic within `BaseField`.
//! - `NonNativeFieldMulResultVar` is an intermediate representations of the
//!     result of multiplication, which is hidden from the `FieldVar` interface
//!     and is left for advanced users who want better performance.
//!
//! The Python script mentioned above can be found in the subdirectory `scripts`.

#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    warnings,
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    missing_docs
)]
#![allow(
    clippy::redundant_closure_call,
    clippy::enum_glob_use,
    clippy::missing_errors_doc,
    clippy::cast_possible_truncation,
    clippy::unseparated_literal_suffix
)]
#![forbid(unsafe_code)]

#[macro_use]
extern crate ark_r1cs_std;

use crate::{
    params::{gen_params, get_params},
    reduce::{bigint_to_basefield, limbs_to_bigint, Reducer},
};
use ark_ff::{to_bytes, BigInteger, FpParameters, PrimeField};
use ark_r1cs_std::{
    bits::{ToBitsGadget, ToBytesGadget},
    boolean::Boolean,
    eq::EqGadget,
    fields::{
        fp::{AllocatedFp, FpVar},
        FieldVar,
    },
    prelude::*,
    select::{CondSelectGadget, ThreeBitCondNegLookupGadget, TwoBitLookupGadget},
    uint8::UInt8,
    R1CSVar, ToConstraintFieldGadget,
};
use ark_relations::{
    lc, ns,
    r1cs::{
        ConstraintSystemRef, LinearCombination, Namespace, Result as R1CSResult, SynthesisError,
    },
};
use ark_std::{borrow::Borrow, cmp::max, fmt::Debug, marker::PhantomData, vec, vec::Vec};
use core::hash::{Hash, Hasher};
use num_bigint::BigUint;

/// example parameters of non-native field gadget
///
/// Sample parameters for non-native field gadgets
/// - `BaseField`:              the constraint field
/// - `TargetField`:            the field being simulated
/// - `num_limbs`:              how many limbs are used
/// - `bits_per_limb`:          the size of the limbs
///
pub mod params;
/// a submodule for reducing the representations
#[doc(hidden)]
pub mod reduce;

/// a macro for computing ceil(log2(x)) for a field element x
#[doc(hidden)]
#[macro_export]
macro_rules! overhead {
    ($x:expr) => {{
        let num = $x;
        let num_bits = num.into_repr().to_bits();
        let mut skipped_bits = 0;
        for b in num_bits.iter() {
            if *b == false {
                skipped_bits += 1;
            } else {
                break;
            }
        }

        let mut is_power_of_2 = true;
        for b in num_bits.iter().skip(skipped_bits + 1) {
            if *b == true {
                is_power_of_2 = false;
            }
        }

        if is_power_of_2 {
            num_bits.len() - skipped_bits
        } else {
            num_bits.len() - skipped_bits + 1
        }
    }};
}

/// Parameters for a specific `NonNativeFieldVar` instantiation
#[derive(Clone, Debug)]
pub struct NonNativeFieldParams {
    /// The number of limbs (`BaseField` elements) used to represent a `TargetField` element. Highest limb first.
    pub num_limbs: usize,

    /// The number of bits of the limb
    pub bits_per_limb: usize,
}

/// The allocated version of `NonNativeFieldVar` (introduced below)
#[derive(Debug)]
#[must_use]
pub struct AllocatedNonNativeFieldVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// Reference to the constraint system
    pub cs: ConstraintSystemRef<BaseField>,
    /// The limbs, each of which is a BaseField gadget.
    pub limbs: Vec<AllocatedFp<BaseField>>,
    /// Number of additions done over this gadget, using which the gadget decides when to reduce.
    pub num_of_additions_over_normal_form: BaseField,
    /// Whether the limb representation is the normal form (using only the bits specified in the parameters, and the representation is strictly within the range of TargetField).
    pub is_in_the_normal_form: bool,
    /// Whether the limbs are in fact constant.
    pub is_constant: bool,
    #[doc(hidden)]
    pub target_phantom: PhantomData<TargetField>,
}

/// A gadget for representing non-native (`TargetField`) field elements over the constraint field (`BaseField`).
#[derive(Clone, Debug)]
#[must_use]
pub enum NonNativeFieldVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// Constant
    Constant(TargetField),
    /// Allocated gadget
    Var(AllocatedNonNativeFieldVar<TargetField, BaseField>),
}

impl<TargetField: PrimeField, BaseField: PrimeField> PartialEq
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn eq(&self, other: &Self) -> bool {
        self.value()
            .unwrap_or_default()
            .eq(&other.value().unwrap_or_default())
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> Eq
    for NonNativeFieldVar<TargetField, BaseField>
{
}

impl<TargetField: PrimeField, BaseField: PrimeField> Hash
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value().unwrap_or_default().hash(state);
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> R1CSVar<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    type Value = TargetField;

    fn cs(&self) -> ConstraintSystemRef<BaseField> {
        match self {
            Self::Constant(_) => ConstraintSystemRef::None,
            Self::Var(a) => a.cs.clone(),
        }
    }

    fn value(&self) -> R1CSResult<Self::Value> {
        match self {
            Self::Constant(v) => Ok(*v),
            Self::Var(v) => v.value(),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> From<Boolean<BaseField>>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn from(other: Boolean<BaseField>) -> Self {
        if let Boolean::Constant(b) = other {
            Self::Constant(<TargetField as From<u128>>::from(b as u128))
        } else {
            // `other` is a variable
            let one = Self::Constant(TargetField::one());
            let zero = Self::Constant(TargetField::zero());
            Self::conditionally_select(&other, &one, &zero).unwrap()
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField>
    From<AllocatedNonNativeFieldVar<TargetField, BaseField>>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn from(other: AllocatedNonNativeFieldVar<TargetField, BaseField>) -> Self {
        Self::Var(other)
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> Clone
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    fn clone(&self) -> Self {
        AllocatedNonNativeFieldVar {
            cs: self.cs.clone(),
            limbs: self.limbs.clone(),
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form,
            is_in_the_normal_form: self.is_in_the_normal_form,
            is_constant: self.is_constant,
            target_phantom: PhantomData,
        }
    }
}

impl<'a, TargetField: PrimeField, BaseField: PrimeField> FieldOpsBounds<'a, TargetField, Self>
    for NonNativeFieldVar<TargetField, BaseField>
{
}

impl<'a, TargetField: PrimeField, BaseField: PrimeField>
    FieldOpsBounds<'a, TargetField, NonNativeFieldVar<TargetField, BaseField>>
    for &'a NonNativeFieldVar<TargetField, BaseField>
{
}

impl<TargetField: PrimeField, BaseField: PrimeField>
    AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    /// Obtain the value of a nonnative field element
    pub fn value(&self) -> R1CSResult<TargetField> {
        let params = get_params::<TargetField, BaseField>(&self.cs);
        let bits_per_limb = params.bits_per_limb;

        let mut result = TargetField::zero();
        let mut power = TargetField::one();
        let mut base_repr: <TargetField as PrimeField>::BigInt = TargetField::one().into_repr();
        base_repr.muln(bits_per_limb as u32);
        let base: TargetField = TargetField::from_repr(base_repr).unwrap();

        for limb in self.limbs.iter().rev() {
            // switch field with the same representation
            let this_limb_as_base = limb.value().unwrap_or_default();
            let this_limb_as_bits = this_limb_as_base.into_repr().to_bits();

            let mut val = TargetField::zero();
            let mut cur = TargetField::one();

            for bit in this_limb_as_bits.iter().rev() {
                if *bit {
                    val += &cur;
                }
                cur.double_in_place();
            }

            result += &(val * power);
            power *= &base;
        }

        Ok(result)
    }

    /// Return cs
    pub fn cs(&self) -> ConstraintSystemRef<BaseField> {
        self.cs.clone()
    }

    /// Add a nonnative field element
    #[tracing::instrument(target = "r1cs")]
    pub fn add(&self, other: &Self) -> R1CSResult<Self> {
        let mut limbs = Vec::<AllocatedFp<BaseField>>::new();
        for (this_limb, other_limb) in self.limbs.iter().zip(other.limbs.iter()) {
            limbs.push(this_limb.add(other_limb));
        }

        let mut res = Self {
            cs: self.cs.clone(),
            limbs,
            num_of_additions_over_normal_form: self
                .num_of_additions_over_normal_form
                .add(&other.num_of_additions_over_normal_form)
                .add(&BaseField::one()),
            is_in_the_normal_form: false,
            is_constant: self.is_constant && other.is_constant,
            target_phantom: PhantomData,
        };

        Reducer::<TargetField, BaseField>::post_add_reduce(&mut res)?;

        Ok(res)
    }

    /// Add a constant
    #[tracing::instrument(target = "r1cs")]
    pub fn add_constant(&self, other: &TargetField) -> R1CSResult<Self> {
        let mut limbs = Vec::<AllocatedFp<BaseField>>::new();
        let other_limbs = Self::get_limbs_representations(other, Some(&self.cs))?;
        for (this_limb, other_limb) in self.limbs.iter().zip(other_limbs.iter()) {
            limbs.push(this_limb.add_constant(*other_limb));
        }

        let mut res = Self {
            cs: self.cs.clone(),
            limbs,
            num_of_additions_over_normal_form: self
                .num_of_additions_over_normal_form
                .add(&BaseField::one()),
            is_in_the_normal_form: false,
            is_constant: self.is_constant,
            target_phantom: PhantomData,
        };

        Reducer::<TargetField, BaseField>::post_add_reduce(&mut res)?;

        Ok(res)
    }

    /// Subtract a nonnative field element, without the final reduction step
    #[tracing::instrument(target = "r1cs")]
    pub fn sub_without_reduce(&self, other: &Self) -> R1CSResult<Self> {
        let params = get_params::<TargetField, BaseField>(&self.cs);
        let bits_per_limb = params.bits_per_limb;

        let mut surfeit = overhead!(other.num_of_additions_over_normal_form + BaseField::one()) + 1;
        let mut other = other.clone();
        if (surfeit + bits_per_limb > BaseField::size_in_bits() - 1)
            || (surfeit + (TargetField::size_in_bits() - bits_per_limb * (params.num_limbs - 1))
                > BaseField::size_in_bits() - 1)
        {
            Reducer::reduce(&mut other)?;
            surfeit = overhead!(other.num_of_additions_over_normal_form + BaseField::one()) + 1;
        }

        // Construct the pad
        let mut pad_non_top_limb_repr: <BaseField as PrimeField>::BigInt =
            BaseField::one().into_repr();
        pad_non_top_limb_repr.muln((surfeit + bits_per_limb) as u32);
        let pad_non_top_limb = BaseField::from_repr(pad_non_top_limb_repr).unwrap();

        let mut pad_top_limb_repr: <BaseField as PrimeField>::BigInt = BaseField::one().into_repr();
        pad_top_limb_repr.muln(
            (surfeit + (TargetField::size_in_bits() - bits_per_limb * (params.num_limbs - 1)))
                as u32,
        );
        let pad_top_limb = BaseField::from_repr(pad_top_limb_repr).unwrap();

        let cs = self.cs().or(other.cs());

        let allocated_pad_non_top_limb =
            AllocatedFp::<BaseField>::new_constant(cs.clone(), pad_non_top_limb)?;
        let allocated_pad_top_limb =
            AllocatedFp::<BaseField>::new_constant(cs.clone(), pad_top_limb)?;

        let mut allocated_pad_limbs = Vec::<AllocatedFp<BaseField>>::new();
        allocated_pad_limbs.push(allocated_pad_top_limb);
        for _ in 0..self.limbs.len() - 1 {
            allocated_pad_limbs.push(allocated_pad_non_top_limb.clone());
        }

        let pad = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs: cs.clone(),
            limbs: allocated_pad_limbs,
            num_of_additions_over_normal_form: BaseField::zero(), // not the actual value, it is because we only use `pad` to get the value
            is_in_the_normal_form: true, // not the actual value, it is because we only use `pad` to get the value
            is_constant: true, // not the actual value, it is because we only use `pad` to get the value
            target_phantom: PhantomData,
        };

        // Compute the delta between the pad to the next kp
        let pad_to_kp_gap = pad.value()?.neg();
        let pad_to_kp_limbs = Self::get_limbs_representations(&pad_to_kp_gap, Some(&self.cs))?;

        // The result is self + pad + pad_to_kp - other
        let mut limbs = Vec::<AllocatedFp<BaseField>>::new();
        for (i, ((this_limb, other_limb), pad_to_kp_limb)) in self
            .limbs
            .iter()
            .zip(other.limbs.iter())
            .zip(pad_to_kp_limbs.iter())
            .enumerate()
        {
            if i != 0 {
                limbs.push(
                    this_limb
                        .add_constant(pad_non_top_limb)
                        .add_constant(*pad_to_kp_limb)
                        .sub(other_limb),
                );
            } else {
                limbs.push(
                    this_limb
                        .add_constant(pad_top_limb)
                        .add_constant(*pad_to_kp_limb)
                        .sub(other_limb),
                );
            }
        }

        let result = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs,
            limbs,
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form
                + ((other.num_of_additions_over_normal_form + BaseField::one()).double()),
            is_in_the_normal_form: false,
            is_constant: self.is_constant && other.is_constant,
            target_phantom: PhantomData,
        };

        Ok(result)
    }

    /// Subtract a nonnative field element
    #[tracing::instrument(target = "r1cs")]
    pub fn sub(&self, other: &Self) -> R1CSResult<Self> {
        let mut result = self.sub_without_reduce(other)?;
        Reducer::<TargetField, BaseField>::post_add_reduce(&mut result)?;
        Ok(result)
    }

    /// Subtract a constant
    #[tracing::instrument(target = "r1cs")]
    pub fn sub_constant(&self, other: &TargetField) -> R1CSResult<Self> {
        self.sub(
            &AllocatedNonNativeFieldVar::<TargetField, BaseField>::new_constant(
                self.cs.clone(),
                other,
            )?,
        )
    }

    /// Multiply a nonnative field element
    #[tracing::instrument(target = "r1cs")]
    pub fn mul(&self, other: &Self) -> R1CSResult<Self> {
        let mul = self.mul_without_reduce(&other)?;
        mul.reduce()
    }

    /// Multiply a constant
    pub fn mul_constant(&self, other: &TargetField) -> R1CSResult<Self> {
        let other_gadget = AllocatedNonNativeFieldVar::new_constant(self.cs.clone(), other)?;
        self.mul(&other_gadget)
    }

    /// Compute the negate of a nonnative field element
    #[tracing::instrument(target = "r1cs")]
    pub fn negate(&self) -> R1CSResult<Self> {
        let zero = Self::new_constant(self.cs.clone(), &TargetField::zero())?;
        zero.sub(self)
    }

    /// Compute the inverse of a nonnative field element
    #[tracing::instrument(target = "r1cs")]
    pub fn inverse(&self) -> R1CSResult<Self> {
        let inverse = Self::new_witness(self.cs.clone(), || {
            Ok({
                self.value()
                    .unwrap()
                    .inverse()
                    .unwrap_or_else(TargetField::zero)
            })
        })?;

        let one = AllocatedNonNativeFieldVar::new_constant(self.cs.clone(), &TargetField::one())?;

        let actual_result = self.clone().mul(&inverse)?;
        actual_result.conditional_enforce_equal(&one, &Boolean::TRUE)?;

        Ok(inverse)
    }

    /// Convert a `TargetField` element into limbs (not constraints)
    /// This is an internal function that would be reused by a number of other functions
    pub fn get_limbs_representations(
        elem: &TargetField,
        cs: Option<&ConstraintSystemRef<BaseField>>,
    ) -> R1CSResult<Vec<BaseField>> {
        Self::get_limbs_representations_from_big_int(&elem.into_repr(), cs)
    }

    /// Obtain the limbs directly from a big int
    pub fn get_limbs_representations_from_big_int(
        elem: &<TargetField as PrimeField>::BigInt,
        cs: Option<&ConstraintSystemRef<BaseField>>,
    ) -> R1CSResult<Vec<BaseField>> {
        let mut limbs: Vec<BaseField> = Vec::new();
        let mut cur = *elem;

        let params = match cs {
            Some(cs) => get_params::<TargetField, BaseField>(cs),
            None => gen_params::<TargetField, BaseField>(),
        };

        let num_limbs = params.num_limbs;
        let bits_per_limb = params.bits_per_limb;

        // push the lower limbs first
        for _ in 0..num_limbs {
            let cur_bits = cur.to_bits(); // `to_bits` is big endian
            let cur_mod_r = <BaseField as PrimeField>::BigInt::from_bits(
                &cur_bits[cur_bits.len() - bits_per_limb..],
            ); // therefore, the lowest `bits_per_non_top_limb` bits is what we want.
            limbs.push(BaseField::from_repr(cur_mod_r).unwrap());
            cur.divn(bits_per_limb as u32);
        }

        // then we reserve, so that the limbs are ``big limb first''
        limbs.reverse();

        Ok(limbs)
    }

    /// for advanced use, multiply and output the intermediate representations (without reduction)
    /// This intermediate representations can be added with each other, and they can later be reduced back to the `NonNativeFieldVar`.
    #[tracing::instrument(target = "r1cs")]
    pub fn mul_without_reduce(
        &self,
        other: &Self,
    ) -> R1CSResult<AllocatedNonNativeFieldMulResultVar<TargetField, BaseField>> {
        let params = get_params::<TargetField, BaseField>(&self.cs);
        let num_limbs = params.num_limbs;

        let mut self_reduced = self.clone();
        let mut other_reduced = other.clone();
        Reducer::<TargetField, BaseField>::pre_mul_reduce(&mut self_reduced, &mut other_reduced)?;

        let x_num_of_additions = self_reduced.num_of_additions_over_normal_form;
        let y_num_of_additions = other_reduced.num_of_additions_over_normal_form;

        let mut prod_limbs: Vec<AllocatedFp<BaseField>> = Vec::new();

        if cfg!(feature = "density-optimized")
            || (self_reduced.is_constant || other_reduced.is_constant)
        {
            let zero =
                AllocatedFp::<BaseField>::new_constant(ns!(self.cs, "zero"), BaseField::zero())?;

            for _ in 0..2 * num_limbs - 1 {
                prod_limbs.push(zero.clone());
            }

            for i in 0..num_limbs {
                for j in 0..num_limbs {
                    let res = if self_reduced.is_constant {
                        other_reduced.limbs[j].mul_constant(self_reduced.limbs[i].value()?)
                    } else if other_reduced.is_constant {
                        self_reduced.limbs[i].mul_constant(other_reduced.limbs[j].value()?)
                    } else {
                        self_reduced.limbs[i].mul(&other_reduced.limbs[j])
                    };
                    prod_limbs[i + j] = prod_limbs[i + j].add(&res);
                }
            }
        } else {
            let x: Vec<BaseField> = self_reduced
                .limbs
                .iter()
                .map(|limb| limb.value().unwrap_or_default())
                .collect();
            let y: Vec<BaseField> = other_reduced
                .limbs
                .iter()
                .map(|limb| limb.value().unwrap_or_default())
                .collect();
            let mut z = vec![BaseField::zero(); 2 * num_limbs - 1];
            for i in 0..num_limbs {
                for j in 0..num_limbs {
                    z[i + j] += &x[i].mul(&y[j]);
                }
            }

            for z_i in &z {
                prod_limbs.push(AllocatedFp::new_witness(
                    ark_relations::ns!(self.cs, "limb product"),
                    || Ok(z_i),
                )?);
            }

            let x_vars: Vec<LinearCombination<BaseField>> = self_reduced
                .limbs
                .iter()
                .map(|f| LinearCombination::from((BaseField::one(), f.variable)))
                .collect();

            let y_vars: Vec<LinearCombination<BaseField>> = other_reduced
                .limbs
                .iter()
                .map(|f| LinearCombination::from((BaseField::one(), f.variable)))
                .collect();

            let z_vars: Vec<LinearCombination<BaseField>> = prod_limbs
                .iter()
                .map(|f| LinearCombination::from((BaseField::one(), f.variable)))
                .collect();

            for c in 0..(2 * num_limbs - 1) {
                let c_pows: Vec<_> = (0..(2 * num_limbs - 1))
                    .map(|i| BaseField::from((c + 1) as u128).pow(&vec![i as u64]))
                    .collect();
                self.cs.enforce_constraint(
                    x_vars
                        .iter()
                        .enumerate()
                        .map(|(i, x_var)| x_var * c_pows[i])
                        .fold(lc!(), |new_lc, term| new_lc + term),
                    y_vars
                        .iter()
                        .enumerate()
                        .map(|(i, y_var)| y_var * c_pows[i])
                        .fold(lc!(), |new_lc, term| new_lc + term),
                    z_vars
                        .iter()
                        .enumerate()
                        .map(|(i, z_var)| z_var * c_pows[i])
                        .fold(lc!(), |new_lc, term| new_lc + term),
                )?;
            }
        }

        Ok(AllocatedNonNativeFieldMulResultVar {
            cs: self.cs.clone(),
            limbs: prod_limbs,
            prod_of_num_of_additions: (x_num_of_additions + BaseField::one())
                * (y_num_of_additions + BaseField::one()),
            target_phantom: PhantomData,
        })
    }

    fn frobenius_map(&self, _power: usize) -> R1CSResult<Self> {
        Ok(self.clone())
    }

    fn conditional_enforce_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<BaseField>,
    ) -> R1CSResult<()> {
        let cs = self.cs().or(other.cs());
        let params = get_params::<TargetField, BaseField>(&cs);

        // Get p
        let p_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations_from_big_int(
                &<TargetField as PrimeField>::Params::MODULUS,
                Some(&cs),
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut p_gadget_limbs = Vec::new();
        for limb in p_representations.iter() {
            p_gadget_limbs.push(AllocatedFp::<BaseField>::new_constant(cs.clone(), limb)?);
        }
        let p_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs: cs.clone(),
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: BaseField::one(),
            is_in_the_normal_form: false,
            is_constant: true,
            target_phantom: PhantomData,
        };

        // Get delta
        let mut delta = self.sub_without_reduce(other)?;
        delta = should_enforce.select(
            &delta,
            &AllocatedNonNativeFieldVar::<TargetField, BaseField>::new_constant(
                cs.clone(),
                TargetField::zero(),
            )?,
        )?;
        let surfeit = overhead!(delta.num_of_additions_over_normal_form + BaseField::one()) + 1;

        let mut delta_limbs_values = Vec::<BaseField>::new();
        for limb in delta.limbs.iter() {
            delta_limbs_values.push(limb.value()?);
        }

        let delta_bigint = limbs_to_bigint(params.bits_per_limb, &delta_limbs_values);

        // Compute k = delta / p
        let k = bigint_to_basefield::<BaseField>(&(delta_bigint / p_bigint));
        let k_gadget = AllocatedFp::<BaseField>::new_witness(cs.clone(), || Ok(k))?;
        Reducer::<TargetField, BaseField>::limb_to_bits(&k_gadget, surfeit)?;

        // Compute kp
        let mut kp_gadget_limbs = Vec::new();
        for limb in &p_gadget.limbs {
            kp_gadget_limbs.push(limb.mul(&k_gadget));
        }

        // Enforce delta = kp
        Reducer::<TargetField, BaseField>::group_and_check_equality(
            cs,
            surfeit,
            params.bits_per_limb,
            params.bits_per_limb,
            &delta.limbs,
            &kp_gadget_limbs,
        )?;

        Ok(())
    }

    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<BaseField>,
    ) -> R1CSResult<()> {
        let cs = self.cs().or(other.cs()).or(should_enforce.cs());

        if cs == ConstraintSystemRef::None {
            assert!(self.value()? != other.value()?);
        } else {
            let val = should_enforce.select(
                &self.sub(other)?,
                &AllocatedNonNativeFieldVar::new_constant(cs, TargetField::one())?,
            )?;
            let _ = val.inverse()?;
        }

        Ok(())
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBitsGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bits_le(&self) -> R1CSResult<Vec<Boolean<BaseField>>> {
        let params = get_params::<TargetField, BaseField>(&self.cs);

        let mut self_normal = self.clone();
        Reducer::<TargetField, BaseField>::pre_eq_reduce(&mut self_normal)?;

        let mut bits = Vec::<Boolean<BaseField>>::new();

        for limb in self_normal.limbs.iter() {
            let limb_bits =
                Reducer::<TargetField, BaseField>::limb_to_bits(&limb, params.bits_per_limb)?;

            bits.extend_from_slice(&limb_bits);
        }
        bits.reverse();

        Boolean::enforce_in_field_le(&bits)?;

        Ok(bits)
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBytesGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bytes(&self) -> R1CSResult<Vec<UInt8<BaseField>>> {
        let mut bits = self.to_bits_le()?;
        bits.reverse();
        let mut bytes = Vec::<UInt8<BaseField>>::new();

        bits.chunks(8).for_each(|bits_per_byte| {
            let mut bits_per_byte: Vec<Boolean<BaseField>> = bits_per_byte.to_vec();
            if bits_per_byte.len() == 8 {
                bits_per_byte.resize_with(8, || Boolean::<BaseField>::constant(false));
            }

            bits_per_byte.reverse();

            bytes.push(UInt8::<BaseField>::from_bits_le(&bits_per_byte));
        });

        Ok(bytes)
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> CondSelectGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    #[tracing::instrument(target = "r1cs")]
    fn conditionally_select(
        cond: &Boolean<BaseField>,
        true_value: &Self,
        false_value: &Self,
    ) -> R1CSResult<Self> {
        let mut limbs_sel = Vec::<AllocatedFp<BaseField>>::with_capacity(true_value.limbs.len());

        for (x, y) in true_value.limbs.iter().zip(&false_value.limbs) {
            limbs_sel.push(AllocatedFp::<BaseField>::conditionally_select(cond, x, y)?);
        }

        Ok(Self {
            cs: true_value.cs.clone(),
            limbs: limbs_sel,
            num_of_additions_over_normal_form: max(
                true_value.num_of_additions_over_normal_form,
                false_value.num_of_additions_over_normal_form,
            ),
            is_in_the_normal_form: true_value.is_in_the_normal_form
                && false_value.is_in_the_normal_form,
            is_constant: false,
            target_phantom: PhantomData,
        })
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> TwoBitLookupGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    type TableConstant = TargetField;

    #[tracing::instrument(target = "r1cs")]
    fn two_bit_lookup(
        bits: &[Boolean<BaseField>],
        constants: &[Self::TableConstant],
    ) -> R1CSResult<Self> {
        debug_assert!(bits.len() == 2);
        debug_assert!(constants.len() == 4);

        let is_variable = !bits.cs().is_none();
        if is_variable {
            let cs = bits.cs();

            let params = get_params::<TargetField, BaseField>(&cs);

            let mut limbs_constants = Vec::new();
            for _ in 0..params.num_limbs {
                limbs_constants.push(Vec::new());
            }

            for constant in constants.iter() {
                let representations =
                    AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                        constant,
                        Some(&cs),
                    )?;

                for (i, representation) in representations.iter().enumerate() {
                    limbs_constants[i].push(*representation);
                }
            }

            let mut limbs = Vec::new();
            for limbs_constant in &limbs_constants {
                limbs.push(AllocatedFp::<BaseField>::two_bit_lookup(
                    bits,
                    limbs_constant,
                )?);
            }

            Ok(AllocatedNonNativeFieldVar::<TargetField, BaseField> {
                cs,
                limbs,
                num_of_additions_over_normal_form: BaseField::zero(),
                is_in_the_normal_form: true,
                is_constant: false,
                target_phantom: PhantomData,
            })
        } else {
            unreachable!("must provide a way to obtain a ConstraintSystemRef")
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ThreeBitCondNegLookupGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    type TableConstant = TargetField;

    #[tracing::instrument(target = "r1cs")]
    fn three_bit_cond_neg_lookup(
        bits: &[Boolean<BaseField>],
        b0b1: &Boolean<BaseField>,
        constants: &[Self::TableConstant],
    ) -> R1CSResult<Self> {
        debug_assert!(bits.len() == 3);
        debug_assert!(constants.len() == 4);

        let is_variable = !bits.cs().is_none();
        if is_variable {
            let params = get_params::<TargetField, BaseField>(&bits.cs());

            let mut limbs_constants = Vec::new();
            for _ in 0..params.num_limbs {
                limbs_constants.push(Vec::new());
            }

            for constant in constants.iter() {
                let representations =
                    AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                        constant,
                        Some(&bits.cs()),
                    )?;

                for (i, representation) in representations.iter().enumerate() {
                    limbs_constants[i].push(*representation);
                }
            }

            let mut limbs = Vec::new();
            for limbs_constant in &limbs_constants {
                limbs.push(AllocatedFp::<BaseField>::three_bit_cond_neg_lookup(
                    bits,
                    b0b1,
                    limbs_constant,
                )?);
            }

            Ok(AllocatedNonNativeFieldVar::<TargetField, BaseField> {
                cs: bits.cs(),
                limbs,
                num_of_additions_over_normal_form: BaseField::zero(),
                is_in_the_normal_form: true,
                is_constant: false,
                target_phantom: PhantomData,
            })
        } else {
            unreachable!("must provide a way to obtain a ConstraintSystemRef")
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> AllocVar<TargetField, BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    fn new_variable<T: Borrow<TargetField>>(
        cs: impl Into<Namespace<BaseField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> R1CSResult<Self> {
        let ns = cs.into();
        let cs = ns.cs();

        let params = get_params::<TargetField, BaseField>(&cs);

        let elem = f()?;
        let elem_representations = Self::get_limbs_representations(&elem.borrow(), Some(&cs))?;
        let mut limbs = Vec::new();

        for limb in &elem_representations {
            limbs.push(AllocatedFp::<BaseField>::new_variable(
                ark_relations::ns!(cs, "alloc"),
                || Ok(limb),
                mode,
            )?);
        }

        let num_of_additions_over_normal_form = if mode != AllocationMode::Witness {
            BaseField::zero()
        } else {
            BaseField::one()
        };

        if mode == AllocationMode::Witness {
            for limb in limbs.iter().rev().take(params.num_limbs - 1) {
                Reducer::<TargetField, BaseField>::limb_to_bits(limb, params.bits_per_limb)?;
            }

            Reducer::<TargetField, BaseField>::limb_to_bits(
                &limbs[0],
                TargetField::size_in_bits() - (params.num_limbs - 1) * params.bits_per_limb,
            )?;
        }

        Ok(Self {
            cs,
            limbs,
            num_of_additions_over_normal_form,
            is_in_the_normal_form: mode != AllocationMode::Witness,
            is_constant: mode == AllocationMode::Constant,
            target_phantom: PhantomData,
        })
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToConstraintFieldGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    fn to_constraint_field(&self) -> R1CSResult<Vec<FpVar<BaseField>>> {
        Ok(self.limbs.iter().cloned().map(FpVar::from).collect())
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> FieldVar<TargetField, BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn zero() -> Self {
        Self::Constant(TargetField::zero())
    }

    fn one() -> Self {
        Self::Constant(TargetField::one())
    }

    fn constant(v: TargetField) -> Self {
        Self::Constant(v)
    }

    #[tracing::instrument(target = "r1cs")]
    fn negate(&self) -> R1CSResult<Self> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(-*c)),
            Self::Var(v) => Ok(Self::Var(v.negate()?)),
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn inverse(&self) -> R1CSResult<Self> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(c.inverse().unwrap_or_default())),
            Self::Var(v) => Ok(Self::Var(v.inverse()?)),
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn frobenius_map(&self, power: usize) -> R1CSResult<Self> {
        match self {
            Self::Constant(c) => Ok(Self::Constant({
                let mut tmp = *c;
                tmp.frobenius_map(power);
                tmp
            })),
            Self::Var(v) => Ok(Self::Var(v.frobenius_map(power)?)),
        }
    }
}

/****************************************************************************/
/****************************************************************************/

impl_bounded_ops!(
    NonNativeFieldVar<TargetField, BaseField>,
    TargetField,
    Add,
    add,
    AddAssign,
    add_assign,
    |this: &'a NonNativeFieldVar<TargetField, BaseField>, other: &'a NonNativeFieldVar<TargetField, BaseField>| {
        use NonNativeFieldVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 + c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.add_constant(c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.add(v2).unwrap()),
        }
    },
    |this: &'a NonNativeFieldVar<TargetField, BaseField>, other: TargetField| { this + &NonNativeFieldVar::Constant(other) },
    (TargetField: PrimeField, BaseField: PrimeField),
);

impl_bounded_ops!(
    NonNativeFieldVar<TargetField, BaseField>,
    TargetField,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    |this: &'a NonNativeFieldVar<TargetField, BaseField>, other: &'a NonNativeFieldVar<TargetField, BaseField>| {
        use NonNativeFieldVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 - c2),
            (Var(v), Constant(c)) => Var(v.sub_constant(c).unwrap()),
            (Constant(c), Var(v)) => Var(v.sub_constant(c).unwrap().negate().unwrap()),
            (Var(v1), Var(v2)) => Var(v1.sub(v2).unwrap()),
        }
    },
    |this: &'a NonNativeFieldVar<TargetField, BaseField>, other: TargetField| {
        this - &NonNativeFieldVar::Constant(other)
    },
    (TargetField: PrimeField, BaseField: PrimeField),
);

impl_bounded_ops!(
    NonNativeFieldVar<TargetField, BaseField>,
    TargetField,
    Mul,
    mul,
    MulAssign,
    mul_assign,
    |this: &'a NonNativeFieldVar<TargetField, BaseField>, other: &'a NonNativeFieldVar<TargetField, BaseField>| {
        use NonNativeFieldVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 * c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.mul_constant(c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.mul(v2).unwrap()),
        }
    },
    |this: &'a NonNativeFieldVar<TargetField, BaseField>, other: TargetField| {
        if other.is_zero() {
            NonNativeFieldVar::zero()
        } else {
            this * &NonNativeFieldVar::Constant(other)
        }
    },
    (TargetField: PrimeField, BaseField: PrimeField),
);

/****************************************************************************/
/****************************************************************************/

impl<TargetField: PrimeField, BaseField: PrimeField> EqGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    #[tracing::instrument(target = "r1cs")]
    fn is_eq(&self, other: &Self) -> R1CSResult<Boolean<BaseField>> {
        let cs = self.cs().or(other.cs());

        if cs == ConstraintSystemRef::None {
            Ok(Boolean::Constant(self.value()? == other.value()?))
        } else {
            let should_enforce_equal =
                Boolean::new_witness(cs, || Ok(self.value()? == other.value()?))?;

            self.conditional_enforce_equal(other, &should_enforce_equal)?;
            self.conditional_enforce_not_equal(other, &should_enforce_equal.not())?;

            Ok(should_enforce_equal)
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<BaseField>,
    ) -> R1CSResult<()> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => {
                if c1 != c2 {
                    should_enforce.enforce_equal(&Boolean::FALSE)?;
                }
                Ok(())
            }
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let cs = v.cs.clone();
                let c = AllocatedNonNativeFieldVar::new_constant(cs, c)?;
                c.conditional_enforce_equal(v, should_enforce)
            }
            (Self::Var(v1), Self::Var(v2)) => v1.conditional_enforce_equal(v2, should_enforce),
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<BaseField>,
    ) -> R1CSResult<()> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => {
                if c1 == c2 {
                    should_enforce.enforce_equal(&Boolean::FALSE)?;
                }
                Ok(())
            }
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let cs = v.cs.clone();
                let c = AllocatedNonNativeFieldVar::new_constant(cs, c)?;
                c.conditional_enforce_not_equal(v, should_enforce)
            }
            (Self::Var(v1), Self::Var(v2)) => v1.conditional_enforce_not_equal(v2, should_enforce),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBitsGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bits_le(&self) -> R1CSResult<Vec<Boolean<BaseField>>> {
        match self {
            Self::Constant(_) => self.to_non_unique_bits_le(),
            Self::Var(v) => v.to_bits_le(),
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn to_non_unique_bits_le(&self) -> R1CSResult<Vec<Boolean<BaseField>>> {
        use ark_ff::BitIteratorLE;
        match self {
            Self::Constant(c) => Ok(BitIteratorLE::without_trailing_zeros(&c.into_repr())
                .map(Boolean::constant)
                .collect::<Vec<_>>()),
            Self::Var(v) => v.to_non_unique_bits_le(),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBytesGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    /// Outputs the unique byte decomposition of `self` in *little-endian*
    /// form.
    #[tracing::instrument(target = "r1cs")]
    fn to_bytes(&self) -> R1CSResult<Vec<UInt8<BaseField>>> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(&to_bytes![c].unwrap())),
            Self::Var(v) => v.to_bytes(),
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn to_non_unique_bytes(&self) -> R1CSResult<Vec<UInt8<BaseField>>> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(&to_bytes![c].unwrap())),
            Self::Var(v) => v.to_non_unique_bytes(),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> CondSelectGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    #[tracing::instrument(target = "r1cs")]
    fn conditionally_select(
        cond: &Boolean<BaseField>,
        true_value: &Self,
        false_value: &Self,
    ) -> R1CSResult<Self> {
        match cond {
            Boolean::Constant(true) => Ok(true_value.clone()),
            Boolean::Constant(false) => Ok(false_value.clone()),
            _ => {
                let cs = cond.cs();
                let true_value = match true_value {
                    Self::Constant(f) => AllocatedNonNativeFieldVar::new_constant(cs.clone(), f)?,
                    Self::Var(v) => v.clone(),
                };
                let false_value = match false_value {
                    Self::Constant(f) => AllocatedNonNativeFieldVar::new_constant(cs, f)?,
                    Self::Var(v) => v.clone(),
                };
                cond.select(&true_value, &false_value).map(Self::Var)
            }
        }
    }
}

/// Uses two bits to perform a lookup into a table
/// `b` is little-endian: `b[0]` is LSB.
impl<TargetField: PrimeField, BaseField: PrimeField> TwoBitLookupGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    type TableConstant = TargetField;

    #[tracing::instrument(target = "r1cs")]
    fn two_bit_lookup(b: &[Boolean<BaseField>], c: &[Self::TableConstant]) -> R1CSResult<Self> {
        debug_assert_eq!(b.len(), 2);
        debug_assert_eq!(c.len(), 4);
        if b.cs().is_none() {
            // We're in the constant case

            let lsb = b[0].value()? as usize;
            let msb = b[1].value()? as usize;
            let index = lsb + (msb << 1);
            Ok(Self::Constant(c[index]))
        } else {
            AllocatedNonNativeFieldVar::two_bit_lookup(b, c).map(Self::Var)
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ThreeBitCondNegLookupGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    type TableConstant = TargetField;

    #[tracing::instrument(target = "r1cs")]
    fn three_bit_cond_neg_lookup(
        b: &[Boolean<BaseField>],
        b0b1: &Boolean<BaseField>,
        c: &[Self::TableConstant],
    ) -> R1CSResult<Self> {
        debug_assert_eq!(b.len(), 3);
        debug_assert_eq!(c.len(), 4);

        if b.cs().or(b0b1.cs()).is_none() {
            // We're in the constant case

            let lsb = b[0].value()? as usize;
            let msb = b[1].value()? as usize;
            let index = lsb + (msb << 1);
            let intermediate = c[index];

            let is_negative = b[2].value()?;
            let y = if is_negative {
                -intermediate
            } else {
                intermediate
            };
            Ok(Self::Constant(y))
        } else {
            AllocatedNonNativeFieldVar::three_bit_cond_neg_lookup(b, b0b1, c).map(Self::Var)
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> AllocVar<TargetField, BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn new_variable<T: Borrow<TargetField>>(
        cs: impl Into<Namespace<BaseField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> R1CSResult<Self> {
        if mode == AllocationMode::Constant {
            Ok(Self::Constant(*f()?.borrow()))
        } else {
            AllocatedNonNativeFieldVar::new_variable(cs, f, mode).map(Self::Var)
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToConstraintFieldGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    #[tracing::instrument(target = "r1cs")]
    fn to_constraint_field(&self) -> R1CSResult<Vec<FpVar<BaseField>>> {
        match self {
            Self::Constant(c) => Ok(AllocatedNonNativeFieldVar::get_limbs_representations(
                c, None,
            )?
            .into_iter()
            .map(FpVar::constant)
            .collect()),
            Self::Var(v) => v.to_constraint_field(),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> NonNativeFieldVar<TargetField, BaseField> {
    /// The `mul_without_reduce` for `NonNativeFieldVar`
    #[tracing::instrument(target = "r1cs")]
    pub fn mul_without_reduce(
        &self,
        other: &Self,
    ) -> R1CSResult<NonNativeFieldMulResultVar<TargetField, BaseField>> {
        match self {
            Self::Constant(c) => Ok(NonNativeFieldMulResultVar::Constant(*c)),
            Self::Var(v) => {
                let other_v = match other {
                    Self::Constant(other_c) => {
                        AllocatedNonNativeFieldVar::new_constant(self.cs(), other_c)?
                    }
                    Self::Var(other_v) => other_v.clone(),
                };
                Ok(NonNativeFieldMulResultVar::Var(
                    v.mul_without_reduce(&other_v)?,
                ))
            }
        }
    }
}

/// The allocated form of `NonNativeFieldMulResultVar` (introduced below)
#[derive(Debug)]
#[must_use]
pub struct AllocatedNonNativeFieldMulResultVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// A reference to the constraint system
    pub cs: ConstraintSystemRef<BaseField>,
    /// Limbs of the intermediate representations (2 * num_limbs - 2)
    pub limbs: Vec<AllocatedFp<BaseField>>,
    /// The cumulative num of additions
    pub prod_of_num_of_additions: BaseField,
    /// Phantom for TargetField
    pub target_phantom: PhantomData<TargetField>,
}

/// An intermediate representation especially for the result of a multiplication, containing more limbs.
/// It is intended for advanced usage to improve the efficiency.
///
/// That is, instead of calling `mul`, one can call `mul_without_reduce` to
/// obtain this intermediate representation, which can still be added.
/// Then, one can call `reduce` to reduce it back to `NonNativeFieldVar`.
/// This may help cut the number of reduce operations.
#[derive(Debug)]
#[must_use]
pub enum NonNativeFieldMulResultVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// as a constant
    Constant(TargetField),
    /// as an allocated gadget
    Var(AllocatedNonNativeFieldMulResultVar<TargetField, BaseField>),
}

impl<TargetField: PrimeField, BaseField: PrimeField>
    AllocatedNonNativeFieldMulResultVar<TargetField, BaseField>
{
    /// Get the value of the multiplication result
    pub fn value(&self) -> R1CSResult<TargetField> {
        let params = get_params::<TargetField, BaseField>(&self.cs);

        let p_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations_from_big_int(
                &<TargetField as PrimeField>::Params::MODULUS,
                Some(&self.cs),
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut limbs_values = Vec::<BaseField>::new();
        for limb in self.limbs.iter() {
            limbs_values.push(limb.value()?);
        }
        let value_bigint = limbs_to_bigint(params.bits_per_limb, &limbs_values);

        let res = bigint_to_basefield::<TargetField>(&(value_bigint % p_bigint));
        Ok(res)
    }

    /// Constraints for reducing the result of a multiplication mod p, to get an original representation.
    pub fn reduce(&self) -> R1CSResult<AllocatedNonNativeFieldVar<TargetField, BaseField>> {
        let cs = self.cs.clone();
        let params = get_params::<TargetField, BaseField>(&self.cs);

        let p_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations_from_big_int(
                &<TargetField as PrimeField>::Params::MODULUS,
                Some(&cs),
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut p_gadget_limbs = Vec::new();
        for limb in p_representations.iter() {
            p_gadget_limbs.push(AllocatedFp::<BaseField>::new_constant(cs.clone(), limb)?);
        }
        let p_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs: cs.clone(),
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: BaseField::one(),
            is_in_the_normal_form: false,
            is_constant: true,
            target_phantom: PhantomData,
        };

        let mut limbs_values = Vec::<BaseField>::new();
        for limb in self.limbs.iter() {
            limbs_values.push(limb.value()?);
        }

        let value_bigint = limbs_to_bigint(params.bits_per_limb, &limbs_values);

        let surfeit = overhead!(self.prod_of_num_of_additions + BaseField::one()) + 1 + 1;

        let k = value_bigint / p_bigint;
        let k_bits = {
            let mut res = Vec::new();
            let mut k_cur = k;

            let total_len = TargetField::size_in_bits() + surfeit;

            for _ in 0..total_len {
                res.push(Boolean::<BaseField>::new_witness(cs.clone(), || {
                    Ok(&k_cur % 2u64 == BigUint::from(1u64))
                })?);
                k_cur /= 2u64;
            }
            res
        };

        let k_limbs = {
            let zero = AllocatedFp::<BaseField>::new_constant(cs.clone(), BaseField::zero())?;
            let mut limbs = Vec::new();

            let mut k_bits_cur = k_bits.clone();

            for i in 0..params.num_limbs {
                let this_limb_size = if i != params.num_limbs - 1 {
                    params.bits_per_limb
                } else {
                    k_bits.len() - (params.num_limbs - 1) * params.bits_per_limb
                };

                let this_limb_bits = k_bits_cur[0..this_limb_size].to_vec();
                k_bits_cur = k_bits_cur[this_limb_size..].to_vec();

                let mut limb = zero.clone();
                let mut cur = BaseField::one();

                for bit in this_limb_bits.iter() {
                    limb = limb.add(&AllocatedFp::<BaseField>::from(bit.clone()).mul_constant(cur));
                    cur.double_in_place();
                }
                limbs.push(limb);
            }

            limbs.reverse();
            limbs
        };

        let k_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            cs: cs.clone(),
            limbs: k_limbs,
            num_of_additions_over_normal_form: self.prod_of_num_of_additions,
            is_in_the_normal_form: false,
            is_constant: false,
            target_phantom: PhantomData,
        };

        let r = self.value()?;
        let r_gadget =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::new_witness(cs.clone(), || {
                Ok(r)
            })?;

        let mut kp_plus_r_gadget = p_gadget.mul_without_reduce(&k_gadget)?;
        let kp_plus_r_limbs_len = kp_plus_r_gadget.limbs.len();
        for (i, limb) in r_gadget.limbs.iter().rev().enumerate() {
            kp_plus_r_gadget.limbs[kp_plus_r_limbs_len - 1 - i] =
                kp_plus_r_gadget.limbs[kp_plus_r_limbs_len - 1 - i].add(limb);
        }

        Reducer::<TargetField, BaseField>::group_and_check_equality(
            cs,
            surfeit,
            2 * params.bits_per_limb,
            params.bits_per_limb,
            &self.limbs,
            &kp_plus_r_gadget.limbs,
        )?;

        Ok(r_gadget)
    }

    /// Add unreduced elements.
    #[tracing::instrument(target = "r1cs")]
    pub fn add(&self, other: &Self) -> R1CSResult<Self> {
        let mut new_limbs: Vec<AllocatedFp<BaseField>> = Vec::new();

        for (l1, l2) in self.limbs.iter().zip(other.limbs.iter()) {
            let new_limb = l1.add(l2);
            new_limbs.push(new_limb);
        }

        Ok(Self {
            cs: self.cs.clone(),
            limbs: new_limbs,
            prod_of_num_of_additions: self.prod_of_num_of_additions
                + other.prod_of_num_of_additions,
            target_phantom: PhantomData,
        })
    }

    /// Add native constant elem
    #[tracing::instrument(target = "r1cs")]
    pub fn add_constant(&self, other: &TargetField) -> R1CSResult<Self> {
        let mut other_limbs =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                other,
                Some(&self.cs),
            )?;
        other_limbs.reverse();

        let mut new_limbs: Vec<AllocatedFp<BaseField>> = Vec::new();

        for (i, limb) in self.limbs.iter().rev().enumerate() {
            if i < other_limbs.len() {
                new_limbs.push(limb.add_constant(other_limbs[i]));
            } else {
                new_limbs.push((*limb).clone());
            }
        }

        new_limbs.reverse();

        Ok(Self {
            cs: self.cs.clone(),
            limbs: new_limbs,
            prod_of_num_of_additions: self.prod_of_num_of_additions + BaseField::one(),
            target_phantom: PhantomData,
        })
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField>
    NonNativeFieldMulResultVar<TargetField, BaseField>
{
    /// Create a zero `NonNativeFieldMulResultVar` (used for additions)
    pub fn zero() -> Self {
        Self::Constant(TargetField::zero())
    }

    /// Create an `NonNativeFieldMulResultVar` from a constant
    pub fn constant(v: TargetField) -> Self {
        Self::Constant(v)
    }

    /// Reduce the `NonNativeFieldMulResultVar` back to NonNativeFieldVar
    #[tracing::instrument(target = "r1cs")]
    pub fn reduce(&self) -> R1CSResult<NonNativeFieldVar<TargetField, BaseField>> {
        match self {
            Self::Constant(c) => Ok(NonNativeFieldVar::Constant(*c)),
            Self::Var(v) => Ok(NonNativeFieldVar::Var(v.reduce()?)),
        }
    }
}

impl_bounded_ops!(
    NonNativeFieldMulResultVar<TargetField, BaseField>,
    TargetField,
    Add,
    add,
    AddAssign,
    add_assign,
    |this: &'a NonNativeFieldMulResultVar<TargetField, BaseField>, other: &'a NonNativeFieldMulResultVar<TargetField, BaseField>| {
        use NonNativeFieldMulResultVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 + c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.add_constant(c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.add(v2).unwrap()),
        }
    },
    |this: &'a NonNativeFieldMulResultVar<TargetField, BaseField>, other: TargetField| { this + &NonNativeFieldMulResultVar::Constant(other) },
    (TargetField: PrimeField, BaseField: PrimeField),
);
