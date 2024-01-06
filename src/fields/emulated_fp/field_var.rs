use super::{params::OptimizationType, AllocatedEmulatedFpVar, MulResultVar};
use crate::{
    boolean::Boolean,
    convert::{ToBitsGadget, ToBytesGadget, ToConstraintFieldGadget},
    fields::{fp::FpVar, FieldVar},
    prelude::*,
    R1CSVar,
};
use ark_ff::{BigInteger, PrimeField};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, Result as R1CSResult, SynthesisError};
use ark_std::{
    borrow::Borrow,
    hash::{Hash, Hasher},
    vec::Vec,
};

/// A gadget for representing non-native (`TargetF`) field elements over the
/// constraint field (`BaseF`).
#[derive(Clone, Debug)]
#[must_use]
pub enum EmulatedFpVar<TargetF: PrimeField, BaseF: PrimeField> {
    /// Constant
    Constant(TargetF),
    /// Allocated gadget
    Var(AllocatedEmulatedFpVar<TargetF, BaseF>),
}

impl<TargetF: PrimeField, BaseF: PrimeField> PartialEq for EmulatedFpVar<TargetF, BaseF> {
    fn eq(&self, other: &Self) -> bool {
        self.value()
            .unwrap_or_default()
            .eq(&other.value().unwrap_or_default())
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> Eq for EmulatedFpVar<TargetF, BaseF> {}

impl<TargetF: PrimeField, BaseF: PrimeField> Hash for EmulatedFpVar<TargetF, BaseF> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value().unwrap_or_default().hash(state);
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> R1CSVar<BaseF> for EmulatedFpVar<TargetF, BaseF> {
    type Value = TargetF;

    fn cs(&self) -> ConstraintSystemRef<BaseF> {
        match self {
            Self::Constant(_) => ConstraintSystemRef::None,
            Self::Var(a) => a.cs(),
        }
    }

    fn value(&self) -> R1CSResult<Self::Value> {
        match self {
            Self::Constant(v) => Ok(*v),
            Self::Var(v) => v.value(),
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> From<Boolean<BaseF>>
    for EmulatedFpVar<TargetF, BaseF>
{
    fn from(other: Boolean<BaseF>) -> Self {
        if let Boolean::Constant(b) = other {
            Self::Constant(<TargetF as From<u128>>::from(b as u128))
        } else {
            // `other` is a variable
            let one = Self::Constant(TargetF::one());
            let zero = Self::Constant(TargetF::zero());
            Self::conditionally_select(&other, &one, &zero).unwrap()
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> From<AllocatedEmulatedFpVar<TargetF, BaseF>>
    for EmulatedFpVar<TargetF, BaseF>
{
    fn from(other: AllocatedEmulatedFpVar<TargetF, BaseF>) -> Self {
        Self::Var(other)
    }
}

impl<'a, TargetF: PrimeField, BaseF: PrimeField> FieldOpsBounds<'a, TargetF, Self>
    for EmulatedFpVar<TargetF, BaseF>
{
}

impl<'a, TargetF: PrimeField, BaseF: PrimeField>
    FieldOpsBounds<'a, TargetF, EmulatedFpVar<TargetF, BaseF>>
    for &'a EmulatedFpVar<TargetF, BaseF>
{
}

impl<TargetF: PrimeField, BaseF: PrimeField> FieldVar<TargetF, BaseF>
    for EmulatedFpVar<TargetF, BaseF>
{
    fn zero() -> Self {
        Self::Constant(TargetF::zero())
    }

    fn one() -> Self {
        Self::Constant(TargetF::one())
    }

    fn constant(v: TargetF) -> Self {
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
                tmp.frobenius_map_in_place(power);
                tmp
            })),
            Self::Var(v) => Ok(Self::Var(v.frobenius_map(power)?)),
        }
    }
}

impl_bounded_ops!(
    EmulatedFpVar<TargetF, BaseF>,
    TargetF,
    Add,
    add,
    AddAssign,
    add_assign,
    |this: &'a EmulatedFpVar<TargetF, BaseF>, other: &'a EmulatedFpVar<TargetF, BaseF>| {
        use EmulatedFpVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 + c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.add_constant(c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.add(v2).unwrap()),
        }
    },
    |this: &'a EmulatedFpVar<TargetF, BaseF>, other: TargetF| { this + &EmulatedFpVar::Constant(other) },
    (TargetF: PrimeField, BaseF: PrimeField),
);

impl_bounded_ops!(
    EmulatedFpVar<TargetF, BaseF>,
    TargetF,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    |this: &'a EmulatedFpVar<TargetF, BaseF>, other: &'a EmulatedFpVar<TargetF, BaseF>| {
        use EmulatedFpVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 - c2),
            (Var(v), Constant(c)) => Var(v.sub_constant(c).unwrap()),
            (Constant(c), Var(v)) => Var(v.sub_constant(c).unwrap().negate().unwrap()),
            (Var(v1), Var(v2)) => Var(v1.sub(v2).unwrap()),
        }
    },
    |this: &'a EmulatedFpVar<TargetF, BaseF>, other: TargetF| {
        this - &EmulatedFpVar::Constant(other)
    },
    (TargetF: PrimeField, BaseF: PrimeField),
);

impl_bounded_ops!(
    EmulatedFpVar<TargetF, BaseF>,
    TargetF,
    Mul,
    mul,
    MulAssign,
    mul_assign,
    |this: &'a EmulatedFpVar<TargetF, BaseF>, other: &'a EmulatedFpVar<TargetF, BaseF>| {
        use EmulatedFpVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 * c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.mul_constant(c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.mul(v2).unwrap()),
        }
    },
    |this: &'a EmulatedFpVar<TargetF, BaseF>, other: TargetF| {
        if other.is_zero() {
            EmulatedFpVar::zero()
        } else {
            this * &EmulatedFpVar::Constant(other)
        }
    },
    (TargetF: PrimeField, BaseF: PrimeField),
);

/// *************************************************************************
/// *************************************************************************

impl<TargetF: PrimeField, BaseF: PrimeField> EqGadget<BaseF> for EmulatedFpVar<TargetF, BaseF> {
    #[tracing::instrument(target = "r1cs")]
    fn is_eq(&self, other: &Self) -> R1CSResult<Boolean<BaseF>> {
        let cs = self.cs().or(other.cs());

        if cs == ConstraintSystemRef::None {
            Ok(Boolean::Constant(self.value()? == other.value()?))
        } else {
            let should_enforce_equal =
                Boolean::new_witness(cs, || Ok(self.value()? == other.value()?))?;

            self.conditional_enforce_equal(other, &should_enforce_equal)?;
            self.conditional_enforce_not_equal(other, &!&should_enforce_equal)?;

            Ok(should_enforce_equal)
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<BaseF>,
    ) -> R1CSResult<()> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => {
                if c1 != c2 {
                    should_enforce.enforce_equal(&Boolean::FALSE)?;
                }
                Ok(())
            },
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let cs = v.cs();
                let c = AllocatedEmulatedFpVar::new_constant(cs, c)?;
                c.conditional_enforce_equal(v, should_enforce)
            },
            (Self::Var(v1), Self::Var(v2)) => v1.conditional_enforce_equal(v2, should_enforce),
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        should_enforce: &Boolean<BaseF>,
    ) -> R1CSResult<()> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => {
                if c1 == c2 {
                    should_enforce.enforce_equal(&Boolean::FALSE)?;
                }
                Ok(())
            },
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let cs = v.cs();
                let c = AllocatedEmulatedFpVar::new_constant(cs, c)?;
                c.conditional_enforce_not_equal(v, should_enforce)
            },
            (Self::Var(v1), Self::Var(v2)) => v1.conditional_enforce_not_equal(v2, should_enforce),
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> ToBitsGadget<BaseF> for EmulatedFpVar<TargetF, BaseF> {
    #[tracing::instrument(target = "r1cs")]
    fn to_bits_le(&self) -> R1CSResult<Vec<Boolean<BaseF>>> {
        match self {
            Self::Constant(_) => self.to_non_unique_bits_le(),
            Self::Var(v) => v.to_bits_le(),
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn to_non_unique_bits_le(&self) -> R1CSResult<Vec<Boolean<BaseF>>> {
        use ark_ff::BitIteratorLE;
        match self {
            Self::Constant(c) => Ok(BitIteratorLE::new(&c.into_bigint())
                .take((TargetF::MODULUS_BIT_SIZE) as usize)
                .map(Boolean::constant)
                .collect::<Vec<_>>()),
            Self::Var(v) => v.to_non_unique_bits_le(),
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> ToBytesGadget<BaseF>
    for EmulatedFpVar<TargetF, BaseF>
{
    /// Outputs the unique byte decomposition of `self` in *little-endian*
    /// form.
    #[tracing::instrument(target = "r1cs")]
    fn to_bytes_le(&self) -> R1CSResult<Vec<UInt8<BaseF>>> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(
                c.into_bigint().to_bytes_le().as_slice(),
            )),

            Self::Var(v) => v.to_bytes_le(),
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn to_non_unique_bytes_le(&self) -> R1CSResult<Vec<UInt8<BaseF>>> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(
                c.into_bigint().to_bytes_le().as_slice(),
            )),
            Self::Var(v) => v.to_non_unique_bytes_le(),
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> CondSelectGadget<BaseF>
    for EmulatedFpVar<TargetF, BaseF>
{
    #[tracing::instrument(target = "r1cs")]
    fn conditionally_select(
        cond: &Boolean<BaseF>,
        true_value: &Self,
        false_value: &Self,
    ) -> R1CSResult<Self> {
        match cond {
            &Boolean::Constant(true) => Ok(true_value.clone()),
            &Boolean::Constant(false) => Ok(false_value.clone()),
            _ => {
                let cs = cond.cs();
                let true_value = match true_value {
                    Self::Constant(f) => AllocatedEmulatedFpVar::new_constant(cs.clone(), f)?,
                    Self::Var(v) => v.clone(),
                };
                let false_value = match false_value {
                    Self::Constant(f) => AllocatedEmulatedFpVar::new_constant(cs, f)?,
                    Self::Var(v) => v.clone(),
                };
                cond.select(&true_value, &false_value).map(Self::Var)
            },
        }
    }
}

/// Uses two bits to perform a lookup into a table
/// `b` is little-endian: `b[0]` is LSB.
impl<TargetF: PrimeField, BaseF: PrimeField> TwoBitLookupGadget<BaseF>
    for EmulatedFpVar<TargetF, BaseF>
{
    type TableConstant = TargetF;

    #[tracing::instrument(target = "r1cs")]
    fn two_bit_lookup(b: &[Boolean<BaseF>], c: &[Self::TableConstant]) -> R1CSResult<Self> {
        debug_assert_eq!(b.len(), 2);
        debug_assert_eq!(c.len(), 4);
        if b.cs().is_none() {
            // We're in the constant case

            let lsb = b[0].value()? as usize;
            let msb = b[1].value()? as usize;
            let index = lsb + (msb << 1);
            Ok(Self::Constant(c[index]))
        } else {
            AllocatedEmulatedFpVar::two_bit_lookup(b, c).map(Self::Var)
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> ThreeBitCondNegLookupGadget<BaseF>
    for EmulatedFpVar<TargetF, BaseF>
{
    type TableConstant = TargetF;

    #[tracing::instrument(target = "r1cs")]
    fn three_bit_cond_neg_lookup(
        b: &[Boolean<BaseF>],
        b0b1: &Boolean<BaseF>,
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
            AllocatedEmulatedFpVar::three_bit_cond_neg_lookup(b, b0b1, c).map(Self::Var)
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> AllocVar<TargetF, BaseF>
    for EmulatedFpVar<TargetF, BaseF>
{
    fn new_variable<T: Borrow<TargetF>>(
        cs: impl Into<Namespace<BaseF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> R1CSResult<Self> {
        let ns = cs.into();
        let cs = ns.cs();

        if cs == ConstraintSystemRef::None || mode == AllocationMode::Constant {
            Ok(Self::Constant(*f()?.borrow()))
        } else {
            AllocatedEmulatedFpVar::new_variable(cs, f, mode).map(Self::Var)
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> ToConstraintFieldGadget<BaseF>
    for EmulatedFpVar<TargetF, BaseF>
{
    #[tracing::instrument(target = "r1cs")]
    fn to_constraint_field(&self) -> R1CSResult<Vec<FpVar<BaseF>>> {
        // Use one group element to represent the optimization type.
        //
        // By default, the constant is converted in the weight-optimized type, because
        // it results in fewer elements.
        match self {
            Self::Constant(c) => Ok(AllocatedEmulatedFpVar::get_limbs_representations(
                c,
                OptimizationType::Weight,
            )?
            .into_iter()
            .map(FpVar::constant)
            .collect()),
            Self::Var(v) => v.to_constraint_field(),
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> EmulatedFpVar<TargetF, BaseF> {
    /// The `mul_without_reduce` for `EmulatedFpVar`
    #[tracing::instrument(target = "r1cs")]
    pub fn mul_without_reduce(&self, other: &Self) -> R1CSResult<MulResultVar<TargetF, BaseF>> {
        match self {
            Self::Constant(c) => match other {
                Self::Constant(other_c) => Ok(MulResultVar::Constant(*c * other_c)),
                Self::Var(other_v) => {
                    let self_v =
                        AllocatedEmulatedFpVar::<TargetF, BaseF>::new_constant(self.cs(), c)?;
                    Ok(MulResultVar::Var(other_v.mul_without_reduce(&self_v)?))
                },
            },
            Self::Var(v) => {
                let other_v = match other {
                    Self::Constant(other_c) => {
                        AllocatedEmulatedFpVar::<TargetF, BaseF>::new_constant(self.cs(), other_c)?
                    },
                    Self::Var(other_v) => other_v.clone(),
                };
                Ok(MulResultVar::Var(v.mul_without_reduce(&other_v)?))
            },
        }
    }
}
