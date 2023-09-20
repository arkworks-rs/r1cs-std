use super::{
    params::{DefaultParams, OptimizationType, Params},
    AllocatedNonNativeFieldVar, NonNativeFieldMulResultVar,
};
use crate::{
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
    prelude::*,
    R1CSVar, ToConstraintFieldGadget,
};
use ark_ff::{BigInteger, PrimeField};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, Result as R1CSResult, SynthesisError};
use ark_std::{
    borrow::Borrow,
    hash::{Hash, Hasher},
    vec::Vec,
};

/// A gadget for representing non-native (`TargetField`) field elements over the
/// constraint field (`BaseField`).
#[derive(Derivative)]
#[derivative(Debug, Clone(bound = "TargetField: Clone, BaseField: Clone"))]
#[must_use]
pub enum NonNativeFieldVar<
    TargetField: PrimeField,
    BaseField: PrimeField,
    P: Params = DefaultParams,
> {
    /// Constant
    Constant(TargetField),
    /// Allocated gadget
    Var(AllocatedNonNativeFieldVar<TargetField, BaseField, P>),
}

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> PartialEq
    for NonNativeFieldVar<TargetField, BaseField, P>
{
    fn eq(&self, other: &Self) -> bool {
        self.value()
            .unwrap_or_default()
            .eq(&other.value().unwrap_or_default())
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> Eq
    for NonNativeFieldVar<TargetField, BaseField, P>
{
}

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> Hash
    for NonNativeFieldVar<TargetField, BaseField, P>
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value().unwrap_or_default().hash(state);
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> R1CSVar<BaseField>
    for NonNativeFieldVar<TargetField, BaseField, P>
{
    type Value = TargetField;

    fn cs(&self) -> ConstraintSystemRef<BaseField> {
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

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> From<Boolean<BaseField>>
    for NonNativeFieldVar<TargetField, BaseField, P>
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

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params>
    From<AllocatedNonNativeFieldVar<TargetField, BaseField, P>>
    for NonNativeFieldVar<TargetField, BaseField, P>
{
    fn from(other: AllocatedNonNativeFieldVar<TargetField, BaseField, P>) -> Self {
        Self::Var(other)
    }
}

impl<'a, TargetField: PrimeField, BaseField: PrimeField, P: Params>
    FieldOpsBounds<'a, TargetField, Self> for NonNativeFieldVar<TargetField, BaseField, P>
{
}

impl<'a, TargetField: PrimeField, BaseField: PrimeField, P: Params>
    FieldOpsBounds<'a, TargetField, NonNativeFieldVar<TargetField, BaseField, P>>
    for &'a NonNativeFieldVar<TargetField, BaseField, P>
{
}

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> FieldVar<TargetField, BaseField>
    for NonNativeFieldVar<TargetField, BaseField, P>
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
                tmp.frobenius_map_in_place(power);
                tmp
            })),
            Self::Var(v) => Ok(Self::Var(v.frobenius_map(power)?)),
        }
    }
}

impl_bounded_ops!(
    NonNativeFieldVar<TargetField, BaseField, P>,
    TargetField,
    Add,
    add,
    AddAssign,
    add_assign,
    |this: &'a NonNativeFieldVar<TargetField, BaseField, P>, other: &'a NonNativeFieldVar<TargetField, BaseField, P>| {
        use NonNativeFieldVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 + c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.add_constant(c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.add(v2).unwrap()),
        }
    },
    |this: &'a NonNativeFieldVar<TargetField, BaseField, P>, other: TargetField| { this + &NonNativeFieldVar::Constant(other) },
    (TargetField: PrimeField, BaseField: PrimeField, P: Params),
);

impl_bounded_ops!(
    NonNativeFieldVar<TargetField, BaseField, P>,
    TargetField,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    |this: &'a NonNativeFieldVar<TargetField, BaseField, P>, other: &'a NonNativeFieldVar<TargetField, BaseField, P>| {
        use NonNativeFieldVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 - c2),
            (Var(v), Constant(c)) => Var(v.sub_constant(c).unwrap()),
            (Constant(c), Var(v)) => Var(v.sub_constant(c).unwrap().negate().unwrap()),
            (Var(v1), Var(v2)) => Var(v1.sub(v2).unwrap()),
        }
    },
    |this: &'a NonNativeFieldVar<TargetField, BaseField, P>, other: TargetField| {
        this - &NonNativeFieldVar::Constant(other)
    },
    (TargetField: PrimeField, BaseField: PrimeField, P: Params),
);

impl_bounded_ops!(
    NonNativeFieldVar<TargetField, BaseField, P>,
    TargetField,
    Mul,
    mul,
    MulAssign,
    mul_assign,
    |this: &'a NonNativeFieldVar<TargetField, BaseField, P>, other: &'a NonNativeFieldVar<TargetField, BaseField, P>| {
        use NonNativeFieldVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 * c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.mul_constant(c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.mul(v2).unwrap()),
        }
    },
    |this: &'a NonNativeFieldVar<TargetField, BaseField, P>, other: TargetField| {
        if other.is_zero() {
            NonNativeFieldVar::zero()
        } else {
            this * &NonNativeFieldVar::Constant(other)
        }
    },
    (TargetField: PrimeField, BaseField: PrimeField, P: Params),
);

/// *************************************************************************
/// *************************************************************************

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> EqGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField, P>
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
            },
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let cs = v.cs();
                let c = AllocatedNonNativeFieldVar::new_constant(cs, c)?;
                c.conditional_enforce_equal(v, should_enforce)
            },
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
            },
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let cs = v.cs();
                let c = AllocatedNonNativeFieldVar::new_constant(cs, c)?;
                c.conditional_enforce_not_equal(v, should_enforce)
            },
            (Self::Var(v1), Self::Var(v2)) => v1.conditional_enforce_not_equal(v2, should_enforce),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> ToBitsGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField, P>
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
            Self::Constant(c) => Ok(BitIteratorLE::new(&c.into_bigint())
                .take((TargetField::MODULUS_BIT_SIZE) as usize)
                .map(Boolean::constant)
                .collect::<Vec<_>>()),
            Self::Var(v) => v.to_non_unique_bits_le(),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> ToBytesGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField, P>
{
    /// Outputs the unique byte decomposition of `self` in *little-endian*
    /// form.
    #[tracing::instrument(target = "r1cs")]
    fn to_bytes(&self) -> R1CSResult<Vec<UInt8<BaseField>>> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(
                c.into_bigint().to_bytes_le().as_slice(),
            )),

            Self::Var(v) => v.to_bytes(),
        }
    }

    #[tracing::instrument(target = "r1cs")]
    fn to_non_unique_bytes(&self) -> R1CSResult<Vec<UInt8<BaseField>>> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(
                c.into_bigint().to_bytes_le().as_slice(),
            )),
            Self::Var(v) => v.to_non_unique_bytes(),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> CondSelectGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField, P>
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
            },
        }
    }
}

/// Uses two bits to perform a lookup into a table
/// `b` is little-endian: `b[0]` is LSB.
impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> TwoBitLookupGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField, P>
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

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params>
    ThreeBitCondNegLookupGadget<BaseField> for NonNativeFieldVar<TargetField, BaseField, P>
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

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> AllocVar<TargetField, BaseField>
    for NonNativeFieldVar<TargetField, BaseField, P>
{
    fn new_variable<T: Borrow<TargetField>>(
        cs: impl Into<Namespace<BaseField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> R1CSResult<Self> {
        let ns = cs.into();
        let cs = ns.cs();

        if cs == ConstraintSystemRef::None || mode == AllocationMode::Constant {
            Ok(Self::Constant(*f()?.borrow()))
        } else {
            AllocatedNonNativeFieldVar::new_variable(cs, f, mode).map(Self::Var)
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params> ToConstraintFieldGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField, P>
{
    #[tracing::instrument(target = "r1cs")]
    fn to_constraint_field(&self) -> R1CSResult<Vec<FpVar<BaseField>>> {
        // Use one group element to represent the optimization type.
        //
        // By default, the constant is converted in the weight-optimized type, because
        // it results in fewer elements.
        match self {
            Self::Constant(c) => Ok(
                AllocatedNonNativeFieldVar::<TargetField, BaseField, P>::get_limbs_representations(
                    c,
                    OptimizationType::Weight,
                )?
                .into_iter()
                .map(FpVar::constant)
                .collect(),
            ),
            Self::Var(v) => v.to_constraint_field(),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField, P: Params>
    NonNativeFieldVar<TargetField, BaseField, P>
{
    /// The `mul_without_reduce` for `NonNativeFieldVar`
    #[tracing::instrument(target = "r1cs")]
    pub fn mul_without_reduce(
        &self,
        other: &Self,
    ) -> R1CSResult<NonNativeFieldMulResultVar<TargetField, BaseField, P>> {
        match self {
            Self::Constant(c) => match other {
                Self::Constant(other_c) => Ok(NonNativeFieldMulResultVar::Constant(*c * other_c)),
                Self::Var(other_v) => {
                    let self_v =
                        AllocatedNonNativeFieldVar::<TargetField, BaseField, P>::new_constant(
                            self.cs(),
                            c,
                        )?;
                    Ok(NonNativeFieldMulResultVar::Var(
                        other_v.mul_without_reduce(&self_v)?,
                    ))
                },
            },
            Self::Var(v) => {
                let other_v = match other {
                    Self::Constant(other_c) => {
                        AllocatedNonNativeFieldVar::<TargetField, BaseField, P>::new_constant(
                            self.cs(),
                            other_c,
                        )?
                    },
                    Self::Var(other_v) => other_v.clone(),
                };
                Ok(NonNativeFieldMulResultVar::Var(
                    v.mul_without_reduce(&other_v)?,
                ))
            },
        }
    }
}
