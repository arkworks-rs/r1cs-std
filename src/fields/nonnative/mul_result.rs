use super::{AllocatedNonNativeFieldMulResultVar, NonNativeFieldVar};
use ark_ff::PrimeField;
use ark_relations::r1cs::Result as R1CSResult;

/// An intermediate representation especially for the result of a
/// multiplication, containing more limbs. It is intended for advanced usage to
/// improve the efficiency.
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

impl<TargetField: PrimeField, BaseField: PrimeField>
    From<&NonNativeFieldVar<TargetField, BaseField>>
    for NonNativeFieldMulResultVar<TargetField, BaseField>
{
    fn from(src: &NonNativeFieldVar<TargetField, BaseField>) -> Self {
        match src {
            NonNativeFieldVar::Constant(c) => NonNativeFieldMulResultVar::Constant(*c),
            NonNativeFieldVar::Var(v) => {
                NonNativeFieldMulResultVar::Var(AllocatedNonNativeFieldMulResultVar::<
                    TargetField,
                    BaseField,
                >::from(v))
            },
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
