use super::{AllocatedMulResultVar, EmulatedFpVar};
use ark_ff::PrimeField;
use ark_relations::r1cs::Result as R1CSResult;

/// An intermediate representation especially for the result of a
/// multiplication, containing more limbs. It is intended for advanced usage to
/// improve the efficiency.
///
/// That is, instead of calling `mul`, one can call `mul_without_reduce` to
/// obtain this intermediate representation, which can still be added.
/// Then, one can call `reduce` to reduce it back to `EmulatedFpVar`.
/// This may help cut the number of reduce operations.
#[derive(Debug)]
#[must_use]
pub enum MulResultVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// as a constant
    Constant(TargetField),
    /// as an allocated gadget
    Var(AllocatedMulResultVar<TargetField, BaseField>),
}

impl<TargetField: PrimeField, BaseField: PrimeField>
    MulResultVar<TargetField, BaseField>
{
    /// Create a zero `MulResultVar` (used for additions)
    pub fn zero() -> Self {
        Self::Constant(TargetField::zero())
    }

    /// Create an `MulResultVar` from a constant
    pub fn constant(v: TargetField) -> Self {
        Self::Constant(v)
    }

    /// Reduce the `MulResultVar` back to EmulatedFpVar
    #[tracing::instrument(target = "r1cs")]
    pub fn reduce(&self) -> R1CSResult<EmulatedFpVar<TargetField, BaseField>> {
        match self {
            Self::Constant(c) => Ok(EmulatedFpVar::Constant(*c)),
            Self::Var(v) => Ok(EmulatedFpVar::Var(v.reduce()?)),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField>
    From<&EmulatedFpVar<TargetField, BaseField>>
    for MulResultVar<TargetField, BaseField>
{
    fn from(src: &EmulatedFpVar<TargetField, BaseField>) -> Self {
        match src {
            EmulatedFpVar::Constant(c) => MulResultVar::Constant(*c),
            EmulatedFpVar::Var(v) => {
                MulResultVar::Var(AllocatedMulResultVar::<
                    TargetField,
                    BaseField,
                >::from(v))
            },
        }
    }
}

impl_bounded_ops!(
    MulResultVar<TargetField, BaseField>,
    TargetField,
    Add,
    add,
    AddAssign,
    add_assign,
    |this: &'a MulResultVar<TargetField, BaseField>, other: &'a MulResultVar<TargetField, BaseField>| {
        use MulResultVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 + c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.add_constant(c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.add(v2).unwrap()),
        }
    },
    |this: &'a MulResultVar<TargetField, BaseField>, other: TargetField| { this + &MulResultVar::Constant(other) },
    (TargetField: PrimeField, BaseField: PrimeField),
);
