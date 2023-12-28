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
pub enum MulResultVar<TargetF: PrimeField, BaseF: PrimeField> {
    /// as a constant
    Constant(TargetF),
    /// as an allocated gadget
    Var(AllocatedMulResultVar<TargetF, BaseF>),
}

impl<TargetF: PrimeField, BaseF: PrimeField> MulResultVar<TargetF, BaseF> {
    /// Create a zero `MulResultVar` (used for additions)
    pub fn zero() -> Self {
        Self::Constant(TargetF::zero())
    }

    /// Create an `MulResultVar` from a constant
    pub fn constant(v: TargetF) -> Self {
        Self::Constant(v)
    }

    /// Reduce the `MulResultVar` back to EmulatedFpVar
    #[tracing::instrument(target = "r1cs")]
    pub fn reduce(&self) -> R1CSResult<EmulatedFpVar<TargetF, BaseF>> {
        match self {
            Self::Constant(c) => Ok(EmulatedFpVar::Constant(*c)),
            Self::Var(v) => Ok(EmulatedFpVar::Var(v.reduce()?)),
        }
    }
}

impl<TargetF: PrimeField, BaseF: PrimeField> From<&EmulatedFpVar<TargetF, BaseF>>
    for MulResultVar<TargetF, BaseF>
{
    fn from(src: &EmulatedFpVar<TargetF, BaseF>) -> Self {
        match src {
            EmulatedFpVar::Constant(c) => MulResultVar::Constant(*c),
            EmulatedFpVar::Var(v) => {
                MulResultVar::Var(AllocatedMulResultVar::<TargetF, BaseF>::from(v))
            },
        }
    }
}

impl_bounded_ops!(
    MulResultVar<TargetF, BaseF>,
    TargetF,
    Add,
    add,
    AddAssign,
    add_assign,
    |this: &'a MulResultVar<TargetF, BaseF>, other: &'a MulResultVar<TargetF, BaseF>| {
        use MulResultVar::*;
        match (this, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 + c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.add_constant(c).unwrap()),
            (Var(v1), Var(v2)) => Var(v1.add(v2).unwrap()),
        }
    },
    |this: &'a MulResultVar<TargetF, BaseF>, other: TargetF| { this + &MulResultVar::Constant(other) },
    (TargetF: PrimeField, BaseF: PrimeField),
);
