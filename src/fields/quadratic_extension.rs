use ark_ff::{
    fields::{Field, QuadExtField, QuadExtParameters},
    Zero,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use core::{borrow::Borrow, marker::PhantomData};

use crate::{
    fields::{fp::FpVar, FieldOpsBounds, FieldVar},
    prelude::*,
    ToConstraintFieldGadget, Vec,
};

use super::FieldExt;

/// This struct is the `R1CS` equivalent of the quadratic extension field type
/// in `ark-ff`, i.e. `ark_ff::QuadExtField`.
#[derive(Derivative)]
#[derivative(
    Debug(bound = "P::BaseField: FieldExt"),
    Clone(bound = "P::BaseField: FieldExt")
)]
#[must_use]
pub struct QuadExtVar<P: QuadExtVarParams>
where
    P::BaseField: FieldExt,
{
    /// The zero-th coefficient of this field element.
    pub c0: BFVar<P>,
    /// The first coefficient of this field element.
    pub c1: BFVar<P>,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

type BFVar<P> = <<P as QuadExtParameters>::BaseField as FieldExt>::Var;

impl<P: QuadExtVarParams> FieldExt for QuadExtField<P> 
where
    P::BaseField: FieldExt,
{
    type Var = QuadExtVar<P>;
}

/// This trait describes parameters that are used to implement arithmetic for
/// `QuadExtVar`.
pub trait QuadExtVarParams: QuadExtParameters
where
    Self::BaseField: FieldExt
{
    /// Multiply the base field of the `QuadExtVar` by the appropriate Frobenius
    /// coefficient. This is equivalent to
    /// `Self::mul_base_field_by_frob_coeff(power)`.
    fn mul_base_field_var_by_frob_coeff(fe: &mut BFVar<Self>, power: usize);
}

impl<P: QuadExtVarParams> QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'a> &'a BFVar<P>: FieldOpsBounds<'a, P::BaseField, BFVar<P>>,
{
    /// Constructs a `QuadExtVar` from the underlying coefficients.
    pub fn new(c0: BFVar<P>, c1: BFVar<P>) -> Self {
        Self {
            c0,
            c1,
            _params: PhantomData,
        }
    }

    /// Multiplies a variable of the base field by the quadratic nonresidue
    /// `P::NONRESIDUE` that is used to construct the extension field.
    #[inline]
    pub fn mul_base_field_by_nonresidue(fe: &BFVar<P>) -> Result<BFVar<P>, SynthesisError> {
        Ok(fe * P::NONRESIDUE)
    }

    /// Multiplies `self` by a constant from the base field.
    #[inline]
    pub fn mul_by_base_field_constant(&self, fe: P::BaseField) -> Self {
        let c0 = self.c0.clone() * fe;
        let c1 = self.c1.clone() * fe;
        QuadExtVar::new(c0, c1)
    }

    /// Sets `self = self.mul_by_base_field_constant(fe)`.
    #[inline]
    pub fn mul_assign_by_base_field_constant(&mut self, fe: P::BaseField) {
        *self = (&*self).mul_by_base_field_constant(fe);
    }

    /// This is only to be used when the element is *known* to be in the
    /// cyclotomic subgroup.
    #[inline]
    pub fn unitary_inverse(&self) -> Result<Self, SynthesisError> {
        Ok(Self::new(self.c0.clone(), self.c1.negate()?))
    }

    /// This is only to be used when the element is *known* to be in the
    /// cyclotomic subgroup.
    #[inline]
    #[tracing::instrument(target = "r1cs", skip(exponent))]
    pub fn cyclotomic_exp(&self, exponent: impl AsRef<[u64]>) -> Result<Self, SynthesisError>
    where
        Self: FieldVar<QuadExtField<P>, P::BasePrimeField>,
    {
        let mut res = Self::one();
        let self_inverse = self.unitary_inverse()?;

        let mut found_nonzero = false;
        let naf = ark_ff::biginteger::arithmetic::find_wnaf(exponent.as_ref());

        for &value in naf.iter().rev() {
            if found_nonzero {
                res.square_in_place()?;
            }

            if value != 0 {
                found_nonzero = true;

                if value > 0 {
                    res *= self;
                } else {
                    res *= &self_inverse;
                }
            }
        }

        Ok(res)
    }
}

impl<P: QuadExtVarParams> R1CSVar<P::BasePrimeField> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'a> &'a BFVar<P>: FieldOpsBounds<'a, P::BaseField, BFVar<P>>,
{
    type Value = QuadExtField<P>;

    fn cs(&self) -> ConstraintSystemRef<P::BasePrimeField> {
        [&self.c0, &self.c1].cs()
    }

    #[inline]
    fn value(&self) -> Result<Self::Value, SynthesisError> {
        match (self.c0.value(), self.c1.value()) {
            (Ok(c0), Ok(c1)) => Ok(QuadExtField::new(c0, c1)),
            (..) => Err(SynthesisError::AssignmentMissing),
        }
    }
}

impl<P: QuadExtVarParams> From<Boolean<P::BasePrimeField>> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'a> &'a BFVar<P>: FieldOpsBounds<'a, P::BaseField, BFVar<P>>,
{
    fn from(other: Boolean<P::BasePrimeField>) -> Self {
        let c0 = BFVar::from(other);
        let c1 = BFVar::zero();
        Self::new(c0, c1)
    }
}

impl<'a, P: QuadExtVarParams> FieldOpsBounds<'a, QuadExtField<P>, QuadExtVar<P>> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>,
{
}

impl<'a, P: QuadExtVarParams> FieldOpsBounds<'a, QuadExtField<P>, QuadExtVar<P>> for &'a QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>,
{
}

impl<P: QuadExtVarParams> FieldVar<QuadExtField<P>, P::BasePrimeField> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'a> &'a BFVar<P>: FieldOpsBounds<'a, P::BaseField, BFVar<P>>,
{
    fn constant(other: QuadExtField<P>) -> Self {
        let c0 = BFVar::constant(other.c0);
        let c1 = BFVar::constant(other.c1);
        Self::new(c0, c1)
    }

    fn zero() -> Self {
        let c0 = BFVar::zero();
        let c1 = BFVar::zero();
        Self::new(c0, c1)
    }

    fn one() -> Self {
        let c0 = BFVar::one();
        let c1 = BFVar::zero();
        Self::new(c0, c1)
    }

    #[inline]
    #[tracing::instrument(target = "r1cs")]
    fn double(&self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.double()?;
        let c1 = self.c1.double()?;
        Ok(Self::new(c0, c1))
    }

    #[inline]
    #[tracing::instrument(target = "r1cs")]
    fn negate(&self) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result.c0.negate_in_place()?;
        result.c1.negate_in_place()?;
        Ok(result)
    }

    #[inline]
    #[tracing::instrument(target = "r1cs")]
    fn square(&self) -> Result<Self, SynthesisError> {
        // From Libsnark/fp2_gadget.tcc
        // Complex multiplication for Fp2:
        //     "Multiplication and Squaring on Pairing-Friendly Fields"
        //     Devegili, OhEigeartaigh, Scott, Dahab

        // v0 = c0 - c1
        let mut v0 = &self.c0 - &self.c1;
        // v3 = c0 - beta * c1
        let v3 = &self.c0 - &Self::mul_base_field_by_nonresidue(&self.c1)?;
        // v2 = c0 * c1
        let v2 = &self.c0 * &self.c1;

        // v0 = (v0 * v3) + v2
        v0 *= &v3;
        v0 += &v2;

        let c0 = &v0 + &Self::mul_base_field_by_nonresidue(&v2)?;
        let c1 = v2.double()?;

        Ok(Self::new(c0, c1))
    }

    #[tracing::instrument(target = "r1cs")]
    fn mul_equals(&self, other: &Self, result: &Self) -> Result<(), SynthesisError> {
        // Karatsuba multiplication for Fp2:
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //     result.c0 = v0 + non_residue * v1
        //     result.c1 = (A.c0 + A.c1) * (B.c0 + B.c1) - v0 - v1
        // Enforced with 3 constraints:
        //     A.c1 * B.c1 = v1
        //     A.c0 * B.c0 = result.c0 - non_residue * v1
        //     (A.c0+A.c1)*(B.c0+B.c1) = result.c1 + result.c0 + (1 - non_residue) * v1
        // Reference:
        // "Multiplication and Squaring on Pairing-Friendly Fields"
        // Devegili, OhEigeartaigh, Scott, Dahab
        // Compute v1
        let v1 = &self.c1 * &other.c1;

        // Perform second check
        let non_residue_times_v1 = Self::mul_base_field_by_nonresidue(&v1)?;
        let rhs = &result.c0 - &non_residue_times_v1;
        self.c0.mul_equals(&other.c0, &rhs)?;

        // Last check
        let a0_plus_a1 = &self.c0 + &self.c1;
        let b0_plus_b1 = &other.c0 + &other.c1;
        let one_minus_non_residue_v1 = &v1 - &non_residue_times_v1;

        let tmp = &(&result.c1 + &result.c0) + &one_minus_non_residue_v1;
        a0_plus_a1.mul_equals(&b0_plus_b1, &tmp)?;

        Ok(())
    }

    #[tracing::instrument(target = "r1cs")]
    fn frobenius_map(&self, power: usize) -> Result<Self, SynthesisError> {
        let mut result = self.clone();
        result.c0.frobenius_map_in_place(power)?;
        result.c1.frobenius_map_in_place(power)?;
        P::mul_base_field_var_by_frob_coeff(&mut result.c1, power);
        Ok(result)
    }

    #[tracing::instrument(target = "r1cs")]
    fn inverse(&self) -> Result<Self, SynthesisError> {
        let mode = if self.is_constant() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let inverse = Self::new_variable(
            self.cs(),
            || {
                self.value()
                    .map(|f| f.inverse().unwrap_or_else(QuadExtField::zero))
            },
            mode,
        )?;
        self.mul_equals(&inverse, &Self::one())?;
        Ok(inverse)
    }
}

impl_bounded_ops!(
    QuadExtVar<P>,
    QuadExtField<P>,
    Add,
    add,
    AddAssign,
    add_assign,
    |this: &'a QuadExtVar<P>, other: &'a QuadExtVar<P>| {
        let c0 = &this.c0 + &other.c0;
        let c1 = &this.c1 + &other.c1;
        QuadExtVar::new(c0, c1)
    },
    |this: &'a QuadExtVar<P>, other: QuadExtField<P>| {
        this + QuadExtVar::constant(other)
    },
    (P: QuadExtVarParams),
    P::BaseField: FieldExt,
    for <'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>
);
impl_bounded_ops!(
    QuadExtVar<P>,
    QuadExtField<P>,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    |this: &'a QuadExtVar<P>, other: &'a QuadExtVar<P>| {
        let c0 = &this.c0 - &other.c0;
        let c1 = &this.c1 - &other.c1;
        QuadExtVar::new(c0, c1)
    },
    |this: &'a QuadExtVar<P>, other: QuadExtField<P>| {
        this - QuadExtVar::constant(other)
    },
    (P: QuadExtVarParams),
    P::BaseField: FieldExt,
    for <'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>
);
impl_bounded_ops!(
    QuadExtVar<P>,
    QuadExtField<P>,
    Mul,
    mul,
    MulAssign,
    mul_assign,
    |this: &'a QuadExtVar<P>, other: &'a QuadExtVar<P>| {
        // Karatsuba multiplication for Fp2:
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //     result.c0 = v0 + non_residue * v1
        //     result.c1 = (A.c0 + A.c1) * (B.c0 + B.c1) - v0 - v1
        // Enforced with 3 constraints:
        //     A.c1 * B.c1 = v1
        //     A.c0 * B.c0 = result.c0 - non_residue * v1
        //     (A.c0+A.c1)*(B.c0+B.c1) = result.c1 + result.c0 + (1 - non_residue) * v1
        // Reference:
        // "Multiplication and Squaring on Pairing-Friendly Fields"
        // Devegili, OhEigeartaigh, Scott, Dahab
        let mut result = this.clone();
        let v0 = &this.c0 * &other.c0;
        let v1 = &this.c1 * &other.c1;

        result.c1 += &this.c0;
        result.c1 *= &other.c0 + &other.c1;
        result.c1 -= &v0;
        result.c1 -= &v1;
        result.c0 = v0 + &QuadExtVar::<P>::mul_base_field_by_nonresidue(&v1).unwrap();
        result
    },
    |this: &'a QuadExtVar<P>, other: QuadExtField<P>| {
        this * QuadExtVar::constant(other)
    },
    (P: QuadExtVarParams),
    P::BaseField: FieldExt,
    for <'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>
);

impl<P> EqGadget<P::BasePrimeField> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>,
    P: QuadExtVarParams,
{
    #[tracing::instrument(target = "r1cs")]
    fn is_eq(&self, other: &Self) -> Result<Boolean<P::BasePrimeField>, SynthesisError> {
        let b0 = self.c0.is_eq(&other.c0)?;
        let b1 = self.c1.is_eq(&other.c1)?;
        b0.and(&b1)
    }

    #[inline]
    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<P::BasePrimeField>,
    ) -> Result<(), SynthesisError> {
        self.c0.conditional_enforce_equal(&other.c0, condition)?;
        self.c1.conditional_enforce_equal(&other.c1, condition)?;
        Ok(())
    }

    #[inline]
    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        condition: &Boolean<P::BasePrimeField>,
    ) -> Result<(), SynthesisError> {
        let is_equal = self.is_eq(other)?;
        is_equal
            .and(condition)?
            .enforce_equal(&Boolean::Constant(false))
    }
}

impl<P: QuadExtVarParams> ToBitsGadget<P::BasePrimeField> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>,
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bits_le(&self) -> Result<Vec<Boolean<P::BasePrimeField>>, SynthesisError> {
        let mut c0 = self.c0.to_bits_le()?;
        let mut c1 = self.c1.to_bits_le()?;
        c0.append(&mut c1);
        Ok(c0)
    }

    #[tracing::instrument(target = "r1cs")]
    fn to_non_unique_bits_le(&self) -> Result<Vec<Boolean<P::BasePrimeField>>, SynthesisError> {
        let mut c0 = self.c0.to_non_unique_bits_le()?;
        let mut c1 = self.c1.to_non_unique_bits_le()?;
        c0.append(&mut c1);
        Ok(c0)
    }
}

impl<P: QuadExtVarParams> ToBytesGadget<P::BasePrimeField> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>,
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bytes(&self) -> Result<Vec<UInt8<P::BasePrimeField>>, SynthesisError> {
        let mut c0 = self.c0.to_bytes()?;
        let mut c1 = self.c1.to_bytes()?;
        c0.append(&mut c1);
        Ok(c0)
    }

    #[tracing::instrument(target = "r1cs")]
    fn to_non_unique_bytes(&self) -> Result<Vec<UInt8<P::BasePrimeField>>, SynthesisError> {
        let mut c0 = self.c0.to_non_unique_bytes()?;
        let mut c1 = self.c1.to_non_unique_bytes()?;
        c0.append(&mut c1);
        Ok(c0)
    }
}

impl<P: QuadExtVarParams> ToConstraintFieldGadget<P::BasePrimeField> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>,
    BFVar<P>: ToConstraintFieldGadget<P::BasePrimeField>,
{
    #[tracing::instrument(target = "r1cs")]
    fn to_constraint_field(&self) -> Result<Vec<FpVar<P::BasePrimeField>>, SynthesisError> {
        let mut res = Vec::new();

        res.extend_from_slice(&self.c0.to_constraint_field()?);
        res.extend_from_slice(&self.c1.to_constraint_field()?);

        Ok(res)
    }
}

impl<P: QuadExtVarParams> CondSelectGadget<P::BasePrimeField> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>,
{
    #[inline]
    fn conditionally_select(
        cond: &Boolean<P::BasePrimeField>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let c0 = BFVar::conditionally_select(cond, &true_value.c0, &false_value.c0)?;
        let c1 = BFVar::conditionally_select(cond, &true_value.c1, &false_value.c1)?;
        Ok(Self::new(c0, c1))
    }
}

impl<P: QuadExtVarParams> TwoBitLookupGadget<P::BasePrimeField> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>,
{
    type TableConstant = QuadExtField<P>;

    #[tracing::instrument(target = "r1cs")]
    fn two_bit_lookup(
        b: &[Boolean<P::BasePrimeField>],
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        let c0s = c.iter().map(|f| f.c0).collect::<Vec<_>>();
        let c1s = c.iter().map(|f| f.c1).collect::<Vec<_>>();
        let c0 = BFVar::two_bit_lookup(b, &c0s)?;
        let c1 = BFVar::two_bit_lookup(b, &c1s)?;
        Ok(Self::new(c0, c1))
    }
}

impl<P: QuadExtVarParams> ThreeBitCondNegLookupGadget<P::BasePrimeField> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>,
{
    type TableConstant = QuadExtField<P>;

    #[tracing::instrument(target = "r1cs")]
    fn three_bit_cond_neg_lookup(
        b: &[Boolean<P::BasePrimeField>],
        b0b1: &Boolean<P::BasePrimeField>,
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        let c0s = c.iter().map(|f| f.c0).collect::<Vec<_>>();
        let c1s = c.iter().map(|f| f.c1).collect::<Vec<_>>();
        let c0 = BFVar::three_bit_cond_neg_lookup(b, b0b1, &c0s)?;
        let c1 = BFVar::three_bit_cond_neg_lookup(b, b0b1, &c1s)?;
        Ok(Self::new(c0, c1))
    }
}


impl<P: QuadExtVarParams> AllocVar<QuadExtField<P>, P::BasePrimeField> for QuadExtVar<P>
where
    P::BaseField: FieldExt,
    for<'b> &'b BFVar<P>: FieldOpsBounds<'b, P::BaseField, BFVar<P>>,
{
    fn new_variable<T: Borrow<QuadExtField<P>>>(
        cs: impl Into<Namespace<P::BasePrimeField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let (c0, c1) = match f() {
            Ok(fe) => (Ok(fe.borrow().c0), Ok(fe.borrow().c1)),
            Err(_) => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let c0 = BFVar::new_variable(ark_relations::ns!(cs, "c0"), || c0, mode)?;
        let c1 = BFVar::new_variable(ark_relations::ns!(cs, "c1"), || c1, mode)?;
        Ok(Self::new(c0, c1))
    }
}
