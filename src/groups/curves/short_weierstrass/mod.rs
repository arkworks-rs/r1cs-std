use ark_ec::{
    short_weierstrass_jacobian::{GroupAffine as SWAffine, GroupProjective as SWProjective},
    AffineCurve, ProjectiveCurve, SWModelParameters,
};
use ark_ff::{BigInteger, BitIteratorBE, Field, One, PrimeField, Zero};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use core::{borrow::Borrow, marker::PhantomData};
use non_zero_affine::NonZeroAffineVar;

use crate::{fields::fp::FpVar, prelude::*, ToConstraintFieldGadget, Vec};

/// This module provides a generic implementation of G1 and G2 for
/// the [\[BLS12]\](<https://eprint.iacr.org/2002/088.pdf>) family of bilinear groups.
pub mod bls12;

/// This module provides a generic implementation of G1 and G2 for
/// the [\[MNT4]\](<https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.20.8113&rep=rep1&type=pdf>)
///  family of bilinear groups.
pub mod mnt4;
/// This module provides a generic implementation of G1 and G2 for
/// the [\[MNT6]\](<https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.20.8113&rep=rep1&type=pdf>)
///  family of bilinear groups.
pub mod mnt6;

mod non_zero_affine;
/// An implementation of arithmetic for Short Weierstrass curves that relies on
/// the complete formulae derived in the paper of
/// [[Renes, Costello, Batina 2015]](<https://eprint.iacr.org/2015/1060>).
#[derive(Derivative)]
#[derivative(Debug, Clone)]
#[must_use]
pub struct ProjectiveVar<
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
> where
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    /// The x-coordinate.
    pub x: F,
    /// The y-coordinate.
    pub y: F,
    /// The z-coordinate.
    pub z: F,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

/// An affine representation of a curve point.
#[derive(Derivative)]
#[derivative(Debug, Clone)]
#[must_use]
pub struct AffineVar<
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
> where
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    /// The x-coordinate.
    pub x: F,
    /// The y-coordinate.
    pub y: F,
    /// Is `self` the point at infinity.
    pub infinity: Boolean<<P::BaseField as Field>::BasePrimeField>,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

impl<P, F> AffineVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    fn new(x: F, y: F, infinity: Boolean<<P::BaseField as Field>::BasePrimeField>) -> Self {
        Self {
            x,
            y,
            infinity,
            _params: PhantomData,
        }
    }

    /// Returns the value assigned to `self` in the underlying
    /// constraint system.
    pub fn value(&self) -> Result<SWAffine<P>, SynthesisError> {
        Ok(SWAffine::new(
            self.x.value()?,
            self.y.value()?,
            self.infinity.value()?,
        ))
    }
}

impl<P, F> ToConstraintFieldGadget<<P::BaseField as Field>::BasePrimeField> for AffineVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
    F: ToConstraintFieldGadget<<P::BaseField as Field>::BasePrimeField>,
{
    fn to_constraint_field(
        &self,
    ) -> Result<Vec<FpVar<<P::BaseField as Field>::BasePrimeField>>, SynthesisError> {
        let mut res = Vec::<FpVar<<P::BaseField as Field>::BasePrimeField>>::new();

        res.extend_from_slice(&self.x.to_constraint_field()?);
        res.extend_from_slice(&self.y.to_constraint_field()?);
        res.extend_from_slice(&self.infinity.to_constraint_field()?);

        Ok(res)
    }
}

impl<P, F> R1CSVar<<P::BaseField as Field>::BasePrimeField> for ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    type Value = SWProjective<P>;

    fn cs(&self) -> ConstraintSystemRef<<P::BaseField as Field>::BasePrimeField> {
        self.x.cs().or(self.y.cs()).or(self.z.cs())
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let (x, y, z) = (self.x.value()?, self.y.value()?, self.z.value()?);
        let result = if let Some(z_inv) = z.inverse() {
            SWAffine::new(x * &z_inv, y * &z_inv, false)
        } else {
            SWAffine::zero()
        };
        Ok(result.into())
    }
}

impl<P: SWModelParameters, F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>>
    ProjectiveVar<P, F>
where
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    /// Constructs `Self` from an `(x, y, z)` coordinate triple.
    pub fn new(x: F, y: F, z: F) -> Self {
        Self {
            x,
            y,
            z,
            _params: PhantomData,
        }
    }

    /// Convert this point into affine form.
    #[tracing::instrument(target = "r1cs")]
    pub fn to_affine(&self) -> Result<AffineVar<P, F>, SynthesisError> {
        if self.is_constant() {
            let point = self.value()?.into_affine();
            let x = F::new_constant(ConstraintSystemRef::None, point.x)?;
            let y = F::new_constant(ConstraintSystemRef::None, point.y)?;
            let infinity = Boolean::constant(point.infinity);
            Ok(AffineVar::new(x, y, infinity))
        } else {
            let cs = self.cs();
            let infinity = self.is_zero()?;
            let zero_x = F::zero();
            let zero_y = F::one();
            // Allocate a variable whose value is either `self.z.inverse()` if the inverse exists,
            // and is zero otherwise.
            let z_inv = F::new_witness(ark_relations::ns!(cs, "z_inverse"), || {
                Ok(self.z.value()?.inverse().unwrap_or_else(P::BaseField::zero))
            })?;
            // The inverse exists if `!self.is_zero()`.
            // This means that `z_inv * self.z = 1` if `self.is_not_zero()`, and
            //                 `z_inv * self.z = 0` if `self.is_zero()`.
            //
            // Thus, `z_inv * self.z = !self.is_zero()`.
            z_inv.mul_equals(&self.z, &F::from(infinity.not()))?;

            let non_zero_x = &self.x * &z_inv;
            let non_zero_y = &self.y * &z_inv;

            let x = infinity.select(&zero_x, &non_zero_x)?;
            let y = infinity.select(&zero_y, &non_zero_y)?;

            Ok(AffineVar::new(x, y, infinity))
        }
    }

    /// Allocates a new variable without performing an on-curve check, which is
    /// useful if the variable is known to be on the curve (eg., if the point
    /// is a constant or is a public input).
    #[tracing::instrument(target = "r1cs", skip(cs, f))]
    pub fn new_variable_omit_on_curve_check(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<SWProjective<P>, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();

        let (x, y, z) = match f() {
            Ok(ge) => {
                let ge = ge.into_affine();
                if ge.is_zero() {
                    (
                        Ok(P::BaseField::zero()),
                        Ok(P::BaseField::one()),
                        Ok(P::BaseField::zero()),
                    )
                } else {
                    (Ok(ge.x), Ok(ge.y), Ok(P::BaseField::one()))
                }
            }
            _ => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let x = F::new_variable(ark_relations::ns!(cs, "x"), || x, mode)?;
        let y = F::new_variable(ark_relations::ns!(cs, "y"), || y, mode)?;
        let z = F::new_variable(ark_relations::ns!(cs, "z"), || z, mode)?;

        Ok(Self::new(x, y, z))
    }

    /// Mixed addition, which is useful when `other = (x2, y2)` is known to have z = 1.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    pub(crate) fn add_mixed(&self, other: &NonZeroAffineVar<P, F>) -> Result<Self, SynthesisError> {
        // Complete mixed addition formula from Renes-Costello-Batina 2015
        // Algorithm 2
        // (https://eprint.iacr.org/2015/1060).
        // Below, comments at the end of a line denote the corresponding
        // step(s) of the algorithm
        //
        // Adapted from code in
        // https://github.com/RustCrypto/elliptic-curves/blob/master/p256/src/arithmetic/projective.rs
        let three_b = P::COEFF_B.double() + &P::COEFF_B;
        let (x1, y1, z1) = (&self.x, &self.y, &self.z);
        let (x2, y2) = (&other.x, &other.y);

        let xx = x1 * x2; // 1
        let yy = y1 * y2; // 2
        let xy_pairs = ((x1 + y1) * &(x2 + y2)) - (&xx + &yy); // 4, 5, 6, 7, 8
        let xz_pairs = (x2 * z1) + x1; // 8, 9
        let yz_pairs = (y2 * z1) + y1; // 10, 11

        let axz = mul_by_coeff_a::<P, F>(&xz_pairs); // 12

        let bz3_part = &axz + z1 * three_b; // 13, 14

        let yy_m_bz3 = &yy - &bz3_part; // 15
        let yy_p_bz3 = &yy + &bz3_part; // 16

        let azz = mul_by_coeff_a::<P, F>(z1); // 20
        let xx3_p_azz = xx.double().unwrap() + &xx + &azz; // 18, 19, 22

        let bxz3 = &xz_pairs * three_b; // 21
        let b3_xz_pairs = mul_by_coeff_a::<P, F>(&(&xx - &azz)) + &bxz3; // 23, 24, 25

        let x = (&yy_m_bz3 * &xy_pairs) - &yz_pairs * &b3_xz_pairs; // 28,29, 30
        let y = (&yy_p_bz3 * &yy_m_bz3) + &xx3_p_azz * b3_xz_pairs; // 17, 26, 27
        let z = (&yy_p_bz3 * &yz_pairs) + xy_pairs * xx3_p_azz; // 31, 32, 33

        Ok(ProjectiveVar::new(x, y, z))
    }

    /// Computes a scalar multiplication with a little-endian scalar of size `P::ScalarField::MODULUS_BITS`.
    #[tracing::instrument(
        target = "r1cs",
        skip(self, mul_result, multiple_of_power_of_two, bits)
    )]
    fn fixed_scalar_mul_le(
        &self,
        mul_result: &mut Self,
        multiple_of_power_of_two: &mut NonZeroAffineVar<P, F>,
        bits: &[&Boolean<<P::BaseField as Field>::BasePrimeField>],
    ) -> Result<(), SynthesisError> {
        let scalar_modulus_bits = <P::ScalarField as PrimeField>::size_in_bits();

        assert!(scalar_modulus_bits >= bits.len());
        let split_len = ark_std::cmp::min(scalar_modulus_bits - 2, bits.len());
        let (affine_bits, proj_bits) = bits.split_at(split_len);
        // Computes the standard little-endian double-and-add algorithm
        // (Algorithm 3.26, Guide to Elliptic Curve Cryptography)
        //
        // We rely on *incomplete* affine formulae for partially computing this.
        // However, we avoid exceptional edge cases because we partition the scalar
        // into two chunks: one guaranteed to be less than p - 2, and the rest.
        // We only use incomplete formulae for the first chunk, which means we avoid exceptions:
        //
        // `add_unchecked(a, b)` is incomplete when either `b.is_zero()`, or when
        // `b = ±a`. During scalar multiplication, we don't hit either case:
        // * `b = ±a`: `b = accumulator = k * a`, where `2 <= k < p - 1`.
        //   This implies that `k != p ± 1`, and so `b != (p ± 1) * a`.
        //   Because the group is finite, this in turn means that `b != ±a`, as required.
        // * `a` or `b` is zero: for `a`, we handle the zero case after the loop; for `b`, notice
        //    that it is monotonically increasing, and furthermore, equals `k * a`, where
        //    `k != p = 0 mod p`.

        // Unlike normal double-and-add, here we start off with a non-zero `accumulator`,
        // because `NonZeroAffineVar::add_unchecked` doesn't support addition with `zero`.
        // In more detail, we initialize `accumulator` to be the initial value of
        // `multiple_of_power_of_two`. This ensures that all unchecked additions of `accumulator`
        // with later values of `multiple_of_power_of_two` are safe.
        // However, to do this correctly, we need to perform two steps:
        // * We must skip the LSB, and instead proceed assuming that it was 1. Later, we will
        //   conditionally subtract the initial value of `accumulator`:
        //     if LSB == 0: subtract initial_acc_value; else, subtract 0.
        // * Because we are assuming the first bit, we must double `multiple_of_power_of_two`.

        let mut accumulator = multiple_of_power_of_two.clone();
        let initial_acc_value = accumulator.into_projective();

        // The powers start at 2 (instead of 1) because we're skipping the first bit.
        multiple_of_power_of_two.double_in_place()?;

        // As mentioned, we will skip the LSB, and will later handle it via a conditional subtraction.
        for bit in affine_bits.iter().skip(1) {
            if bit.is_constant() {
                if *bit == &Boolean::TRUE {
                    accumulator = accumulator.add_unchecked(&multiple_of_power_of_two)?;
                }
            } else {
                let temp = accumulator.add_unchecked(&multiple_of_power_of_two)?;
                accumulator = bit.select(&temp, &accumulator)?;
            }
            multiple_of_power_of_two.double_in_place()?;
        }
        // Perform conditional subtraction:

        // We can convert to projective safely because the result is guaranteed to be non-zero
        // by the condition on `affine_bits.len()`, and by the fact that `accumulator` is non-zero
        let result = accumulator.into_projective();
        // If bits[0] is 0, then we have to subtract `self`; else, we subtract zero.
        let subtrahend = bits[0].select(&Self::zero(), &initial_acc_value)?;
        *mul_result += result - subtrahend;

        // Now, let's finish off the rest of the bits using our complete formulae
        for bit in proj_bits {
            if bit.is_constant() {
                if *bit == &Boolean::TRUE {
                    *mul_result += &multiple_of_power_of_two.into_projective();
                }
            } else {
                let temp = &*mul_result + &multiple_of_power_of_two.into_projective();
                *mul_result = bit.select(&temp, &mul_result)?;
            }
            multiple_of_power_of_two.double_in_place()?;
        }
        Ok(())
    }
}

impl<P, F> CurveVar<SWProjective<P>, <P::BaseField as Field>::BasePrimeField>
    for ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    fn constant(g: SWProjective<P>) -> Self {
        let cs = ConstraintSystemRef::None;
        Self::new_variable_omit_on_curve_check(cs, || Ok(g), AllocationMode::Constant).unwrap()
    }

    fn zero() -> Self {
        Self::new(F::zero(), F::one(), F::zero())
    }

    fn is_zero(&self) -> Result<Boolean<<P::BaseField as Field>::BasePrimeField>, SynthesisError> {
        self.z.is_zero()
    }

    #[tracing::instrument(target = "r1cs", skip(cs, f))]
    fn new_variable_omit_prime_order_check(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<SWProjective<P>, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        // Curve equation in projective form:
        // E: Y² * Z = X³ + aX * Z² + bZ³
        //
        // This can be re-written as
        // E: Y² * Z - bZ³ = X³ + aX * Z²
        // E: Z * (Y² - bZ²) = X * (X² + aZ²)
        // so, compute X², Y², Z²,
        //     compute temp = X * (X² + aZ²)
        //     check Z.mul_equals((Y² - bZ²), temp)
        //
        //     A total of 5 multiplications

        let g = Self::new_variable_omit_on_curve_check(cs, f, mode)?;

        if mode != AllocationMode::Constant {
            // Perform on-curve check.
            let b = P::COEFF_B;
            let a = P::COEFF_A;

            let x2 = g.x.square()?;
            let y2 = g.y.square()?;
            let z2 = g.z.square()?;
            let t = &g.x * (x2 + &z2 * a);

            g.z.mul_equals(&(y2 - z2 * b), &t)?;
        }
        Ok(g)
    }

    /// Enforce that `self` is in the prime-order subgroup.
    ///
    /// Does so by multiplying by the prime order, and checking that the result
    /// is unchanged.
    // TODO: at the moment this doesn't work, because the addition and doubling
    // formulae are incomplete for even-order points.
    #[tracing::instrument(target = "r1cs")]
    fn enforce_prime_order(&self) -> Result<(), SynthesisError> {
        unimplemented!("cannot enforce prime order");
        // let r_minus_1 = (-P::ScalarField::one()).into_repr();

        // let mut result = Self::zero();
        // for b in BitIteratorBE::without_leading_zeros(r_minus_1) {
        //     result.double_in_place()?;

        //     if b {
        //         result += self;
        //     }
        // }
        // self.negate()?.enforce_equal(&result)?;
        // Ok(())
    }

    #[inline]
    #[tracing::instrument(target = "r1cs")]
    fn double_in_place(&mut self) -> Result<(), SynthesisError> {
        // Complete doubling formula from Renes-Costello-Batina 2015
        // Algorithm 3
        // (https://eprint.iacr.org/2015/1060).
        // Below, comments at the end of a line denote the corresponding
        // step(s) of the algorithm
        //
        // Adapted from code in
        // https://github.com/RustCrypto/elliptic-curves/blob/master/p256/src/arithmetic/projective.rs
        let three_b = P::COEFF_B.double() + &P::COEFF_B;

        let xx = self.x.square()?; // 1
        let yy = self.y.square()?; // 2
        let zz = self.z.square()?; // 3
        let xy2 = (&self.x * &self.y).double()?; // 4, 5
        let xz2 = (&self.x * &self.z).double()?; // 6, 7

        let axz2 = mul_by_coeff_a::<P, F>(&xz2); // 8

        let bzz3_part = &axz2 + &zz * three_b; // 9, 10
        let yy_m_bzz3 = &yy - &bzz3_part; // 11
        let yy_p_bzz3 = &yy + &bzz3_part; // 12
        let y_frag = yy_p_bzz3 * &yy_m_bzz3; // 13
        let x_frag = yy_m_bzz3 * &xy2; // 14

        let bxz3 = xz2 * three_b; // 15
        let azz = mul_by_coeff_a::<P, F>(&zz); // 16
        let b3_xz_pairs = mul_by_coeff_a::<P, F>(&(&xx - &azz)) + &bxz3; // 15, 16, 17, 18, 19
        let xx3_p_azz = (xx.double()? + &xx + &azz) * &b3_xz_pairs; // 23, 24, 25

        let y = y_frag + &xx3_p_azz; // 26, 27
        let yz2 = (&self.y * &self.z).double()?; // 28, 29
        let x = x_frag - &(b3_xz_pairs * &yz2); // 30, 31
        let z = (yz2 * &yy).double()?.double()?; // 32, 33, 34
        self.x = x;
        self.y = y;
        self.z = z;
        Ok(())
    }

    #[tracing::instrument(target = "r1cs")]
    fn negate(&self) -> Result<Self, SynthesisError> {
        Ok(Self::new(self.x.clone(), self.y.negate()?, self.z.clone()))
    }

    /// Computes `bits * self`, where `bits` is a little-endian
    /// `Boolean` representation of a scalar.
    #[tracing::instrument(target = "r1cs", skip(bits))]
    fn scalar_mul_le<'a>(
        &self,
        bits: impl Iterator<Item = &'a Boolean<<P::BaseField as Field>::BasePrimeField>>,
    ) -> Result<Self, SynthesisError> {
        if self.is_constant() {
            if self.value().unwrap().is_zero() {
                return Ok(self.clone());
            }
        }
        let self_affine = self.to_affine()?;
        let (x, y, infinity) = (self_affine.x, self_affine.y, self_affine.infinity);
        // We first handle the non-zero case, and then later
        // will conditionally select zero if `self` was zero.
        let non_zero_self = NonZeroAffineVar::new(x, y);

        let mut bits = bits.collect::<Vec<_>>();
        if bits.len() == 0 {
            return Ok(Self::zero());
        }
        // Remove unnecessary constant zeros in the most-significant positions.
        bits = bits
            .into_iter()
            // We iterate from the MSB down.
            .rev()
            // Skip leading zeros, if they are constants.
            .skip_while(|b| b.is_constant() && (b.value().unwrap() == false))
            .collect();
        // After collecting we are in big-endian form; we have to reverse to get back to
        // little-endian.
        bits.reverse();

        let scalar_modulus_bits = <P::ScalarField as PrimeField>::size_in_bits();
        let mut mul_result = Self::zero();
        let mut power_of_two_times_self = non_zero_self;
        // We chunk up `bits` into `p`-sized chunks.
        for bits in bits.chunks(scalar_modulus_bits) {
            self.fixed_scalar_mul_le(&mut mul_result, &mut power_of_two_times_self, bits)?;
        }

        // The foregoing algorithm relies on incomplete addition, and so does not
        // work when the input (`self`) is zero. We hence have to perform
        // a check to ensure that if the input is zero, then so is the output.
        // The cost of this check should be less than the benefit of using
        // mixed addition in almost all cases.
        infinity.select(&Self::zero(), &mul_result)
    }

    #[tracing::instrument(target = "r1cs", skip(scalar_bits_with_bases))]
    fn precomputed_base_scalar_mul_le<'a, I, B>(
        &mut self,
        scalar_bits_with_bases: I,
    ) -> Result<(), SynthesisError>
    where
        I: Iterator<Item = (B, &'a SWProjective<P>)>,
        B: Borrow<Boolean<<P::BaseField as Field>::BasePrimeField>>,
    {
        // We just ignore the provided bases and use the faster scalar multiplication.
        let (bits, bases): (Vec<_>, Vec<_>) = scalar_bits_with_bases
            .map(|(b, c)| (b.borrow().clone(), *c))
            .unzip();
        let base = bases[0];
        *self = Self::constant(base).scalar_mul_le(bits.iter())?;
        Ok(())
    }
}

impl<P, F> ToConstraintFieldGadget<<P::BaseField as Field>::BasePrimeField> for ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
    F: ToConstraintFieldGadget<<P::BaseField as Field>::BasePrimeField>,
{
    fn to_constraint_field(
        &self,
    ) -> Result<Vec<FpVar<<P::BaseField as Field>::BasePrimeField>>, SynthesisError> {
        self.to_affine()?.to_constraint_field()
    }
}

fn mul_by_coeff_a<
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
>(
    f: &F,
) -> F
where
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    if !P::COEFF_A.is_zero() {
        f * P::COEFF_A
    } else {
        F::zero()
    }
}

impl_bounded_ops!(
    ProjectiveVar<P, F>,
    SWProjective<P>,
    Add,
    add,
    AddAssign,
    add_assign,
    |mut this: &'a ProjectiveVar<P, F>, mut other: &'a ProjectiveVar<P, F>| {
        // Implement complete addition for Short Weierstrass curves, following
        // the complete addition formula from Renes-Costello-Batina 2015
        // (https://eprint.iacr.org/2015/1060).
        //
        // We special case handling of constants to get better constraint weight.
        if this.is_constant() {
            // we'll just act like `other` is constant.
            core::mem::swap(&mut this, &mut other);
        }

        if other.is_constant() {
            // The value should exist because `other` is a constant.
            let other = other.value().unwrap();
            if other.is_zero() {
                // this + 0 = this
                this.clone()
            } else {
                // We'll use mixed addition to add non-zero constants.
                let x = F::constant(other.x);
                let y = F::constant(other.y);
                this.add_mixed(&NonZeroAffineVar::new(x, y)).unwrap()
            }
        } else {
            // Complete addition formula from Renes-Costello-Batina 2015
            // Algorithm 1
            // (https://eprint.iacr.org/2015/1060).
            // Below, comments at the end of a line denote the corresponding
            // step(s) of the algorithm
            //
            // Adapted from code in
            // https://github.com/RustCrypto/elliptic-curves/blob/master/p256/src/arithmetic/projective.rs
            let three_b = P::COEFF_B.double() + &P::COEFF_B;
            let (x1, y1, z1) = (&this.x, &this.y, &this.z);
            let (x2, y2, z2) = (&other.x, &other.y, &other.z);

            let xx = x1 * x2; // 1
            let yy = y1 * y2; // 2
            let zz = z1 * z2; // 3
            let xy_pairs = ((x1 + y1) * &(x2 + y2)) - (&xx + &yy); // 4, 5, 6, 7, 8
            let xz_pairs = ((x1 + z1) * &(x2 + z2)) - (&xx + &zz); // 9, 10, 11, 12, 13
            let yz_pairs = ((y1 + z1) * &(y2 + z2)) - (&yy + &zz); // 14, 15, 16, 17, 18

            let axz = mul_by_coeff_a::<P, F>(&xz_pairs); // 19

            let bzz3_part = &axz + &zz * three_b; // 20, 21

            let yy_m_bzz3 = &yy - &bzz3_part; // 22
            let yy_p_bzz3 = &yy + &bzz3_part; // 23

            let azz = mul_by_coeff_a::<P, F>(&zz);
            let xx3_p_azz = xx.double().unwrap() + &xx + &azz; // 25, 26, 27, 29

            let bxz3 = &xz_pairs * three_b; // 28
            let b3_xz_pairs = mul_by_coeff_a::<P, F>(&(&xx - &azz)) + &bxz3; // 30, 31, 32

            let x = (&yy_m_bzz3 * &xy_pairs) - &yz_pairs * &b3_xz_pairs; // 35, 39, 40
            let y = (&yy_p_bzz3 * &yy_m_bzz3) + &xx3_p_azz * b3_xz_pairs; // 24, 36, 37, 38
            let z = (&yy_p_bzz3 * &yz_pairs) + xy_pairs * xx3_p_azz; // 41, 42, 43

            ProjectiveVar::new(x, y, z)
        }

    },
    |this: &'a ProjectiveVar<P, F>, other: SWProjective<P>| {
        this + ProjectiveVar::constant(other)
    },
    (F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>, P: SWModelParameters),
    for <'b> &'b F: FieldOpsBounds<'b, P::BaseField, F>,
);

impl_bounded_ops!(
    ProjectiveVar<P, F>,
    SWProjective<P>,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    |this: &'a ProjectiveVar<P, F>, other: &'a ProjectiveVar<P, F>| this + other.negate().unwrap(),
    |this: &'a ProjectiveVar<P, F>, other: SWProjective<P>| this - ProjectiveVar::constant(other),
    (F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>, P: SWModelParameters),
    for <'b> &'b F: FieldOpsBounds<'b, P::BaseField, F>
);

impl<'a, P, F> GroupOpsBounds<'a, SWProjective<P>, ProjectiveVar<P, F>> for ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'b> &'b F: FieldOpsBounds<'b, P::BaseField, F>,
{
}

impl<'a, P, F> GroupOpsBounds<'a, SWProjective<P>, ProjectiveVar<P, F>> for &'a ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'b> &'b F: FieldOpsBounds<'b, P::BaseField, F>,
{
}

impl<P, F> CondSelectGadget<<P::BaseField as Field>::BasePrimeField> for ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    #[inline]
    #[tracing::instrument(target = "r1cs")]
    fn conditionally_select(
        cond: &Boolean<<P::BaseField as Field>::BasePrimeField>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = cond.select(&true_value.x, &false_value.x)?;
        let y = cond.select(&true_value.y, &false_value.y)?;
        let z = cond.select(&true_value.z, &false_value.z)?;

        Ok(Self::new(x, y, z))
    }
}

impl<P, F> EqGadget<<P::BaseField as Field>::BasePrimeField> for ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    #[tracing::instrument(target = "r1cs")]
    fn is_eq(
        &self,
        other: &Self,
    ) -> Result<Boolean<<P::BaseField as Field>::BasePrimeField>, SynthesisError> {
        let x_equal = (&self.x * &other.z).is_eq(&(&other.x * &self.z))?;
        let y_equal = (&self.y * &other.z).is_eq(&(&other.y * &self.z))?;
        let coordinates_equal = x_equal.and(&y_equal)?;
        let both_are_zero = self.is_zero()?.and(&other.is_zero()?)?;
        both_are_zero.or(&coordinates_equal)
    }

    #[inline]
    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<<P::BaseField as Field>::BasePrimeField>,
    ) -> Result<(), SynthesisError> {
        let x_equal = (&self.x * &other.z).is_eq(&(&other.x * &self.z))?;
        let y_equal = (&self.y * &other.z).is_eq(&(&other.y * &self.z))?;
        let coordinates_equal = x_equal.and(&y_equal)?;
        let both_are_zero = self.is_zero()?.and(&other.is_zero()?)?;
        both_are_zero
            .or(&coordinates_equal)?
            .conditional_enforce_equal(&Boolean::Constant(true), condition)?;
        Ok(())
    }

    #[inline]
    #[tracing::instrument(target = "r1cs")]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        condition: &Boolean<<P::BaseField as Field>::BasePrimeField>,
    ) -> Result<(), SynthesisError> {
        let is_equal = self.is_eq(other)?;
        is_equal
            .and(condition)?
            .enforce_equal(&Boolean::Constant(false))
    }
}

impl<P, F> AllocVar<SWAffine<P>, <P::BaseField as Field>::BasePrimeField> for ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    fn new_variable<T: Borrow<SWAffine<P>>>(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        Self::new_variable(cs, || f().map(|b| b.borrow().into_projective()), mode)
    }
}

impl<P, F> AllocVar<SWProjective<P>, <P::BaseField as Field>::BasePrimeField>
    for ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    fn new_variable<T: Borrow<SWProjective<P>>>(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let f = || Ok(*f()?.borrow());
        match mode {
            AllocationMode::Constant => Self::new_variable_omit_prime_order_check(cs, f, mode),
            AllocationMode::Input => Self::new_variable_omit_prime_order_check(cs, f, mode),
            AllocationMode::Witness => {
                // if cofactor.is_even():
                //   divide until you've removed all even factors
                // else:
                //   just directly use double and add.
                let mut power_of_2: u32 = 0;
                let mut cofactor = P::COFACTOR.to_vec();
                while cofactor[0] % 2 == 0 {
                    div2(&mut cofactor);
                    power_of_2 += 1;
                }

                let cofactor_weight = BitIteratorBE::new(cofactor.as_slice())
                    .filter(|b| *b)
                    .count();
                let modulus_minus_1 = (-P::ScalarField::one()).into_repr(); // r - 1
                let modulus_minus_1_weight =
                    BitIteratorBE::new(modulus_minus_1).filter(|b| *b).count();

                // We pick the most efficient method of performing the prime order check:
                // If the cofactor has lower hamming weight than the scalar field's modulus,
                // we first multiply by the inverse of the cofactor, and then, after allocating,
                // multiply by the cofactor. This ensures the resulting point has no cofactors
                //
                // Else, we multiply by the scalar field's modulus and ensure that the result
                // equals the identity.

                let (mut ge, iter) = if cofactor_weight < modulus_minus_1_weight {
                    let ge = Self::new_variable_omit_prime_order_check(
                        ark_relations::ns!(cs, "Witness without subgroup check with cofactor mul"),
                        || f().map(|g| g.borrow().into_affine().mul_by_cofactor_inv().into()),
                        mode,
                    )?;
                    (
                        ge,
                        BitIteratorBE::without_leading_zeros(cofactor.as_slice()),
                    )
                } else {
                    let ge = Self::new_variable_omit_prime_order_check(
                        ark_relations::ns!(cs, "Witness without subgroup check with `r` check"),
                        || {
                            f().map(|g| {
                                let g = g.into_affine();
                                let mut power_of_two = P::ScalarField::one().into_repr();
                                power_of_two.muln(power_of_2);
                                let power_of_two_inv = P::ScalarField::from_repr(power_of_two)
                                    .and_then(|n| n.inverse())
                                    .unwrap();
                                g.mul(power_of_two_inv)
                            })
                        },
                        mode,
                    )?;

                    (
                        ge,
                        BitIteratorBE::without_leading_zeros(modulus_minus_1.as_ref()),
                    )
                };
                // Remove the even part of the cofactor
                for _ in 0..power_of_2 {
                    ge.double_in_place()?;
                }

                let mut result = Self::zero();
                for b in iter {
                    result.double_in_place()?;

                    if b {
                        result += &ge
                    }
                }
                if cofactor_weight < modulus_minus_1_weight {
                    Ok(result)
                } else {
                    ge.enforce_equal(&ge)?;
                    Ok(ge)
                }
            }
        }
    }
}

#[inline]
fn div2(limbs: &mut [u64]) {
    let mut t = 0;
    for i in limbs.iter_mut().rev() {
        let t2 = *i << 63;
        *i >>= 1;
        *i |= t;
        t = t2;
    }
}

impl<P, F> ToBitsGadget<<P::BaseField as Field>::BasePrimeField> for ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bits_le(
        &self,
    ) -> Result<Vec<Boolean<<P::BaseField as Field>::BasePrimeField>>, SynthesisError> {
        let g = self.to_affine()?;
        let mut bits = g.x.to_bits_le()?;
        let y_bits = g.y.to_bits_le()?;
        bits.extend_from_slice(&y_bits);
        bits.push(g.infinity);
        Ok(bits)
    }

    #[tracing::instrument(target = "r1cs")]
    fn to_non_unique_bits_le(
        &self,
    ) -> Result<Vec<Boolean<<P::BaseField as Field>::BasePrimeField>>, SynthesisError> {
        let g = self.to_affine()?;
        let mut bits = g.x.to_non_unique_bits_le()?;
        let y_bits = g.y.to_non_unique_bits_le()?;
        bits.extend_from_slice(&y_bits);
        bits.push(g.infinity);
        Ok(bits)
    }
}

impl<P, F> ToBytesGadget<<P::BaseField as Field>::BasePrimeField> for ProjectiveVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    #[tracing::instrument(target = "r1cs")]
    fn to_bytes(
        &self,
    ) -> Result<Vec<UInt8<<P::BaseField as Field>::BasePrimeField>>, SynthesisError> {
        let g = self.to_affine()?;
        let mut bytes = g.x.to_bytes()?;
        let y_bytes = g.y.to_bytes()?;
        let inf_bytes = g.infinity.to_bytes()?;
        bytes.extend_from_slice(&y_bytes);
        bytes.extend_from_slice(&inf_bytes);
        Ok(bytes)
    }

    #[tracing::instrument(target = "r1cs")]
    fn to_non_unique_bytes(
        &self,
    ) -> Result<Vec<UInt8<<P::BaseField as Field>::BasePrimeField>>, SynthesisError> {
        let g = self.to_affine()?;
        let mut bytes = g.x.to_non_unique_bytes()?;
        let y_bytes = g.y.to_non_unique_bytes()?;
        let inf_bytes = g.infinity.to_non_unique_bytes()?;
        bytes.extend_from_slice(&y_bytes);
        bytes.extend_from_slice(&inf_bytes);
        Ok(bytes)
    }
}
