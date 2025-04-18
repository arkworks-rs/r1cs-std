use super::*;
use ark_std::ops::Add;

/// An affine representation of a prime order curve point that is guaranteed
/// to *not* be the point at infinity.
#[derive(Educe)]
#[educe(Debug, Clone)]
#[must_use]
pub struct NonZeroAffineVar<
    P: SWCurveConfig,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
> where
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    /// The x-coordinate.
    pub x: F,
    /// The y-coordinate.
    pub y: F,
    #[educe(Debug(ignore))]
    _params: PhantomData<P>,
}

impl<P, F> NonZeroAffineVar<P, F>
where
    P: SWCurveConfig,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    /// Creates a new non-zero affine point.
    pub fn new(x: F, y: F) -> Self {
        Self {
            x,
            y,
            _params: PhantomData,
        }
    }

    /// Converts self into a non-zero projective point.
    #[tracing::instrument(target = "gr1cs", skip(self))]
    pub fn into_projective(&self) -> ProjectiveVar<P, F> {
        ProjectiveVar::new(self.x.clone(), self.y.clone(), F::one())
    }

    /// Performs an addition without checking that other != ±self.
    #[tracing::instrument(target = "gr1cs", skip(self, other))]
    pub fn add_unchecked(&self, other: &Self) -> Result<Self, SynthesisError> {
        if [self, other].is_constant() {
            let result = self.value()?.add(other.value()?).into_affine();
            Ok(Self::new(F::constant(result.x), F::constant(result.y)))
        } else {
            let (x1, y1) = (&self.x, &self.y);
            let (x2, y2) = (&other.x, &other.y);
            // Then,
            // slope lambda := (y2 - y1)/(x2 - x1);
            // x3 = lambda^2 - x1 - x2;
            // y3 = lambda * (x1 - x3) - y1
            let numerator = y2 - y1;
            let denominator = x2 - x1;
            // It's okay to use `unchecked` here, because the precondition of
            // `add_unchecked` is that self != ±other, which means that
            // `numerator` and `denominator` are both non-zero.
            let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;
            let x3 = lambda.square()? - x1 - x2;
            let y3 = lambda * &(x1 - &x3) - y1;
            Ok(Self::new(x3, y3))
        }
    }

    /// Doubles `self`. As this is a prime order curve point,
    /// the output is guaranteed to not be the point at infinity.
    #[tracing::instrument(target = "gr1cs", skip(self))]
    pub fn double(&self) -> Result<Self, SynthesisError> {
        if [self].is_constant() {
            let result = SWProjective::<P>::from(self.value()?)
                .double()
                .into_affine();
            // Panic if the result is zero.
            assert!(!result.is_zero());
            Ok(Self::new(F::constant(result.x), F::constant(result.y)))
        } else {
            let (x1, y1) = (&self.x, &self.y);
            let x1_sqr = x1.square()?;
            // Then,
            // tangent lambda := (3 * x1^2 + a) / (2 * y1);
            // x3 = lambda^2 - 2x1
            // y3 = lambda * (x1 - x3) - y1
            let numerator = x1_sqr.double()? + &x1_sqr + P::COEFF_A;
            let denominator = y1.double()?;
            // It's okay to use `unchecked` here, because the precondition of `double` is
            // that self != zero.
            let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;
            let x3 = lambda.square()? - x1.double()?;
            let y3 = lambda * &(x1 - &x3) - y1;
            Ok(Self::new(x3, y3))
        }
    }

    /// Computes `(self + other) + self`. This method requires only 5
    /// constraints, less than the 7 required when computing via
    /// `self.double() + other`.
    ///
    /// This follows the formulae from [\[ELM03\]](https://arxiv.org/abs/math/0208038).
    #[tracing::instrument(target = "gr1cs", skip(self))]
    pub fn double_and_add_unchecked(&self, other: &Self) -> Result<Self, SynthesisError> {
        if [self].is_constant() || other.is_constant() {
            self.double()?.add_unchecked(other)
        } else {
            // It's okay to use `unchecked` the precondition is that `self != ±other` (i.e.
            // same logic as in `add_unchecked`)
            let (x1, y1) = (&self.x, &self.y);
            let (x2, y2) = (&other.x, &other.y);

            // Calculate self + other:
            // slope lambda := (y2 - y1)/(x2 - x1);
            // x3 = lambda^2 - x1 - x2;
            // y3 = lambda * (x1 - x3) - y1
            let numerator = y2 - y1;
            let denominator = x2 - x1;
            let lambda_1 = numerator.mul_by_inverse_unchecked(&denominator)?;

            let x3 = lambda_1.square()? - x1 - x2;

            // Calculate final addition slope:
            let lambda_2 =
                (lambda_1 + y1.double()?.mul_by_inverse_unchecked(&(&x3 - x1))?).negate()?;

            let x4 = lambda_2.square()? - x1 - x3;
            let y4 = lambda_2 * &(x1 - &x4) - y1;
            Ok(Self::new(x4, y4))
        }
    }

    /// Doubles `self` in place.
    #[tracing::instrument(target = "gr1cs", skip(self))]
    pub fn double_in_place(&mut self) -> Result<(), SynthesisError> {
        *self = self.double()?;
        Ok(())
    }
}

impl<P, F> GR1CSVar<<P::BaseField as Field>::BasePrimeField> for NonZeroAffineVar<P, F>
where
    P: SWCurveConfig,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    type Value = SWAffine<P>;

    fn cs(&self) -> ConstraintSystemRef<<P::BaseField as Field>::BasePrimeField> {
        self.x.cs().or(self.y.cs())
    }

    fn value(&self) -> Result<SWAffine<P>, SynthesisError> {
        Ok(SWAffine::new(self.x.value()?, self.y.value()?))
    }
}

impl<P, F> CondSelectGadget<<P::BaseField as Field>::BasePrimeField> for NonZeroAffineVar<P, F>
where
    P: SWCurveConfig,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    #[inline]
    #[tracing::instrument(target = "gr1cs")]
    fn conditionally_select(
        cond: &Boolean<<P::BaseField as Field>::BasePrimeField>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = cond.select(&true_value.x, &false_value.x)?;
        let y = cond.select(&true_value.y, &false_value.y)?;

        Ok(Self::new(x, y))
    }
}

impl<P, F> EqGadget<<P::BaseField as Field>::BasePrimeField> for NonZeroAffineVar<P, F>
where
    P: SWCurveConfig,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    #[tracing::instrument(target = "gr1cs")]
    fn is_eq(
        &self,
        other: &Self,
    ) -> Result<Boolean<<P::BaseField as Field>::BasePrimeField>, SynthesisError> {
        let x_equal = self.x.is_eq(&other.x)?;
        let y_equal = self.y.is_eq(&other.y)?;
        Ok(x_equal & y_equal)
    }

    #[inline]
    #[tracing::instrument(target = "gr1cs")]
    fn conditional_enforce_equal(
        &self,
        other: &Self,
        condition: &Boolean<<P::BaseField as Field>::BasePrimeField>,
    ) -> Result<(), SynthesisError> {
        let x_equal = self.x.is_eq(&other.x)?;
        let y_equal = self.y.is_eq(&other.y)?;
        let coordinates_equal = x_equal & y_equal;
        coordinates_equal.conditional_enforce_equal(&Boolean::TRUE, condition)?;
        Ok(())
    }

    #[inline]
    #[tracing::instrument(target = "gr1cs")]
    fn enforce_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.x.enforce_equal(&other.x)?;
        self.y.enforce_equal(&other.y)?;
        Ok(())
    }

    #[inline]
    #[tracing::instrument(target = "gr1cs")]
    fn conditional_enforce_not_equal(
        &self,
        other: &Self,
        condition: &Boolean<<P::BaseField as Field>::BasePrimeField>,
    ) -> Result<(), SynthesisError> {
        let is_equal = self.is_eq(other)?;
        (is_equal & condition).enforce_equal(&Boolean::FALSE)
    }
}

#[cfg(test)]
mod test_non_zero_affine {
    use crate::{
        alloc::AllocVar,
        eq::EqGadget,
        fields::fp::{AllocatedFp, FpVar},
        groups::{
            curves::short_weierstrass::{non_zero_affine::NonZeroAffineVar, ProjectiveVar},
            CurveVar,
        },
        GR1CSVar,
    };
    use ark_ec::{models::short_weierstrass::SWCurveConfig, CurveGroup};
    use ark_relations::gr1cs::ConstraintSystem;
    use ark_std::{vec::Vec, One};
    use ark_test_curves::bls12_381::{g1::Config as G1Config, Fq};

    #[test]
    fn correctness_test_1() {
        let cs = ConstraintSystem::<Fq>::new_ref();

        let x = FpVar::Var(
            AllocatedFp::<Fq>::new_witness(cs.clone(), || Ok(G1Config::GENERATOR.x)).unwrap(),
        );
        let y = FpVar::Var(
            AllocatedFp::<Fq>::new_witness(cs.clone(), || Ok(G1Config::GENERATOR.y)).unwrap(),
        );

        // The following code uses `double` and `add` (`add_unchecked`) to compute
        // (1 + 2 + ... + 2^9) G

        let sum_a = {
            let mut a = ProjectiveVar::<G1Config, FpVar<Fq>>::new(
                x.clone(),
                y.clone(),
                FpVar::Constant(Fq::one()),
            );

            let mut double_sequence = Vec::new();
            double_sequence.push(a.clone());

            for _ in 1..10 {
                a = a.double().unwrap();
                double_sequence.push(a.clone());
            }

            let mut sum = double_sequence[0].clone();
            for elem in double_sequence.iter().skip(1) {
                sum = sum + elem;
            }

            let sum = sum.value().unwrap().into_affine();
            (sum.x, sum.y)
        };

        let sum_b = {
            let mut a = NonZeroAffineVar::<G1Config, FpVar<Fq>>::new(x, y);

            let mut double_sequence = Vec::new();
            double_sequence.push(a.clone());

            for _ in 1..10 {
                a = a.double().unwrap();
                double_sequence.push(a.clone());
            }

            let mut sum = double_sequence[0].clone();
            for elem in double_sequence.iter().skip(1) {
                sum = sum.add_unchecked(&elem).unwrap();
            }

            (sum.x.value().unwrap(), sum.y.value().unwrap())
        };

        assert_eq!(sum_a.0, sum_b.0);
        assert_eq!(sum_a.1, sum_b.1);
    }

    #[test]
    fn correctness_test_2() {
        let cs = ConstraintSystem::<Fq>::new_ref();

        let x = FpVar::Var(
            AllocatedFp::<Fq>::new_witness(cs.clone(), || Ok(G1Config::GENERATOR.x)).unwrap(),
        );
        let y = FpVar::Var(
            AllocatedFp::<Fq>::new_witness(cs.clone(), || Ok(G1Config::GENERATOR.y)).unwrap(),
        );

        // The following code tests `double_and_add`.
        let sum_a = {
            let a = ProjectiveVar::<G1Config, FpVar<Fq>>::new(
                x.clone(),
                y.clone(),
                FpVar::Constant(Fq::one()),
            );

            let mut cur = a.clone();
            cur.double_in_place().unwrap();
            for _ in 1..10 {
                cur.double_in_place().unwrap();
                cur = cur + &a;
            }

            let sum = cur.value().unwrap().into_affine();
            (sum.x, sum.y)
        };

        let sum_b = {
            let a = NonZeroAffineVar::<G1Config, FpVar<Fq>>::new(x, y);

            let mut cur = a.double().unwrap();
            for _ in 1..10 {
                cur = cur.double_and_add_unchecked(&a).unwrap();
            }

            (cur.x.value().unwrap(), cur.y.value().unwrap())
        };

        assert!(cs.is_satisfied().unwrap());
        assert_eq!(sum_a.0, sum_b.0);
        assert_eq!(sum_a.1, sum_b.1);
    }

    #[test]
    fn correctness_test_eq() {
        let cs = ConstraintSystem::<Fq>::new_ref();

        let x = FpVar::Var(
            AllocatedFp::<Fq>::new_witness(cs.clone(), || Ok(G1Config::GENERATOR.x)).unwrap(),
        );
        let y = FpVar::Var(
            AllocatedFp::<Fq>::new_witness(cs.clone(), || Ok(G1Config::GENERATOR.y)).unwrap(),
        );

        let a = NonZeroAffineVar::<G1Config, FpVar<Fq>>::new(x, y);

        let n = 10;

        let a_multiples: Vec<NonZeroAffineVar<G1Config, FpVar<Fq>>> =
            std::iter::successors(Some(a.clone()), |acc| Some(acc.add_unchecked(&a).unwrap()))
                .take(n)
                .collect();

        let all_equal: Vec<NonZeroAffineVar<G1Config, FpVar<Fq>>> = (0..n / 2)
            .map(|i| {
                a_multiples[i]
                    .add_unchecked(&a_multiples[n - i - 1])
                    .unwrap()
            })
            .collect();

        for i in 0..n - 1 {
            a_multiples[i]
                .enforce_not_equal(&a_multiples[i + 1])
                .unwrap();
        }
        for i in 0..all_equal.len() - 1 {
            all_equal[i].enforce_equal(&all_equal[i + 1]).unwrap();
        }

        assert!(cs.is_satisfied().unwrap());
    }
}
