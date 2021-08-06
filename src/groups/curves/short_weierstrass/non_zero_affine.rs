use super::*;

/// An affine representation of a prime order curve point that is guaranteed
/// to *not* be the point at infinity.
#[derive(Derivative)]
#[derivative(
    Debug(bound = "P: SWModelParameters"),
    Clone(bound = "P: SWModelParameters")
)]
#[must_use]
pub struct NonZeroAffineVar<P: SWModelParameters>
where
    BF<P>: FieldWithVar,
{
    /// The x-coordinate.
    pub x: BFVar<P>,
    /// The y-coordinate.
    pub y: BFVar<P>,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

impl<P> NonZeroAffineVar<P>
where
    P: SWModelParameters,
    BF<P>: FieldWithVar,
    BFVar<P>: FieldVar<P::BaseField, CF<P>>,
{
    pub(crate) fn new(x: BFVar<P>, y: BFVar<P>) -> Self {
        Self {
            x,
            y,
            _params: PhantomData,
        }
    }

    /// Converts self into a non-zero projective point.
    #[tracing::instrument(target = "r1cs", skip(self))]
    pub(crate) fn into_projective(&self) -> ProjectiveVar<P> {
        ProjectiveVar::new(self.x.clone(), self.y.clone(), BFVar::<P>::one())
    }
}

impl<P> NonZeroAffineVar<P>
where
    P: SWModelParameters,
    BF<P>: FieldWithVar,
    BFVar<P>: FieldVar<P::BaseField, CF<P>>,
    for<'a> &'a BFVar<P>: FieldOpsBounds<'a, P::BaseField, BFVar<P>>,
{
    /// Performs an addition without checking that other != ±self.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    pub(crate) fn add_unchecked(&self, other: &Self) -> Result<Self, SynthesisError> {
        if [self, other].is_constant() {
            let result =
                (self.value()?.into_projective() + other.value()?.into_projective()).into_affine();
            Ok(Self::new(
                BFVar::<P>::constant(result.x),
                BFVar::<P>::constant(result.y),
            ))
        } else {
            let (x1, y1) = (&self.x, &self.y);
            let (x2, y2) = (&other.x, &other.y);
            // Then,
            // slope lambda := (y2 - y1)/(x2 - x1);
            // x3 = lambda^2 - x1 - x2;
            // y3 = lambda * (x1 - x3) - y1
            let numerator = y2 - y1;
            let denominator = x2 - x1;
            // It's okay to use `unchecked` here, because the precondition of `add_unchecked` is that
            // self != ±other, which means that `numerator` and `denominator` are both non-zero.
            let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;
            let x3 = lambda.square()? - x1 - x2;
            let y3 = lambda * &(x1 - &x3) - y1;
            Ok(Self::new(x3, y3))
        }
    }

    /// Doubles `self`. As this is a prime order curve point,
    /// the output is guaranteed to not be the point at infinity.
    #[tracing::instrument(target = "r1cs", skip(self))]
    pub(crate) fn double(&self) -> Result<Self, SynthesisError> {
        if [self].is_constant() {
            let result = self.value()?.into_projective().double().into_affine();
            // Panic if the result is zero.
            assert!(!result.is_zero());
            Ok(Self::new(
                BFVar::<P>::constant(result.x),
                BFVar::<P>::constant(result.y),
            ))
        } else {
            let (x1, y1) = (&self.x, &self.y);
            let x1_sqr = x1.square()?;
            // Then,
            // tangent lambda := (3 * x1^2 + a) / (2 * y1);
            // x3 = lambda^2 - 2x1
            // y3 = lambda * (x1 - x3) - y1
            let numerator = x1_sqr.double()? + &x1_sqr + P::COEFF_A;
            let denominator = y1.double()?;
            // It's okay to use `unchecked` here, because the precondition of `double` is that
            // self != zero.
            let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;
            let x3 = lambda.square()? - x1.double()?;
            let y3 = lambda * &(x1 - &x3) - y1;
            Ok(Self::new(x3, y3))
        }
    }

    /// Computes `(self + other) + self`. This method requires only 5 constraints,
    /// less than the 7 required when computing via `self.double() + other`.
    ///
    /// This follows the formulae from [\[ELM03\]](https://arxiv.org/abs/math/0208038).
    #[tracing::instrument(target = "r1cs", skip(self))]
    pub(crate) fn double_and_add_unchecked(&self, other: &Self) -> Result<Self, SynthesisError> {
        if [self].is_constant() || other.is_constant() {
            self.double()?.add_unchecked(other)
        } else {
            // It's okay to use `unchecked` the precondition is that `self != ±other` (i.e. same logic as in `add_unchecked`)
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
    #[tracing::instrument(target = "r1cs", skip(self))]
    pub(crate) fn double_in_place(&mut self) -> Result<(), SynthesisError> {
        *self = self.double()?;
        Ok(())
    }
}

impl<P> R1CSVar<CF<P>> for NonZeroAffineVar<P>
where
    P: SWModelParameters,
    BF<P>: FieldWithVar,
{
    type Value = SWAffine<P>;

    fn cs(&self) -> ConstraintSystemRef<CF<P>> {
        self.x.cs().or(self.y.cs())
    }

    fn value(&self) -> Result<SWAffine<P>, SynthesisError> {
        Ok(SWAffine::new(self.x.value()?, self.y.value()?, false))
    }
}

impl<P> CondSelectGadget<CF<P>> for NonZeroAffineVar<P>
where
    P: SWModelParameters,
    BF<P>: FieldWithVar,
{
    #[inline]
    #[tracing::instrument(target = "r1cs")]
    fn conditionally_select(
        cond: &Boolean<CF<P>>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = cond.select(&true_value.x, &false_value.x)?;
        let y = cond.select(&true_value.y, &false_value.y)?;

        Ok(Self::new(x, y))
    }
}

#[cfg(test)]
mod test_non_zero_affine {
    use crate::alloc::AllocVar;
    use crate::fields::fp::{AllocatedFp, FpVar};
    use crate::groups::curves::short_weierstrass::non_zero_affine::NonZeroAffineVar;
    use crate::groups::curves::short_weierstrass::ProjectiveVar;
    use crate::groups::CurveVar;
    use crate::R1CSVar;
    use ark_ec::{ProjectiveCurve, SWModelParameters};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{vec::Vec, One};
    use ark_test_curves::bls12_381::{g1::Parameters as G1Parameters, Fq};

    #[test]
    fn correctness_test_1() {
        let cs = ConstraintSystem::<Fq>::new_ref();

        let x = FpVar::Var(
            AllocatedFp::<Fq>::new_witness(cs.clone(), || {
                Ok(G1Parameters::AFFINE_GENERATOR_COEFFS.0)
            })
            .unwrap(),
        );
        let y = FpVar::Var(
            AllocatedFp::<Fq>::new_witness(cs.clone(), || {
                Ok(G1Parameters::AFFINE_GENERATOR_COEFFS.1)
            })
            .unwrap(),
        );

        // The following code uses `double` and `add` (`add_unchecked`) to compute
        // (1 + 2 + ... + 2^9) G

        let sum_a = {
            let mut a = ProjectiveVar::<G1Parameters>::new(
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
            let mut a = NonZeroAffineVar::<G1Parameters>::new(x, y);

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
            AllocatedFp::<Fq>::new_witness(cs.clone(), || {
                Ok(G1Parameters::AFFINE_GENERATOR_COEFFS.0)
            })
            .unwrap(),
        );
        let y = FpVar::Var(
            AllocatedFp::<Fq>::new_witness(cs.clone(), || {
                Ok(G1Parameters::AFFINE_GENERATOR_COEFFS.1)
            })
            .unwrap(),
        );

        // The following code tests `double_and_add`.
        let sum_a = {
            let a = ProjectiveVar::<G1Parameters>::new(
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
            let a = NonZeroAffineVar::<G1Parameters>::new(x, y);

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
}
