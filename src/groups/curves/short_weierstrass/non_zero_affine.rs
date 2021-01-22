use super::*;
/// An affine representation of a prime order curve point that is guaranteed
/// to *not* be the point at infinity.
#[derive(Derivative)]
#[derivative(Debug, Clone)]
#[must_use]
pub struct NonZeroAffineVar<
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
> where
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    /// The x-coordinate.
    pub x: F,
    /// The y-coordinate.
    pub y: F,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

impl<P, F> NonZeroAffineVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    pub(crate) fn new(x: F, y: F) -> Self {
        Self {
            x,
            y,
            _params: PhantomData,
        }
    }

    /// Converts self into a non-zero projective point.
    #[tracing::instrument(target = "r1cs", skip(self))]
    pub(crate) fn into_projective(&self) -> ProjectiveVar<P, F> {
        ProjectiveVar::new(self.x.clone(), self.y.clone(), F::one())
    }

    /// Performs an addition without checking that other != ±self.
    #[tracing::instrument(target = "r1cs", skip(self, other))]
    pub(crate) fn add_unchecked(&self, other: &Self) -> Result<Self, SynthesisError> {
        if [self, other].is_constant() {
            let result =
                (self.value()?.into_projective() + other.value()?.into_projective()).into_affine();
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
            let lambda = numerator.mul_by_inverse(&denominator)?;
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
            let lambda = numerator.mul_by_inverse(&denominator)?;
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
    pub(crate) fn double_and_add(&self, other: &Self) -> Result<Self, SynthesisError> {
        if [self].is_constant() || other.is_constant() {
            self.double()?.add_unchecked(other)
        } else {
            let (x1, y1) = (&self.x, &self.y);
            let (x2, y2) = (&other.x, &other.y);

            // Calculate self + other:
            // slope lambda := (y2 - y1)/(x2 - x1);
            // x3 = lambda^2 - x1 - x2;
            // y3 = lambda * (x1 - x3) - y1
            let numerator = y2 - y1;
            let denominator = x2 - x1;
            let lambda_1 = numerator.mul_by_inverse(&denominator)?;

            let x3 = lambda_1.square()? - x1 - x2;

            // Calculate final addition slope:
            let lambda_2 = (lambda_1 + y1.double()?.mul_by_inverse(&(&x3 - x1))?).negate()?;

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

impl<P, F> R1CSVar<<P::BaseField as Field>::BasePrimeField> for NonZeroAffineVar<P, F>
where
    P: SWModelParameters,
    F: FieldVar<P::BaseField, <P::BaseField as Field>::BasePrimeField>,
    for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    type Value = SWAffine<P>;

    fn cs(&self) -> ConstraintSystemRef<<P::BaseField as Field>::BasePrimeField> {
        self.x.cs().or(self.y.cs())
    }

    fn value(&self) -> Result<SWAffine<P>, SynthesisError> {
        Ok(SWAffine::new(self.x.value()?, self.y.value()?, false))
    }
}

impl<P, F> CondSelectGadget<<P::BaseField as Field>::BasePrimeField> for NonZeroAffineVar<P, F>
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

        Ok(Self::new(x, y))
    }
}
