use super::*;
/// An affine representation of a curve point that is guaranteed
/// to *not* be the point at infinity.
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
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

impl<P, F> AffineVar<P, F>
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

    /// Returns the value assigned to `self` in the underlying
    /// constraint system.
    pub(crate) fn value(&self) -> Result<SWAffine<P>, SynthesisError> {
        Ok(SWAffine::new(
            self.x.value()?,
            self.y.value()?,
            false,
        ))
    }
}