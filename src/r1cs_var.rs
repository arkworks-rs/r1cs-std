use ark_ff::Field;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_std::vec::Vec;

/// This trait describes some core functionality that is common to high-level
/// variables, such as `Boolean`s, `FieldVar`s, `GroupVar`s, etc.
pub trait R1CSVar<F: Field> {
    /// The type of the "native" value that `Self` represents in the constraint
    /// system.
    type Value: core::fmt::Debug + Eq + Clone;

    /// Returns the underlying `ConstraintSystemRef`.
    ///
    /// If `self` is a constant value, then this *must* return
    /// `ark_relations::r1cs::ConstraintSystemRef::None`.
    fn cs(&self) -> ConstraintSystemRef<F>;

    /// Returns `true` if `self` is a circuit-generation-time constant.
    fn is_constant(&self) -> bool {
        self.cs().is_none()
    }

    /// Returns the value that is assigned to `self` in the underlying
    /// `ConstraintSystem`.
    fn value(&self) -> Result<Self::Value, SynthesisError>;
}

impl<F: Field, T: R1CSVar<F>> R1CSVar<F> for [T] {
    type Value = Vec<T::Value>;

    fn cs(&self) -> ConstraintSystemRef<F> {
        let mut result = ConstraintSystemRef::None;
        for var in self {
            result = var.cs().or(result);
        }
        result
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let mut result = Vec::new();
        for var in self {
            result.push(var.value()?);
        }
        Ok(result)
    }
}

impl<'a, F: Field, T: 'a + R1CSVar<F>> R1CSVar<F> for &'a T {
    type Value = T::Value;

    fn cs(&self) -> ConstraintSystemRef<F> {
        (*self).cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        (*self).value()
    }
}

impl<F: Field, T: R1CSVar<F>, const N: usize> R1CSVar<F> for [T; N] {
    type Value = [T::Value; N];

    fn cs(&self) -> ConstraintSystemRef<F> {
        let mut result = ConstraintSystemRef::None;
        for var in self {
            result = var.cs().or(result);
        }
        result
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok(core::array::from_fn(|i| self[i].value().unwrap()))
    }
}

impl<F: Field> R1CSVar<F> for () {
    type Value = ();

    fn cs(&self) -> ConstraintSystemRef<F> {
        ConstraintSystemRef::None
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok(())
    }
}
