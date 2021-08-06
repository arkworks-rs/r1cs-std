use crate::fields::{quadratic_extension::*, FieldWithVar};
use ark_ff::fields::{Fp2Parameters, Fp2ParamsWrapper, QuadExtParameters};

type FpVar<P> = <<Fp2ParamsWrapper<P> as QuadExtParameters>::BasePrimeField as FieldWithVar>::Var;

/// A quadratic extension field constructed over a prime field.
/// This is the R1CS equivalent of `ark_ff::Fp2<P>`.
pub type Fp2Var<P> = QuadExtVar<Fp2ParamsWrapper<P>>;

impl<P: Fp2Parameters> QuadExtVarParams for Fp2ParamsWrapper<P>
where
    Self::BaseField: FieldWithVar,
{
    fn mul_base_field_var_by_frob_coeff(fe: &mut FpVar<P>, power: usize) {
        *fe *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
