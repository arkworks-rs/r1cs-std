use crate::fields::{cubic_extension::*, FieldWithVar};
use ark_ff::fields::{CubicExtParameters, Fp3Parameters, Fp3ParamsWrapper};

type FpVar<P> = <<Fp3ParamsWrapper<P> as CubicExtParameters>::BasePrimeField as FieldWithVar>::Var;

/// A cubic extension field constructed over a prime field.
/// This is the R1CS equivalent of `ark_ff::Fp3<P>`.
pub type Fp3Var<P> = CubicExtVar<Fp3ParamsWrapper<P>>;

impl<P: Fp3Parameters> CubicExtVarParams for Fp3ParamsWrapper<P>
where
    Self::BasePrimeField: FieldWithVar,
{
    fn mul_base_field_vars_by_frob_coeff(c1: &mut FpVar<P>, c2: &mut FpVar<P>, power: usize) {
        *c1 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        *c2 *= Self::FROBENIUS_COEFF_C2[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
