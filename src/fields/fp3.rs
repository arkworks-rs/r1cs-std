use crate::fields::{cubic_extension::*, FieldWithVar};
use ark_ff::fields::{CubicExtConfig, Fp3Config, Fp3ConfigWrapper};

type FpVar<P> = <<Fp3ConfigWrapper<P> as CubicExtConfig>::BasePrimeField as FieldWithVar>::Var;

/// A cubic extension field constructed over a prime field.
/// This is the R1CS equivalent of `ark_ff::Fp3<P>`.
pub type Fp3Var<P> = CubicExtVar<Fp3ConfigWrapper<P>>;

impl<P: Fp3Config> CubicExtVarConfig for Fp3ConfigWrapper<P>
where
    Self::BasePrimeField: FieldWithVar,
{
    fn mul_base_field_vars_by_frob_coeff(c1: &mut FpVar<P>, c2: &mut FpVar<P>, power: usize) {
        *c1 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        *c2 *= Self::FROBENIUS_COEFF_C2[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
