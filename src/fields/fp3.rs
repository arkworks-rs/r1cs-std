use crate::fields::{FieldExt, cubic_extension::*, fp::FpVar};
use ark_ff::fields::{CubicExtParameters, Fp3Parameters, Fp3ParamsWrapper};

/// A cubic extension field constructed over a prime field.
/// This is the R1CS equivalent of `ark_ff::Fp3<P>`.
pub type Fp3Var<P> = CubicExtVar<Fp3ParamsWrapper<P>>;

impl<P: Fp3Parameters> CubicExtVarParams for Fp3ParamsWrapper<P> 
where 
    Self::BasePrimeField: FieldExt
{
    fn mul_base_field_vars_by_frob_coeff(
        c1: &mut FpVar<P::Fp>,
        c2: &mut FpVar<P::Fp>,
        power: usize,
    ) {
        *c1 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        *c2 *= Self::FROBENIUS_COEFF_C2[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
