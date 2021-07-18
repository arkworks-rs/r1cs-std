use crate::fields::{FieldExt, fp::FpVar, quadratic_extension::*};
use ark_ff::fields::{Fp2Parameters, Fp2ParamsWrapper, QuadExtParameters};

/// A quadratic extension field constructed over a prime field.
/// This is the R1CS equivalent of `ark_ff::Fp2<P>`.
pub type Fp2Var<P> = QuadExtVar<Fp2ParamsWrapper<P>>;

impl<P: Fp2Parameters> QuadExtVarParams for Fp2ParamsWrapper<P> 
where
    Self::BaseField: FieldExt
{
    fn mul_base_field_var_by_frob_coeff(fe: &mut FpVar<P::Fp>, power: usize) {
        *fe *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
