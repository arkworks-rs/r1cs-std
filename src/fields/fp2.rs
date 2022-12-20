use crate::fields::{quadratic_extension::*, FieldWithVar};
use ark_ff::fields::{Fp2Config, Fp2ConfigWrapper, QuadExtConfig};

type FpVar<P> = <<Fp2ConfigWrapper<P> as QuadExtConfig>::BasePrimeField as FieldWithVar>::Var;

/// A quadratic extension field constructed over a prime field.
/// This is the R1CS equivalent of `ark_ff::Fp2<P>`.
pub type Fp2Var<P> = QuadExtVar<Fp2ConfigWrapper<P>>;

impl<P: Fp2Config> QuadExtVarConfig for Fp2ConfigWrapper<P>
where
    Self::BaseField: FieldWithVar,
{
    fn mul_base_field_var_by_frob_coeff(fe: &mut FpVar<P>, power: usize) {
        *fe *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
