use crate::fields::{fp::FpVar, quadratic_extension::*};
use ark_ff::fields::{Fp2Config, Fp2ConfigWrapper, QuadExtConfig};

/// A quadratic extension field constructed over a prime field.
/// This is the R1CS equivalent of `ark_ff::Fp2<P>`.
pub type Fp2Var<P> = QuadExtVar<FpVar<<P as Fp2Config>::Fp>, Fp2ConfigWrapper<P>>;

impl<P: Fp2Config> QuadExtVarConfig<FpVar<P::Fp>> for Fp2ConfigWrapper<P> {
    fn mul_base_field_var_by_frob_coeff(fe: &mut FpVar<P::Fp>, power: usize) {
        *fe *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
