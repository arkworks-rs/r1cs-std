use crate::fields::{fp3::Fp3Var, quadratic_extension::*};
use ark_ff::{fields::fp6_2over3::*, QuadExtConfig};

/// A sextic extension field constructed as the tower of a
/// quadratic extension over a cubic extension field.
/// This is the R1CS equivalent of `ark_ff::fp6_2over3::Fp6<P>`.
pub type Fp6Var<P> = QuadExtVar<Fp3Var<<P as Fp6Config>::Fp3Config>, Fp6ConfigWrapper<P>>;

impl<P: Fp6Config> QuadExtVarConfig<Fp3Var<P::Fp3Config>> for Fp6ConfigWrapper<P> {
    fn mul_base_field_var_by_frob_coeff(fe: &mut Fp3Var<P::Fp3Config>, power: usize) {
        fe.c0 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        fe.c1 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        fe.c2 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
