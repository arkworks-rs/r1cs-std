use crate::fields::{fp2::Fp2Var, quadratic_extension::*};
use ark_ff::{
    fields::{Fp4ConfigWrapper, QuadExtConfig},
    Fp4Config,
};

/// A quartic extension field constructed as the tower of a
/// quadratic extension over a quadratic extension field.
/// This is the R1CS equivalent of `ark_ff::Fp4<P>`.
pub type Fp4Var<P> = QuadExtVar<Fp2Var<<P as Fp4Config>::Fp2Config>, Fp4ConfigWrapper<P>>;

impl<P: Fp4Config> QuadExtVarConfig<Fp2Var<P::Fp2Config>> for Fp4ConfigWrapper<P> {
    fn mul_base_field_var_by_frob_coeff(fe: &mut Fp2Var<P::Fp2Config>, power: usize) {
        fe.c0 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        fe.c1 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
