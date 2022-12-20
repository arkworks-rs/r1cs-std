use crate::fields::{fp2::Fp2Var, quadratic_extension::*, FieldWithVar};
use ark_ff::fields::{Fp4Config, Fp4ConfigWrapper, QuadExtConfig};

/// A quartic extension field constructed as the tower of a
/// quadratic extension over a quadratic extension field.
/// This is the R1CS equivalent of `ark_ff::Fp4<P>`.
pub type Fp4Var<P> = QuadExtVar<Fp4ConfigWrapper<P>>;

impl<P: Fp4Config> QuadExtVarConfig for Fp4ConfigWrapper<P>
where
    Self::BasePrimeField: FieldWithVar,
{
    fn mul_base_field_var_by_frob_coeff(fe: &mut Fp2Var<P::Fp2Config>, power: usize) {
        fe.c0 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
        fe.c1 *= Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}
