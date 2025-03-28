use ark_relations::gr1cs::SynthesisError;

use super::PairingVar as PG;

use crate::{
    fields::{fp::FpVar, fp3::Fp3Var, fp6_2over3::Fp6Var, FieldVar},
    groups::mnt6::{
        AteAdditionCoefficientsVar, AteDoubleCoefficientsVar, G1PreparedVar, G1Var, G2PreparedVar,
        G2ProjectiveExtendedVar, G2Var,
    },
};
use ark_ec::mnt6::{MNT6Config, MNT6};
use core::marker::PhantomData;

/// Specifies the constraints for computing a pairing in a MNT6 bilinear group.
pub struct PairingVar<P: MNT6Config>(PhantomData<P>);

type Fp3G<P> = Fp3Var<<P as MNT6Config>::Fp3Config>;
type Fp6G<P> = Fp6Var<<P as MNT6Config>::Fp6Config>;
/// A variable corresponding to `ark_ec::mnt6::GT`.
pub type GTVar<P> = Fp6G<P>;

impl<P: MNT6Config> PairingVar<P> {
    #[tracing::instrument(target = "gr1cs", skip(r))]
    pub(crate) fn doubling_step_for_flipped_miller_loop(
        r: &G2ProjectiveExtendedVar<P>,
    ) -> Result<(G2ProjectiveExtendedVar<P>, AteDoubleCoefficientsVar<P>), SynthesisError> {
        let a = r.t.square()?;
        let b = r.x.square()?;
        let c = r.y.square()?;
        let d = c.square()?;
        let e = (&r.x + &c).square()? - &b - &d;
        let f = b.double()? + &b + &(&a * P::TWIST_COEFF_A);
        let g = f.square()?;

        let d_eight = d.double()?.double()?.double()?;

        let e2 = e.double()?;
        let x = &g - e2.double()?;
        let y = &f * (e2 - &x) - d_eight;
        let z = (&r.y + &r.z).square()? - &c - &r.z.square()?;
        let t = z.square()?;

        let r2 = G2ProjectiveExtendedVar { x, y, z, t };
        let coeff = AteDoubleCoefficientsVar {
            c_h: (&r2.z + &r.t).square()? - &r2.t - &a,
            c_4c: c.double()?.double()?,
            c_j: (&f + &r.t).square()? - &g - &a,
            c_l: (&f + &r.x).square()? - &g - &b,
        };

        Ok((r2, coeff))
    }

    #[tracing::instrument(target = "gr1cs", skip(r))]
    pub(crate) fn mixed_addition_step_for_flipped_miller_loop(
        x: &Fp3G<P>,
        y: &Fp3G<P>,
        r: &G2ProjectiveExtendedVar<P>,
    ) -> Result<(G2ProjectiveExtendedVar<P>, AteAdditionCoefficientsVar<P>), SynthesisError> {
        let a = y.square()?;
        let b = &r.t * x;
        let d = ((&r.z + y).square()? - &a - &r.t) * &r.t;
        let h = &b - &r.x;
        let i = h.square()?;
        let e = i.double()?.double()?;
        let j = &h * &e;
        let v = &r.x * &e;
        let ry2 = r.y.double()?;
        let l1 = &d - &ry2;

        let x = l1.square()? - &j - &v.double()?;
        let y = &l1 * &(&v - &x) - &j * ry2;
        let z = (&r.z + &h).square()? - &r.t - &i;
        let t = z.square()?;

        let r2 = G2ProjectiveExtendedVar {
            x,
            y,
            z: z.clone(),
            t,
        };
        let coeff = AteAdditionCoefficientsVar { c_l1: l1, c_rz: z };

        Ok((r2, coeff))
    }

    #[tracing::instrument(target = "gr1cs", skip(p, q))]
    pub(crate) fn ate_miller_loop(
        p: &G1PreparedVar<P>,
        q: &G2PreparedVar<P>,
    ) -> Result<Fp6G<P>, SynthesisError> {
        let zero = FpVar::<P::Fp>::zero();
        let l1_coeff = Fp3Var::new(p.x.clone(), zero.clone(), zero) - &q.x_over_twist;

        let mut f = Fp6G::<P>::one();

        let mut add_idx: usize = 0;

        // code below gets executed for all bits (EXCEPT the MSB itself) of
        // mnt6_param_p (skipping leading zeros) in MSB to LSB order
        let y_over_twist_neg = &q.y_over_twist.negate()?;
        for (dbl_idx, bit) in P::ATE_LOOP_COUNT.iter().skip(1).enumerate() {
            let dc = &q.double_coefficients[dbl_idx];

            let g_rr_at_p = Fp6G::<P>::new(
                &dc.c_l - &dc.c_4c - &dc.c_j * &p.x_twist,
                &dc.c_h * &p.y_twist,
            );

            f = f.square()? * &g_rr_at_p;

            let g_rq_at_p;
            // Compute l_{R,Q}(P) if bit == 1, and l_{R,-Q}(P) if bit == -1
            if *bit == 1 {
                let ac = &q.addition_coefficients[add_idx];
                add_idx += 1;

                g_rq_at_p = Fp6G::<P>::new(
                    &ac.c_rz * &p.y_twist,
                    (&q.y_over_twist * &ac.c_rz + &l1_coeff * &ac.c_l1).negate()?,
                );
            } else if *bit == -1 {
                let ac = &q.addition_coefficients[add_idx];
                add_idx += 1;

                g_rq_at_p = Fp6G::<P>::new(
                    &ac.c_rz * &p.y_twist,
                    (y_over_twist_neg * &ac.c_rz + &l1_coeff * &ac.c_l1).negate()?,
                );
            } else {
                continue;
            }

            f *= &g_rq_at_p;
        }

        if P::ATE_IS_LOOP_COUNT_NEG {
            let ac = &q.addition_coefficients[add_idx];

            let g_rnegr_at_p = Fp6Var::new(
                &ac.c_rz * &p.y_twist,
                (&q.y_over_twist * &ac.c_rz + &(l1_coeff * &ac.c_l1)).negate()?,
            );
            f = (f * &g_rnegr_at_p).inverse()?;
        }

        Ok(f)
    }

    #[tracing::instrument(target = "gr1cs")]
    pub(crate) fn final_exponentiation(value: &Fp6G<P>) -> Result<GTVar<P>, SynthesisError> {
        let value_inv = value.inverse()?;
        let value_to_first_chunk = Self::final_exponentiation_first_chunk(value, &value_inv)?;
        let value_inv_to_first_chunk = Self::final_exponentiation_first_chunk(&value_inv, value)?;
        Self::final_exponentiation_last_chunk(&value_to_first_chunk, &value_inv_to_first_chunk)
    }

    #[tracing::instrument(target = "gr1cs", skip(elt, elt_inv))]
    fn final_exponentiation_first_chunk(
        elt: &Fp6G<P>,
        elt_inv: &Fp6G<P>,
    ) -> Result<Fp6G<P>, SynthesisError> {
        // (q^3-1)*(q+1)

        // elt_q3 = elt^(q^3)
        let elt_q3 = elt.unitary_inverse()?;
        // elt_q3_over_elt = elt^(q^3-1)
        let elt_q3_over_elt = elt_q3 * elt_inv;
        // alpha = elt^((q^3-1) * q)
        let alpha = elt_q3_over_elt.frobenius_map(1)?;
        // beta = elt^((q^3-1)*(q+1)
        Ok(alpha * &elt_q3_over_elt)
    }

    #[tracing::instrument(target = "gr1cs", skip(elt, elt_inv))]
    fn final_exponentiation_last_chunk(
        elt: &Fp6G<P>,
        elt_inv: &Fp6G<P>,
    ) -> Result<Fp6G<P>, SynthesisError> {
        let elt_q = elt.frobenius_map(1)?;

        let w1_part = elt_q.cyclotomic_exp(&P::FINAL_EXPONENT_LAST_CHUNK_1)?;
        let w0_part = if P::FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG {
            elt_inv.cyclotomic_exp(&P::FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0)?
        } else {
            elt.cyclotomic_exp(&P::FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0)?
        };

        Ok(w1_part * &w0_part)
    }
}

impl<P: MNT6Config> PG<MNT6<P>> for PairingVar<P> {
    type G1Var = G1Var<P>;
    type G2Var = G2Var<P>;
    type G1PreparedVar = G1PreparedVar<P>;
    type G2PreparedVar = G2PreparedVar<P>;
    type GTVar = GTVar<P>;

    #[tracing::instrument(target = "gr1cs")]
    fn miller_loop(
        ps: &[Self::G1PreparedVar],
        qs: &[Self::G2PreparedVar],
    ) -> Result<Self::GTVar, SynthesisError> {
        let mut result = Fp6G::<P>::one();
        for (p, q) in ps.iter().zip(qs) {
            result *= Self::ate_miller_loop(p, q)?;
        }

        Ok(result)
    }

    #[tracing::instrument(target = "gr1cs")]
    fn final_exponentiation(r: &Self::GTVar) -> Result<Self::GTVar, SynthesisError> {
        Self::final_exponentiation(r)
    }

    #[tracing::instrument(target = "gr1cs")]
    fn prepare_g1(p: &Self::G1Var) -> Result<Self::G1PreparedVar, SynthesisError> {
        Self::G1PreparedVar::from_group_var(p)
    }

    #[tracing::instrument(target = "gr1cs")]
    fn prepare_g2(q: &Self::G2Var) -> Result<Self::G2PreparedVar, SynthesisError> {
        Self::G2PreparedVar::from_group_var(q)
    }
}
