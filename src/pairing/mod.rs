use crate::prelude::*;
use ark_ec::PairingEngine;
use ark_ff::Field;
use ark_relations::r1cs::SynthesisError;
use core::fmt::Debug;

/// This module implements pairings for BLS12 bilinear groups.
pub mod bls12;
/// This module implements pairings for MNT4 bilinear groups.
pub mod mnt4;
/// This module implements pairings for MNT6 bilinear groups.
pub mod mnt6;

/// Specifies the constraints for computing a pairing in the yybilinear group
/// `E`.
pub trait PairingVar<E: PairingEngine, ConstraintF: Field = <E as PairingEngine>::Fq> {
    /// An variable representing an element of `G1`.
    /// This is the R1CS equivalent of `E::G1Projective`.
    type G1Var: CurveVar<E::G1Projective, ConstraintF>
        + AllocVar<E::G1Projective, ConstraintF>
        + AllocVar<E::G1Affine, ConstraintF>;

    /// An variable representing an element of `G2`.
    /// This is the R1CS equivalent of `E::G2Projective`.
    type G2Var: CurveVar<E::G2Projective, ConstraintF>
        + AllocVar<E::G2Projective, ConstraintF>
        + AllocVar<E::G2Affine, ConstraintF>;

    /// An variable representing an element of `GT`.
    /// This is the R1CS equivalent of `E::GT`.
    type GTVar: FieldVar<E::Fqk, ConstraintF>;

    /// An variable representing cached precomputation  that can speed up
    /// pairings computations. This is the R1CS equivalent of
    /// `E::G1Prepared`.
    type G1PreparedVar: ToBytesGadget<ConstraintF>
        + AllocVar<E::G1Prepared, ConstraintF>
        + Clone
        + Debug;
    /// An variable representing cached precomputation  that can speed up
    /// pairings computations. This is the R1CS equivalent of
    /// `E::G2Prepared`.
    type G2PreparedVar: ToBytesGadget<ConstraintF>
        + AllocVar<E::G2Prepared, ConstraintF>
        + Clone
        + Debug;

    /// Computes a multi-miller loop between elements
    /// of `p` and `q`.
    fn miller_loop(
        p: &[Self::G1PreparedVar],
        q: &[Self::G2PreparedVar],
    ) -> Result<Self::GTVar, SynthesisError>;

    /// Computes a final exponentiation over `p`.
    fn final_exponentiation(p: &Self::GTVar) -> Result<Self::GTVar, SynthesisError>;

    /// Computes a pairing over `p` and `q`.
    #[tracing::instrument(target = "r1cs")]
    fn pairing(
        p: Self::G1PreparedVar,
        q: Self::G2PreparedVar,
    ) -> Result<Self::GTVar, SynthesisError> {
        let tmp = Self::miller_loop(&[p], &[q])?;
        Self::final_exponentiation(&tmp)
    }

    /// Computes a product of pairings over the elements in `p` and `q`.
    #[must_use]
    #[tracing::instrument(target = "r1cs")]
    fn product_of_pairings(
        p: &[Self::G1PreparedVar],
        q: &[Self::G2PreparedVar],
    ) -> Result<Self::GTVar, SynthesisError> {
        let miller_result = Self::miller_loop(p, q)?;
        Self::final_exponentiation(&miller_result)
    }

    /// Performs the precomputation to generate `Self::G1PreparedVar`.
    fn prepare_g1(q: &Self::G1Var) -> Result<Self::G1PreparedVar, SynthesisError>;

    /// Performs the precomputation to generate `Self::G2PreparedVar`.
    fn prepare_g2(q: &Self::G2Var) -> Result<Self::G2PreparedVar, SynthesisError>;
}
