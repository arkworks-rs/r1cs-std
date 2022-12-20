use crate::{fields::fp::FpVar, prelude::*};
use ark_ec::pairing::Pairing;
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
pub trait PairingGadget: Pairing
where
    Self::BaseField: FieldWithVar<Var = FpVar<Self::BaseField>>,
    Self::TargetField: FieldWithVar<Var = Self::GTVar>,
    Self::G1: CurveWithVar<Self::BaseField, Var = Self::G1Var>,
    Self::G2: CurveWithVar<Self::BaseField, Var = Self::G2Var>,
{
    /// An variable representing an element of `G1`.
    /// This is the R1CS equivalent of `E::G1Projective`.
    type G1Var: CurveVar<Self::G1, Self::BaseField>
        + AllocVar<Self::G1, Self::BaseField>
        + AllocVar<Self::G1Affine, Self::BaseField>;

    /// An variable representing an element of `G2`.
    /// This is the R1CS equivalent of `E::G2Projective`.
    type G2Var: CurveVar<Self::G2, Self::BaseField>
        + AllocVar<Self::G2, Self::BaseField>
        + AllocVar<Self::G2Affine, Self::BaseField>;

    /// An variable representing an element of `GT`.
    /// This is the R1CS equivalent of `E::GT`.
    type GTVar: FieldVar<Self::TargetField, Self::BaseField>;

    /// An variable representing cached precomputation  that can speed up
    /// pairings computations. This is the R1CS equivalent of
    /// `E::G1Prepared`.
    type G1PreparedVar: ToBytesGadget<Self::BaseField>
        + AllocVar<Self::G1Prepared, Self::BaseField>
        + Clone
        + Debug;
    /// An variable representing cached precomputation  that can speed up
    /// pairings computations. This is the R1CS equivalent of
    /// `E::G2Prepared`.
    type G2PreparedVar: ToBytesGadget<Self::BaseField>
        + AllocVar<Self::G2Prepared, Self::BaseField>
        + Clone
        + Debug;

    /// Computes a multi-miller loop between elements
    /// of `p` and `q`.
    fn miller_loop_gadget(
        p: &[Self::G1PreparedVar],
        q: &[Self::G2PreparedVar],
    ) -> Result<Self::GTVar, SynthesisError>;

    /// Computes a final exponentiation over `p`.
    fn final_exponentiation_gadget(p: &Self::GTVar) -> Result<Self::GTVar, SynthesisError>;

    /// Computes a pairing over `p` and `q`.
    #[tracing::instrument(target = "r1cs")]
    fn pairing_gadget(
        p: Self::G1PreparedVar,
        q: Self::G2PreparedVar,
    ) -> Result<Self::GTVar, SynthesisError> {
        let tmp = <Self as PairingGadget>::miller_loop_gadget(&[p], &[q])?;
        <Self as PairingGadget>::final_exponentiation_gadget(&tmp)
    }

    /// Computes a product of pairings over the elements in `p` and `q`.
    #[must_use]
    #[tracing::instrument(target = "r1cs")]
    fn product_of_pairings_gadget(
        p: &[Self::G1PreparedVar],
        q: &[Self::G2PreparedVar],
    ) -> Result<Self::GTVar, SynthesisError> {
        let miller_result = <Self as PairingGadget>::miller_loop_gadget(p, q)?;
        <Self as PairingGadget>::final_exponentiation_gadget(&miller_result)
    }

    /// Performs the precomputation to generate `Self::G1PreparedVar`.
    fn prepare_g1(q: &Self::G1Var) -> Result<Self::G1PreparedVar, SynthesisError>;

    /// Performs the precomputation to generate `Self::G2PreparedVar`.
    fn prepare_g2(q: &Self::G2Var) -> Result<Self::G2PreparedVar, SynthesisError>;
}
