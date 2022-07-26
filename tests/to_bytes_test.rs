use ark_ec::PairingEngine;
use ark_ff::{to_bytes, Zero};
use ark_mnt4_298::MNT4_298;
use ark_mnt6_298::MNT6_298;
use ark_r1cs_std::{
    alloc::AllocVar, fields::nonnative::NonNativeFieldVar, R1CSVar, ToBitsGadget, ToBytesGadget,
};
use ark_relations::r1cs::ConstraintSystem;

#[test]
fn to_bytes_test() {
    let cs = ConstraintSystem::<<MNT6_298 as PairingEngine>::Fr>::new_ref();

    let target_test_elem = <MNT4_298 as PairingEngine>::Fr::from(123456u128);
    let target_test_gadget = NonNativeFieldVar::<
        <MNT4_298 as PairingEngine>::Fr,
        <MNT6_298 as PairingEngine>::Fr,
    >::new_witness(cs, || Ok(target_test_elem))
    .unwrap();

    let target_to_bytes: Vec<u8> = target_test_gadget
        .to_bytes()
        .unwrap()
        .iter()
        .map(|v| v.value().unwrap())
        .collect();

    // 123456 = 65536 + 226 * 256 + 64
    assert_eq!(target_to_bytes[0], 64);
    assert_eq!(target_to_bytes[1], 226);
    assert_eq!(target_to_bytes[2], 1);

    for byte in target_to_bytes.iter().skip(3) {
        assert_eq!(*byte, 0);
    }

    assert_eq!(to_bytes!(target_test_elem).unwrap(), target_to_bytes);
}

#[test]
fn to_bits_test() {
    type F = ark_bls12_377::Fr;
    type CF = ark_bls12_377::Fq;

    let cs = ConstraintSystem::<CF>::new_ref();
    let f = F::zero();

    let f_var = NonNativeFieldVar::<F, CF>::new_input(cs.clone(), || Ok(f)).unwrap();
    f_var.to_bits_le().unwrap();
}
