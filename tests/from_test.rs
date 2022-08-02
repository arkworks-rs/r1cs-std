use ark_r1cs_std::{
    alloc::AllocVar,
    fields::nonnative::{NonNativeFieldMulResultVar, NonNativeFieldVar},
    R1CSVar,
};
use ark_relations::r1cs::ConstraintSystem;
use ark_std::UniformRand;

#[test]
fn from_test() {
    type F = ark_bls12_377::Fr;
    type CF = ark_bls12_377::Fq;

    let mut rng = ark_std::test_rng();
    let cs = ConstraintSystem::<CF>::new_ref();
    let f = F::rand(&mut rng);

    let f_var = NonNativeFieldVar::<F, CF>::new_input(cs.clone(), || Ok(f)).unwrap();
    let f_var_converted = NonNativeFieldMulResultVar::<F, CF>::from(&f_var);
    let f_var_converted_reduced = f_var_converted.reduce().unwrap();

    let f_var_value = f_var.value().unwrap();
    let f_var_converted_reduced_value = f_var_converted_reduced.value().unwrap();

    assert_eq!(f_var_value, f_var_converted_reduced_value);
}
