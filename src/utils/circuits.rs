use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_relations::r1cs::{ConstraintSynthesizer, SynthesisError};

#[derive(Clone, Debug)]
pub struct TestCircuit<F: PrimeField> {
    pub pub_x: F,
    pub res: F,
    pub pow: usize,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let x_0 = FpVar::new_input(cs.clone(), || Ok(self.pub_x))?;
        let x_res = FpVar::new_witness(cs, || Ok(self.res))?;
        let mut x_computed_res = x_0.clone();
        for _ in 0..self.pow - 1 {
            x_computed_res *= x_0.clone();
        }
        let _ = x_computed_res.enforce_equal(&x_res)?;
        Ok(())
    }
}
