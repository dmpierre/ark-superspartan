use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_std::log2;
use folding_schemes::{
    arith::{ccs::CCS, r1cs::R1CS},
    utils::mle::{matrix_to_mle, vec_to_dense_mle},
};
use std::marker::PhantomData;
use utils::pad_r1cs;

pub mod prover;
pub mod utils;
pub mod verifier;

pub struct SuperSpartan<F: PrimeField> {
    _f: PhantomData<F>,
}

// TODO: remove extra infos about the preprocessed R1CS
pub enum ConstraintSystem<F: PrimeField> {
    R1CS((R1CS<F>, Vec<F>, usize, usize)), // r1cs, instance vec, how many padded zeros added to
    // instance, final length of z
    CCS(CCS<F>),
}

impl<F: PrimeField> SuperSpartan<F> {
    /// Preprocess the given constraint system, either in R1CS or in CCS format
    pub fn preprocess(
        cs: &mut ConstraintSystem<F>,
    ) -> (
        Vec<DenseMultilinearExtension<F>>,
        DenseMultilinearExtension<F>,
        CCS<F>,
    ) {
        // Initialize padded CCS
        let (preprocessed_ccs, instance) = match cs {
            ConstraintSystem::R1CS((r1cs, instance, n_instance_padded_zeros, len_final_z)) => {
                pad_r1cs(r1cs, r1cs.l + 1, *n_instance_padded_zeros);
                r1cs.l = instance.len();
                r1cs.A.n_cols = *len_final_z;
                r1cs.B.n_cols = *len_final_z;
                r1cs.C.n_cols = *len_final_z;
                (CCS::<F>::from_r1cs(r1cs.clone()), instance)
            }
            ConstraintSystem::CCS(_) => {
                panic!("Preprocessing for CCS is not supported yet!");
            }
        };

        // Compute MLEs for matrices and instance vector
        let matrices_mle = preprocessed_ccs
            .M
            .clone()
            .iter()
            .map(|mat| matrix_to_mle(mat.clone()).to_dense_multilinear_extension())
            .collect::<Vec<DenseMultilinearExtension<F>>>();

        let instance_mle = vec_to_dense_mle(log2(instance.len()) as usize, instance);

        // Compute g(a) polynomial
        (matrices_mle, instance_mle, preprocessed_ccs)
    }
}

#[cfg(test)]
mod tests {
    use self::utils::{circuits::TestCircuit, get_default_poseidon_sponge_config};
    use super::*;
    use crate::verifier::Verifier;
    use crate::{
        prover::Prover, utils::extract_witness_and_instance_assignments,
        ConstraintSystem as SuperSpartanCS,
    };
    use ark_bn254::Fr;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    use folding_schemes::folding::nova::get_r1cs_from_cs;

    #[test]
    fn test_superspartan() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let circuit = TestCircuit {
            pub_x: Fr::from(2),
            res: Fr::from(536870912),
            pow: 29,
        };
        circuit.clone().generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let poseidon_config = get_default_poseidon_sponge_config();

        // pad r1cs
        let (mut wtns, mut instance) = extract_witness_and_instance_assignments(cs);
        let r1cs = get_r1cs_from_cs(circuit).unwrap();
        let (_, added_instance) = Prover::preprocess(&mut wtns, &mut instance);

        let (matrices_mle, instance_mle, ccs) =
            SuperSpartan::preprocess(&mut SuperSpartanCS::R1CS((
                r1cs,
                instance.clone(),
                added_instance,
                wtns.len() + instance.len(),
            )));

        let mut z = instance.clone();
        z.extend(wtns.clone());
        let witness_mle_oracle =
            Prover::compute_mle_vec((log2(wtns.len())) as usize, &wtns.clone());

        let (g, sumcheck_proof_g_poly, batched_poly, sumcheck_proof_batched_poly, claimed_mle_sums) =
            Prover::prove(&matrices_mle, &ccs, &instance, &z, &poseidon_config).unwrap();
        let (_, _) = Verifier::verify(
            &ccs,
            &instance,
            &g,
            &sumcheck_proof_g_poly,
            &batched_poly,
            &sumcheck_proof_batched_poly,
            &claimed_mle_sums,
            &instance_mle,
            &witness_mle_oracle,
            &matrices_mle,
            &poseidon_config,
        )
        .unwrap();
    }
}
