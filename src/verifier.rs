use crate::utils::compute_gamma_challenge;
use crate::utils::compute_tau_challenge;
use crate::utils::fix_last_variables;
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_crypto_primitives::sponge::Absorb;
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use espresso_subroutines::PolyIOPErrors;
use folding_schemes::utils::sum_check::structs::IOPProof;
use folding_schemes::utils::sum_check::IOPSumCheck;
use folding_schemes::utils::sum_check::SumCheck;
use folding_schemes::utils::sum_check::SumCheckSubClaim;
use folding_schemes::utils::virtual_polynomial::build_eq_x_r;
use folding_schemes::{arith::ccs::CCS, utils::virtual_polynomial::VirtualPolynomial};
use std::marker::PhantomData;

pub struct Verifier<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField + Absorb> Verifier<F> {
    pub fn verify(
        ccs: &CCS<F>,
        instance: &Vec<F>,
        g: &VirtualPolynomial<F>,
        sumcheck_proof_g: &IOPProof<F>,
        batched_poly: &VirtualPolynomial<F>,
        sumcheck_proof_batched_poly: &IOPProof<F>,
        claimed_mle_sums: &Vec<F>,
        instance_mle: &DenseMultilinearExtension<F>,
        witness_mle_oracle: &DenseMultilinearExtension<F>,
        matrices_mle: &Vec<DenseMultilinearExtension<F>>,
        poseidon_config: &PoseidonConfig<F>,
    ) -> Result<(SumCheckSubClaim<F>, SumCheckSubClaim<F>), PolyIOPErrors> {
        let mut transcript = PoseidonSponge::new(&poseidon_config);

        // 1. Verify sumcheck proof for g
        // Verifier will check whether g(r_a) is correct below
        let tau = compute_tau_challenge(&matrices_mle, &instance, &mut transcript, ccs.s);
        let verify_sumcheck_proof_g = IOPSumCheck::<F, PoseidonSponge<F>>::verify(
            F::zero(),
            &sumcheck_proof_g,
            &g.aux_info,
            &mut transcript,
        )?;

        // 2. Verify sumcheck proof for the batched polynomial
        // Verifier will check whether batched_poly(r_y) is correct below
        let gamma = compute_gamma_challenge(&sumcheck_proof_g.point, &mut transcript)[0];
        let claimed_sum_batched_poly =
            IOPSumCheck::<F, PoseidonSponge<F>>::extract_sum(&sumcheck_proof_batched_poly);
        let verify_sumcheck_proof_batched_poly = IOPSumCheck::<F, PoseidonSponge<F>>::verify(
            claimed_sum_batched_poly,
            sumcheck_proof_batched_poly,
            &batched_poly.aux_info,
            &mut transcript,
        )?;

        // 3. Check that the claimed sumcheck sum of the batched/rlc polynomial of the mles
        // matches what has been sent by the prover
        let claimed_batched_poly_sum =
            IOPSumCheck::<F, PoseidonSponge<F>>::extract_sum(&sumcheck_proof_batched_poly);
        let mut gamma_coeff = F::one();
        let mut sum_from_prover_values = F::zero();
        for claim in claimed_mle_sums {
            sum_from_prover_values += *claim * gamma_coeff;
            gamma_coeff *= gamma;
        }

        if sum_from_prover_values != claimed_batched_poly_sum {
            return Err(PolyIOPErrors::InvalidVerifier("Claimed sum of the batched poly is different to when summing the prover provided MLE sums".to_string()))?;
        }

        // 4. Check that the last evaluation of the sumchecked batched poly is correct
        let r_y = &sumcheck_proof_batched_poly.point;
        let v_w = witness_mle_oracle.evaluate(&r_y[..r_y.len() - 1]).ok_or(
            PolyIOPErrors::InvalidVerifier("Failed to evaluate oracle witness MLE".to_string()),
        )?;
        let v_instance =
            instance_mle
                .evaluate(&r_y[..r_y.len() - 1])
                .ok_or(PolyIOPErrors::InvalidVerifier(
                    "Failed to evaluate instance MLE".to_string(),
                ))?;

        // Slightly differs from the formula in the paper, since our mle is little endian encoded
        // Also, the instance comes first in our z vector
        let v_z = (F::one() - r_y[r_y.len() - 1]) * v_instance + r_y[r_y.len() - 1] * v_w;

        let mut gamma_coeff = F::one();
        let mut batched_poly_computed_last_eval = F::zero();
        for mat_mle in matrices_mle {
            let mat_mle_fixed = fix_last_variables(&mat_mle, &sumcheck_proof_g.point);
            let mle_eval = mat_mle_fixed
                .evaluate(&r_y)
                .ok_or(PolyIOPErrors::InvalidVerifier(
                    "Failed to evaluate matrices MLE at r_y".to_string(),
                ))?;
            batched_poly_computed_last_eval += gamma_coeff * v_z * mle_eval;
            gamma_coeff *= gamma;
        }

        if batched_poly_computed_last_eval != verify_sumcheck_proof_batched_poly.expected_evaluation
        {
            return Err(PolyIOPErrors::InvalidVerifier(
                "computed_batched_poly(r_y) != expected_batched_poly(r_y)".to_string(),
            ));
        }

        // 5. Check that the last evaluation of the sumchecked poly g is correct
        // I.e. checking the g(r_a) is correct
        // Now, V knows that the prover claims regarding the values for the sum over the hypercube
        // M^{\tilde}(r_a, y) \cdot z^{\tilde}(y) are correct.
        // V can now compute the evaluation for g(r_a) and compare it to the expected evaluation.
        let eq_tau_a =
            build_eq_x_r(&tau).or_else(|_| Err(PolyIOPErrors::InvalidVerifier("".to_string())))?;
        let verifier_eq_ra =
            eq_tau_a
                .evaluate(&sumcheck_proof_g.point)
                .ok_or(PolyIOPErrors::InvalidVerifier(
                    "Failed to evaluate eq_tau(r_a)".to_string(),
                ))?;
        let mut verifier_g_ra = F::zero();
        for i in 0..ccs.q {
            let c_i = ccs.c[i];
            let mut intermediate_prod = F::one();
            for j in ccs.S[i].clone() {
                intermediate_prod *= claimed_mle_sums[j]; // M(r_a, y) \cot z(y);
            }
            verifier_g_ra += c_i * intermediate_prod;
        }
        verifier_g_ra *= verifier_eq_ra;

        if verifier_g_ra != verify_sumcheck_proof_g.expected_evaluation {
            return Err(PolyIOPErrors::InvalidVerifier(
                "computed_g(r_a) != expected_g(r_a)".to_string(),
            ));
        }

        Ok((verify_sumcheck_proof_g, verify_sumcheck_proof_batched_poly))
    }
}
