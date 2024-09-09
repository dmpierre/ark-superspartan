use crate::utils::{
    compute_evaluations_over_hypercube, compute_gamma_challenge, compute_tau_challenge,
};
use crate::utils::{
    fix_last_variables, pad_wnts_instance,
    polynomials::{compute_inner_prod_for_g, compute_inner_sum_for_g},
};
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_crypto_primitives::sponge::Absorb;
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use espresso_subroutines::PolyIOPErrors;
use folding_schemes::utils::multilinear_polynomial::scalar_mul;
use folding_schemes::utils::sum_check::structs::IOPProof;
use folding_schemes::utils::sum_check::IOPSumCheck;
use folding_schemes::utils::sum_check::SumCheck;
use folding_schemes::{
    arith::ccs::CCS,
    utils::{
        hypercube::BooleanHypercube,
        mle::dense_vec_to_dense_mle,
        virtual_polynomial::{build_eq_x_r, ArithErrors, VirtualPolynomial},
    },
};
use std::marker::PhantomData;
use std::sync::Arc;

pub struct Prover<F: PrimeField + Absorb> {
    _f: PhantomData<F>,
}

impl<F: PrimeField + Absorb> Prover<F> {
    /// Preprocess witness and instance so that they have equal size n/2, with n a power of 2
    /// Returns a tuple (n added elements to witness, n added elements to instance)
    pub fn preprocess(witness: &mut Vec<F>, instance: &mut Vec<F>) -> (usize, usize) {
        pad_wnts_instance(witness, instance)
    }

    /// Computes the g polynomial used in the first invocation sumcheck
    fn compute_g_polynomial(
        tau: &[F],
        matrices_mle: &Vec<DenseMultilinearExtension<F>>,
        z_mle_evals: &Vec<F>,
        ccs: &CCS<F>,
    ) -> Result<VirtualPolynomial<F>, ArithErrors> {
        let mat_mle_sums = compute_inner_sum_for_g(matrices_mle, z_mle_evals, &ccs.s_prime);
        let mut inner_prod = compute_inner_prod_for_g(&mat_mle_sums, ccs, &ccs.s)?;
        let eq_tau_a = build_eq_x_r(tau)?;
        inner_prod.mul_by_mle(eq_tau_a.clone(), F::one())?;
        Ok(inner_prod)
    }

    /// Computes the g polynomial used in the first invocation sumcheck
    /// Returns claimed evaluations for each term of this batched polynomial
    fn compute_batched_polynomial(
        gamma: &F,
        matrices_mle: &Vec<DenseMultilinearExtension<F>>,
        z_mle: &DenseMultilinearExtension<F>,
        z_mle_evals: &Vec<F>,
        r_a: &[F],
        log_n: usize,
    ) -> Result<(VirtualPolynomial<F>, Vec<F>), ArithErrors> {
        let mut claimed_mle_sums = vec![]; // verifier will have access to the claimed
                                           // sums and will compare them to the claimed sum he
                                           // obtained when engaging in the second part of the
                                           // sumcheck protocol
        let mut mles_to_rlc = vec![];
        let mut gamma_coeff = F::one();
        for mat_mle in matrices_mle.clone() {
            let mut sum = F::zero();
            let hypercube_log_n = BooleanHypercube::new(log_n);
            let mat_mle_fixed = fix_last_variables(&mat_mle, &r_a);
            let times_gamma = scalar_mul(&mat_mle_fixed, &gamma_coeff);
            for (i, v) in hypercube_log_n.enumerate() {
                let eval_mat_mle = mat_mle_fixed
                    .evaluate(&v)
                    .ok_or(ArithErrors::ShouldNotArrive)?; // TODO: not very representative
                                                           // err here
                let eval_z_mle = z_mle_evals[i];
                sum += eval_mat_mle * eval_z_mle;
            }
            claimed_mle_sums.push(sum);
            let mut vp = VirtualPolynomial::new_from_mle(&Arc::new(times_gamma), F::one());
            vp.mul_by_mle(Arc::new(z_mle.clone()), F::one())?;
            mles_to_rlc.push(vp);
            gamma_coeff *= gamma;
        }

        let mut batched_g = mles_to_rlc[0].clone();
        for mle in mles_to_rlc.iter().skip(1) {
            batched_g = &batched_g + mle;
        }
        Ok((batched_g, claimed_mle_sums))
    }

    pub fn prove(
        matrices_mle: &Vec<DenseMultilinearExtension<F>>,
        ccs: &CCS<F>,
        instance: &Vec<F>,
        z: &Vec<F>,
        poseidon_config: &PoseidonConfig<F>,
    ) -> Result<
        (
            VirtualPolynomial<F>,
            IOPProof<F>,
            VirtualPolynomial<F>,
            IOPProof<F>,
            Vec<F>,
        ),
        PolyIOPErrors,
    > {
        let z_mle = Prover::compute_mle_vec(ccs.s_prime, z);
        let z_mle_hypercube_evals = compute_evaluations_over_hypercube(&z_mle, ccs.s_prime);

        let mut transcript = PoseidonSponge::new(poseidon_config);

        // 1. Run sumcheck of g(), ensure that sum is zero
        let tau = compute_tau_challenge(&matrices_mle, &instance, &mut transcript, ccs.s);
        let g = Prover::compute_g_polynomial(&tau, &matrices_mle, &z_mle_hypercube_evals, &ccs)
            .or(Err(PolyIOPErrors::InvalidProver(
                "Failed to compute batched polynomial".to_string(),
            )))?;

        let sumcheck_proof_g = IOPSumCheck::<F, PoseidonSponge<F>>::prove(&g, &mut transcript)?;

        if IOPSumCheck::<F, PoseidonSponge<F>>::extract_sum(&sumcheck_proof_g) != F::zero() {
            return Err(PolyIOPErrors::InvalidProver(
                "Claimed sum for g is not 0".to_string(),
            ));
        }

        // 2. Run sumcheck for batched poly
        let gamma = compute_gamma_challenge(&sumcheck_proof_g.point, &mut transcript)[0];
        let (batched_poly, claimed_mle_sums) = Prover::compute_batched_polynomial(
            &gamma,
            &matrices_mle,
            &z_mle,
            &z_mle_hypercube_evals,
            &sumcheck_proof_g.point,
            ccs.s_prime,
        )
        .or(Err(PolyIOPErrors::InvalidProver(
            "Failed to compute batched polynomial".to_string(),
        )))?;

        let sumcheck_proof_batched_poly =
            IOPSumCheck::<F, PoseidonSponge<F>>::prove(&batched_poly, &mut transcript)?;

        Ok((
            g,
            sumcheck_proof_g,
            batched_poly,
            sumcheck_proof_batched_poly,
            claimed_mle_sums,
        ))
    }

    /// P will provide V oracle access to the MLE of the witness
    pub fn compute_mle_vec(n_vars: usize, v: &Vec<F>) -> DenseMultilinearExtension<F> {
        dense_vec_to_dense_mle(n_vars, v)
    }
}
