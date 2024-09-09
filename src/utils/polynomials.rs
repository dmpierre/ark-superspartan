use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use folding_schemes::arith::ccs::CCS;
use folding_schemes::utils::hypercube::BooleanHypercube;
use folding_schemes::utils::multilinear_polynomial::fix_variables;
use folding_schemes::utils::multilinear_polynomial::scalar_mul;
use folding_schemes::utils::virtual_polynomial::ArithErrors;
use folding_schemes::utils::virtual_polynomial::VirtualPolynomial;
use std::sync::Arc;

pub fn compute_inner_sum_for_g<F: PrimeField>(
    matrices_mle: &Vec<DenseMultilinearExtension<F>>,
    z_mle_evals: &Vec<F>,
    log_n: &usize,
) -> Vec<DenseMultilinearExtension<F>> {
    let mut mat_mle_sums = vec![];
    let hypercube_log_n = BooleanHypercube::new(*log_n);
    for mat_mle in matrices_mle.clone() {
        let mut mles_to_sum = vec![];
        for (i, v) in hypercube_log_n.clone().enumerate() {
            let coeff = z_mle_evals[i]; // z^{\tilde}(y)
            let mat_mle_fixed = fix_variables(&mat_mle, &v); // M_j^{\tilde}(a, y)
            let m_j_z = scalar_mul(&mat_mle_fixed, &coeff);
            mles_to_sum.push(m_j_z);
        }
        let mut sum_mle = mles_to_sum[0].clone();
        for i in 1..mles_to_sum.len() {
            sum_mle += mles_to_sum[i].clone();
        }
        mat_mle_sums.push(sum_mle);
    }
    mat_mle_sums
}

pub fn compute_inner_prod_for_g<F: PrimeField>(
    mat_mle_sums: &Vec<DenseMultilinearExtension<F>>,
    ccs: &CCS<F>,
    log_m: &usize,
) -> Result<VirtualPolynomial<F>, ArithErrors> {
    let mut rhs_poly = VirtualPolynomial::new(*log_m);
    for i in 0..ccs.q {
        let c_i = ccs.c[i];
        let start_idx = ccs.S[i][0];
        let mut prod_poly =
            VirtualPolynomial::new_from_mle(&Arc::new(mat_mle_sums[start_idx].clone()), F::one());
        for j in ccs.S[i].iter().skip(1) {
            prod_poly.mul_by_mle(Arc::new(mat_mle_sums[*j].clone()), F::one())?;
        }

        let _ = prod_poly.scalar_mul(&c_i);

        rhs_poly = &rhs_poly + &prod_poly;
    }

    Ok(rhs_poly)
}
