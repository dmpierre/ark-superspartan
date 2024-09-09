use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_crypto_primitives::sponge::Absorb;
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_crypto_primitives::sponge::FieldBasedCryptographicSponge;
use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_relations::r1cs::ConstraintSystemRef;
use folding_schemes::{arith::r1cs::R1CS, utils::hypercube::BooleanHypercube};
use std::ops::Deref;

pub mod circuits;
pub mod polynomials;

pub fn compute_tau_challenge<F: PrimeField + Absorb>(
    mat_mle: &Vec<DenseMultilinearExtension<F>>,
    instance: &[F],
    transcript: &mut PoseidonSponge<F>,
    to_squeeze: usize,
) -> Vec<F> {
    for mat in mat_mle {
        transcript.absorb(&mat.evaluations);
    }
    for element in instance {
        transcript.absorb(element);
    }
    transcript.squeeze_native_field_elements(to_squeeze)
}

pub fn compute_gamma_challenge<F: PrimeField + Absorb>(
    r_a: &[F], // random point when computing g(r_a)
    transcript: &mut PoseidonSponge<F>,
) -> Vec<F> {
    transcript.absorb(&r_a);
    transcript.squeeze_field_elements(1)
}

pub fn compute_evaluations_over_hypercube<F: PrimeField>(
    mle: &DenseMultilinearExtension<F>,
    hypercube_size: usize,
) -> Vec<F> {
    let hypercube = BooleanHypercube::new(hypercube_size);

    hypercube
        .clone()
        .map(|v| mle.evaluate(&v).unwrap())
        .collect::<Vec<F>>()
}

fn pad_cols<F: PrimeField>(
    row: &mut Vec<(F, usize)>,
    len_instance: usize, // to check if the current z element is an instance value
    len_padded_instance: usize, // to offset the index of witness elements by the corresponding
                         // added instance elements
) {
    for val in row.iter_mut() {
        // offset all wtns element by the number of zeros we added to padding
        if val.1 > len_instance - 1 {
            val.1 += len_padded_instance as usize;
        }
    }
}

// TODO: have this, but for CCS directly
pub fn pad_r1cs<F: PrimeField>(
    r1cs: &mut R1CS<F>,
    len_instance: usize,
    len_padded_instance: usize,
) -> usize {
    // n should be a power of 2
    for row in r1cs.A.coeffs.iter_mut() {
        pad_cols(row, len_instance, len_padded_instance);
    }

    for row in r1cs.B.coeffs.iter_mut() {
        pad_cols(row, len_instance, len_padded_instance);
    }

    for row in r1cs.C.coeffs.iter_mut() {
        pad_cols(row, len_instance, len_padded_instance);
    }

    // m should be a power of 2
    let expected_n_rows = r1cs.A.n_rows.next_power_of_two();
    while r1cs.A.n_rows < expected_n_rows {
        r1cs.A.coeffs.push(vec![]);
        r1cs.B.coeffs.push(vec![]);
        r1cs.C.coeffs.push(vec![]);

        r1cs.A.n_rows += 1;
        r1cs.B.n_rows += 1;
        r1cs.C.n_rows += 1;
    }
    expected_n_rows
}

pub fn compute_next_pow2_wtns_instance<F: PrimeField>(wtns: &[F], instance: &[F]) -> usize {
    ((wtns.len() + instance.len()).next_power_of_two() + 1).next_power_of_two() / 2
}

// TODO: this is not finding the lowest size vec possible, rewrite
pub(crate) fn pad_wnts_instance<F: PrimeField>(
    wtns: &mut Vec<F>,
    instance: &mut Vec<F>,
) -> (usize, usize) {
    let next_power_of_two_div_2 = compute_next_pow2_wtns_instance(wtns, instance);
    let mut added_wtns = 0;
    let mut added_instance = 0;
    while wtns.len() < next_power_of_two_div_2 {
        wtns.push(F::zero());
        added_wtns += 1;
    }
    while instance.len() < next_power_of_two_div_2 {
        instance.push(F::zero());
        added_instance += 1;
    }
    (added_wtns, added_instance)
}

// from: https://github.com/EspressoSystems/hyperplonk/blob/dc194f83ef5cae523b869f7256f314bdbeb2a42c/arithmetic/src/multilinear_polynomial.rs#L251
pub fn fix_last_variables<F: PrimeField>(
    poly: &DenseMultilinearExtension<F>,
    partial_point: &[F],
) -> DenseMultilinearExtension<F> {
    assert!(
        partial_point.len() <= poly.num_vars,
        "invalid size of partial point"
    );
    let nv = poly.num_vars;
    let mut poly = poly.evaluations.to_vec();
    let dim = partial_point.len();
    // evaluate single variable of partial point from left to right
    for (i, point) in partial_point.iter().rev().enumerate().take(dim) {
        poly = fix_last_variable_helper(&poly, nv - i, point);
    }

    DenseMultilinearExtension::<F>::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
}

// from: https://github.com/EspressoSystems/hyperplonk/blob/dc194f83ef5cae523b869f7256f314bdbeb2a42c/arithmetic/src/multilinear_polynomial.rs#L251
fn fix_last_variable_helper<F: PrimeField>(data: &[F], nv: usize, point: &F) -> Vec<F> {
    let half_len = 1 << (nv - 1);
    let mut res = vec![F::zero(); half_len];

    // evaluate single variable of partial point from left to right
    #[cfg(not(feature = "parallel"))]
    for b in 0..half_len {
        res[b] = data[b] + (data[b + half_len] - data[b]) * point;
    }

    #[cfg(feature = "parallel")]
    res.par_iter_mut().enumerate().for_each(|(i, x)| {
        *x = data[i] + (data[i + half_len] - data[i]) * point;
    });

    res
}

pub fn extract_witness_and_instance_assignments<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
) -> (Vec<F>, Vec<F>) {
    let extracted = match cs {
        ConstraintSystemRef::CS(cs) => {
            let cs = cs.deref().take();
            (cs.witness_assignment, cs.instance_assignment)
        }
        _ => panic!(""),
    };
    extracted
}

// from https://github.com/privacy-scaling-explorations/sonobe/blob/main/folding-schemes/src/utils/vec.rs#L51
pub fn get_default_poseidon_sponge_config<F: PrimeField>() -> PoseidonConfig<F> {
    let full_rounds = 8;
    let partial_rounds = 60;
    let alpha = 5;
    let rate = 4;

    let (ark, mds) = ark_crypto_primitives::sponge::poseidon::find_poseidon_ark_and_mds::<F>(
        F::MODULUS_BIT_SIZE as u64,
        rate,
        full_rounds,
        partial_rounds,
        0,
    );

    PoseidonConfig::new(
        full_rounds as usize,
        partial_rounds as usize,
        alpha,
        mds,
        ark,
        rate,
        1,
    )
}
