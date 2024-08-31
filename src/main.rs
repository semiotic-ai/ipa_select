use ark_dh_commitments::{pedersen::PedersenCommitment, DoublyHomomorphicCommitment, identity::IdentityCommitment};
use ark_bls12_381::{Fr, Bls12_381};
use ark_inner_products::{InnerProduct, ScalarInnerProduct};
use ark_ip_proofs::tipa::TIPA;
use ark_std::{One, Zero, UniformRand, ops::Mul};
use ark_ff::Field;
use blake2::Blake2b;
use std::time::Instant;
use ark_ec::pairing::Pairing;
use rayon::prelude::*;

type CommitmentG1 = PedersenCommitment<<Bls12_381 as Pairing>::G1>;
type CommitmentG2 = PedersenCommitment<<Bls12_381 as Pairing>::G2>;
type IPC = IdentityCommitment<<Bls12_381 as Pairing>::ScalarField, <Bls12_381 as Pairing>::ScalarField>;
type ScalarIPA = TIPA<
    ScalarInnerProduct<<Bls12_381 as Pairing>::ScalarField>,
    CommitmentG2, 
    CommitmentG1, 
    IPC, 
    Bls12_381,
    Blake2b,
>;
fn main() {
    println!("Hello, world!");

    // Create "tables" x_vec and y_vec
    let n = 8192usize;
    let mut rng = ark_std::test_rng();
    let y_vec: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
    let mut x_vec: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();

    // Verifier chooses delta
    let delta = Fr::rand(&mut rng);
    // TESTING ONLY, insert delta in x_vec
    x_vec[0] = delta;
    x_vec[128] = delta;
    x_vec[256] = delta;
    x_vec[512] = delta;
    x_vec[1024] = delta;
    x_vec[2048] = delta;
    x_vec[4096] = delta;
    x_vec[8191] = delta;

    // Setup the commitment keys 
    let (srs, out_key) = ScalarIPA::setup(&mut rng, n).unwrap();
    let (h_key, g_key) = srs.get_commitment_keys();
    let cks = (h_key.as_slice(), g_key.as_slice(), &out_key.clone());
    let v_srs = srs.get_verifier_key();

    // Commit to vectors and output
    let start_time = Instant::now();
    let x_commit: <Bls12_381 as Pairing>::G1 = CommitmentG1::commit(&g_key, &x_vec).unwrap();
    let y_commit: <Bls12_381 as Pairing>::G1 = CommitmentG1::commit(&g_key, &y_vec).unwrap();

    // Commit to ones_vec
    let ones_vec = vec![Fr::one(); n];
    let ones_commit = g_key.iter().sum();
    let ones_h_commit = h_key.iter().sum();

    assert!(CommitmentG1::verify(&g_key, &ones_vec, &ones_commit).unwrap());
    assert!(CommitmentG2::verify(&h_key, &ones_vec, &ones_h_commit).unwrap());


    // Calculate d_vec and d_hat_vec
    let d_vec: Vec<Fr> = x_vec.iter().map(|x| *x - delta).collect();
    
    // Compute commitment to d_vec
    let d_commit = x_commit - ones_commit.mul(delta); 

    // Check d_commit
    assert!(CommitmentG1::verify(&g_key, &d_vec, &d_commit).unwrap());

    let d_hat_vec: Vec<Fr> = d_vec.iter().map(|d| {
        if *d == Fr::zero() {
            Fr::zero()
        } else {
            d.inverse().unwrap()
        }}).collect();

    // Commit to d_hat_vec and w_vec
    let d_hat_commit = CommitmentG2::commit(&h_key, &d_hat_vec).unwrap();
    
    // Find indices, w_vec, where x_vec = delta
    let w_vec: Vec<Fr> = x_vec.iter().map(|x| Fr::from(*x == delta)).collect();
    
    // Calculate s_vec
    let s_vec: Vec<Fr> = w_vec.iter().zip(&y_vec).map(|(w, y)| *w * *y).collect();

    // Commit to s_vec and w_vec
    let s_commit = CommitmentG1::commit(&g_key, &s_vec).unwrap();
    let w_commit = CommitmentG2::commit(&h_key, &w_vec).unwrap();

    let commit_time = start_time.elapsed();
    let commit_time_ms = commit_time.as_millis();
    println!("Done committing, took {}ms", commit_time_ms);

    // Draw random challenges r and z
    let transcript = &mut merlin::Transcript::new(b"ipa_select");
    // TODO: Add commitments to transcript
    let mut r_bytes: Vec<u8> = vec![0u8; 32];
    transcript.challenge_bytes(b"r", &mut r_bytes);
    let mut z_bytes: Vec<u8> = vec![0u8; 32]; 
    transcript.challenge_bytes(b"z",  &mut z_bytes);
    
    let z = Fr::from_random_bytes(&z_bytes).unwrap();
    let r = Fr::from_random_bytes(&r_bytes).unwrap();
    let r_inv = r.inverse().unwrap();
    let mut r_pow = Fr::one();
    let mut r_pow_inv = Fr::one();
    let mut r_vec = Vec::new();
    let mut r_vec_inv = Vec::new();
    for _ in 0..n {
        r_vec_inv.push(r_pow_inv);
        r_vec.push(r_pow);
        r_pow_inv *= r_inv;
        r_pow *= r;
    }

    // Check that the constraints hold
    let lhs: Vec<Fr> = d_vec.iter().zip(&w_vec).map(|(d, w)| *d * w).collect();
    let rhs = r_vec.clone();
    let out = ScalarInnerProduct::<Fr>::inner_product(&lhs, &rhs).unwrap();
    assert!(out == Fr::zero());

    let lhs: Vec<Fr> = d_vec.iter().zip(&d_hat_vec).zip(&w_vec).map(|((d, d_hat), w)| Fr::one() - w - *d * d_hat).collect();
    let rhs = r_vec.clone();
    let out = ScalarInnerProduct::<Fr>::inner_product(&lhs, &rhs).unwrap();
    assert!(out == Fr::zero());

    let lhs: Vec<Fr> = s_vec.iter().zip(&w_vec).zip(&y_vec).map(|((s, w), y)| y * w - *s).collect();
    let rhs = r_vec.clone();
    let out = ScalarInnerProduct::<Fr>::inner_product(&lhs, &rhs).unwrap();
    assert!(out == Fr::zero());

    // First IPA
    // PROVER: Calculate l_1, r_1, and c_1
    let l_1: Vec<Fr> = d_vec.iter().zip(y_vec).map(|(d, y)| *d + z * y - z*z).collect();
    let r_1: Vec<Fr> = r_vec.iter().zip(w_vec).map(|(r, w)| *r * w).collect();
    let c_1 = ScalarInnerProduct::<Fr>::inner_product(&r_1, &l_1).unwrap();
    let c_1_commit = IPC::commit(&[out_key.clone()], &[c_1]).unwrap();

    // VERIFIER: Compute commitment to l_1 and r_1
    let l_1_commit = d_commit + y_commit.mul(z) + ones_commit.mul(-z*z);
    let r_1_commit = w_commit;


    // Calculate rescaled h_key
    let h_key_rescale_time = start_time.elapsed().as_millis();
    let h_key_prime: Vec<<Bls12_381 as Pairing>::G2> = h_key.par_iter().zip(&r_vec_inv).map(|(h, r)| h.mul(r)).collect();
    let h_key_prime_time = start_time.elapsed().as_millis() - h_key_rescale_time;
    println!("Rescaled h_key, took {}ms", h_key_prime_time);

    // Verify commitments
    assert!(CommitmentG1::verify(&g_key, &l_1, &l_1_commit).unwrap());
    assert!(CommitmentG2::verify(&h_key_prime, &r_1, &r_1_commit).unwrap());
    assert!(IPC::verify(&[out_key.clone()], &[c_1], &c_1_commit).unwrap());

    let cks_shift = (h_key_prime.as_slice(), g_key.as_slice(), &out_key.clone());
    // Compute IPA proof
    let vecs = (r_1.as_slice(), l_1.as_slice());
    let commitments = (&r_1_commit, &l_1_commit, &c_1_commit);
    let proof_start_time = start_time.elapsed().as_millis();
    let ipa_proof = ScalarIPA::prove_with_srs_shift(&srs, vecs, cks_shift, &r).unwrap();
    let prove_time = start_time.elapsed();
    let prove_time_ms = prove_time.as_millis() - proof_start_time;
    println!("Done proving, took {}ms", prove_time_ms);

    // Verify proof
    let verify_start_time = start_time.elapsed().as_millis();
    assert!(ScalarIPA::verify_with_srs_shift(&v_srs, &out_key.clone(), commitments, &ipa_proof, &r).unwrap());
    let verify_time = start_time.elapsed();
    let verify_time_ms = verify_time.as_millis() - verify_start_time;
    println!("Proof verified successfully!");
    println!("Took {}ms", verify_time_ms);


    // Second IPA
    // PROVER: Calculate l_2, r_2, and c_2
    let l_2: Vec<Fr> = s_vec.iter().map(|s| z*z - z*s).collect();
    let r_2 = r_vec.clone();
    let c_2 = ScalarInnerProduct::<Fr>::inner_product(&l_2, &r_2).unwrap();
    let c_2_commit = IPC::commit(&[out_key.clone()], &[c_2]).unwrap();

    // VERIFIER: Compute commitment to l_2 and r_2
    let l_2_commit = ones_commit.mul(z*z) - s_commit.mul(z);
    let r_2_commit = ones_h_commit;
    
    // Verify commitments
    assert!(CommitmentG1::verify(&g_key, &l_2, &l_2_commit).unwrap());
    assert!(CommitmentG2::verify(&h_key_prime, &r_2, &r_2_commit).unwrap());
    assert!(IPC::verify(&[out_key.clone()], &[c_2], &c_2_commit).unwrap());

    // Compute IPA proof
    let vecs = (r_2.as_slice(), l_2.as_slice());
    let commitments = (&r_2_commit, &l_2_commit, &c_2_commit);
    let proof_start_time = start_time.elapsed().as_millis();
    let ipa_proof = ScalarIPA::prove_with_srs_shift(&srs, vecs, cks_shift, &r).unwrap();
    let prove_time = start_time.elapsed();
    let prove_time_ms = prove_time.as_millis() - proof_start_time;
    println!("Done proving, took {}ms", prove_time_ms);

    // Verify proof
    let verify_start_time = start_time.elapsed().as_millis();
    assert!(ScalarIPA::verify_with_srs_shift(&v_srs, &out_key.clone(), commitments, &ipa_proof, &r).unwrap());
    let verify_time = start_time.elapsed();
    let verify_time_ms = verify_time.as_millis() - verify_start_time;
    println!("Proof verified successfully!");
    println!("Took {}ms", verify_time_ms);

    // Third IPA
    let l_3: Vec<Fr> = d_vec; 
    let r_3: Vec<Fr> = r_vec.iter().zip(d_hat_vec).map(|(r, d_hat)| *r * d_hat).collect();
    let c_3 = ScalarInnerProduct::<Fr>::inner_product(&l_3, &r_3).unwrap();
    let c_3_commit = IPC::commit(&[out_key.clone()], &[c_3]).unwrap();

    // VERIFIER: Compute commitment to l_3 and r_3
    let l_3_commit = d_commit; 
    let r_3_commit = d_hat_commit; 
    
    // Verify commitments
    assert!(CommitmentG1::verify(&g_key, &l_3, &l_3_commit).unwrap());
    assert!(CommitmentG2::verify(&h_key_prime, &r_2, &r_2_commit).unwrap());
    assert!(IPC::verify(&[out_key.clone()], &[c_3], &c_3_commit).unwrap());

    // Compute IPA proof
    let vecs = (r_3.as_slice(), l_3.as_slice());
    let commitments = (&r_3_commit, &l_3_commit, &c_3_commit);
    let proof_start_time = start_time.elapsed().as_millis();
    let ipa_proof = ScalarIPA::prove_with_srs_shift(&srs, vecs, cks_shift, &r).unwrap();
    let prove_time = start_time.elapsed();
    let prove_time_ms = prove_time.as_millis() - proof_start_time;
    println!("Done proving, took {}ms", prove_time_ms);

    // Verify proof
    let verify_start_time = start_time.elapsed().as_millis();
    assert!(ScalarIPA::verify_with_srs_shift(&v_srs, &out_key.clone(), commitments, &ipa_proof, &r).unwrap());
    let verify_time = start_time.elapsed();
    let verify_time_ms = verify_time.as_millis() - verify_start_time;
    println!("Proof verified successfully!");
    println!("Took {}ms", verify_time_ms);


    // Final Check
    // Verifier checks that c_1 + c_2 - z*z*c_3 = 0
    let c_final = c_1 + c_2 - z*z * c_3;
    assert!(c_final == Fr::zero());
    println!("Final check passed!");

    
}
