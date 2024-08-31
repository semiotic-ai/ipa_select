use ark_dh_commitments::{pedersen::PedersenCommitment, DoublyHomomorphicCommitment};
use ark_ed_on_bls12_381_bandersnatch::{EdwardsProjective, Fr};
use ark_inner_products::{InnerProduct, ScalarInnerProduct};
use ark_ip_proofs::gipa::GIPA;
use ark_std::{One, Zero, UniformRand, ops::Mul};
use ark_ff::Field;
use blake2::Blake2b;
use std::time::Instant;

type ScalarIPA = GIPA<
    ScalarInnerProduct<Fr>,
    PedersenCommitment<EdwardsProjective>,
    PedersenCommitment<EdwardsProjective>,
    PedersenCommitment<EdwardsProjective>,
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
    let (g_key, h_key, out_key) = ScalarIPA::setup(&mut rng, n).unwrap();

    // Commit to vectors and output
    let start_time = Instant::now();
    let x_commit = PedersenCommitment::<EdwardsProjective>::commit(&g_key, &x_vec).unwrap();
    let y_commit = PedersenCommitment::<EdwardsProjective>::commit(&g_key, &y_vec).unwrap();
    let commit_time = start_time.elapsed();
    let commit_time_ms = commit_time.as_millis();
    println!("Done committing, took {}ms", commit_time_ms);

    // Commit to ones_vec
    let ones_vec = vec![Fr::one(); n];
    let ones_commit: EdwardsProjective = g_key.iter().sum();
    let ones_h_commit: EdwardsProjective = h_key.iter().sum();

    assert!(PedersenCommitment::<EdwardsProjective>::verify(&g_key, &ones_vec, &ones_commit).unwrap());


    // Calculate d_vec and d_hat_vec
    let d_vec: Vec<Fr> = x_vec.iter().map(|x| *x - delta).collect();
    
    // Compute commitment to d_vec
    let d_commit = x_commit - ones_commit.mul(delta); 

    // Check d_commit
    assert!(PedersenCommitment::<EdwardsProjective>::verify(&g_key, &d_vec, &d_commit).unwrap());

    let d_hat_vec: Vec<Fr> = d_vec.iter().map(|d| {
        if *d == Fr::zero() {
            Fr::zero()
        } else {
            d.inverse().unwrap()
        }}).collect();

    // Commit to d_hat_vec and w_vec
    let d_hat_commit = PedersenCommitment::<EdwardsProjective>::commit(&h_key, &d_hat_vec).unwrap();
    
    // Find indices, w_vec, where x_vec = delta
    let w_vec: Vec<Fr> = x_vec.iter().map(|x| Fr::from(*x == delta)).collect();
    
    // Calculate s_vec
    let s_vec: Vec<Fr> = w_vec.iter().zip(&y_vec).map(|(w, y)| *w * *y).collect();

    // Commit to s_vec and w_vec
    let s_commit = PedersenCommitment::<EdwardsProjective>::commit(&g_key, &s_vec).unwrap();
    let w_commit = PedersenCommitment::<EdwardsProjective>::commit(&h_key, &w_vec).unwrap();


    // Draw random challenges r and z
    let transcript = &mut merlin::Transcript::new(b"ipa_select");
    // TODO: Add commitments to transcript
    let mut r_bytes: Vec<u8> = vec![0u8; 32];
    transcript.challenge_bytes(b"r", &mut r_bytes);
    let mut z_bytes: Vec<u8> = vec![0u8; 32]; 
    transcript.challenge_bytes(b"z",  &mut z_bytes);
    
    let z = Fr::from_random_bytes(&z_bytes).unwrap();
    let mut r = Fr::from_random_bytes(&r_bytes).unwrap();
    let mut r_vec = Vec::new();

    for _ in 0..n {
        r_vec.push(r);
        r = r * r;
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
    let c_1 = ScalarInnerProduct::<Fr>::inner_product(&l_1, &r_1).unwrap();
    let c_1_commit = PedersenCommitment::<EdwardsProjective>::commit(&[out_key], &[c_1]).unwrap();

    // VERIFIER: Compute commitment to l_1 and r_1
    let l_1_commit = d_commit + y_commit.mul(z) + ones_commit.mul(-z*z);
    let r_1_commit = w_commit;

    // Calculate h_prime_key explicitly for now. 
    // TODO: Incorporate h_prime_key calculation into the IPA 
    let h_prime_key: Vec<EdwardsProjective> = h_key.iter().zip(&r_vec).map(|(h, r)| h.mul(r.inverse().unwrap())).collect(); 

    // Verify commitments
    assert!(PedersenCommitment::<EdwardsProjective>::verify(&g_key, &l_1, &l_1_commit).unwrap());
    assert!(PedersenCommitment::<EdwardsProjective>::verify(&h_prime_key, &r_1, &r_1_commit).unwrap());
    assert!(PedersenCommitment::<EdwardsProjective>::verify(&[out_key], &[c_1], &c_1_commit).unwrap());

    // Compute IPA proof
    let vecs = (l_1.as_slice(), r_1.as_slice(), &c_1);
    let keys = (g_key.as_slice(), h_prime_key.as_slice(), &out_key);
    let commitments = (&l_1_commit, &r_1_commit, &c_1_commit);
    let ipa_proof = ScalarIPA::prove(vecs, keys, commitments).unwrap();
    let prove_time = start_time.elapsed();
    let prove_time_ms = prove_time.as_millis() - commit_time_ms;
    println!("Done proving, took {}ms", prove_time_ms);

    // Verify proof
    assert!(ScalarIPA::verify(keys, commitments, &ipa_proof).unwrap());
    let verify_time = start_time.elapsed();
    let verify_time_ms = verify_time.as_millis() - prove_time_ms;
    println!("Proof verified successfully!");
    println!("Took {}ms", verify_time_ms);


    // Second IPA
    // PROVER: Calculate l_2, r_2, and c_2
    let l_2: Vec<Fr> = s_vec.iter().map(|s| z*z - z*s).collect();
    let r_2 = r_vec.clone();
    let c_2 = ScalarInnerProduct::<Fr>::inner_product(&l_2, &r_2).unwrap();
    let c_2_commit = PedersenCommitment::<EdwardsProjective>::commit(&[out_key], &[c_2]).unwrap();

    // VERIFIER: Compute commitment to l_2 and r_2
    let l_2_commit = ones_commit.mul(z*z) - s_commit.mul(z);
    let r_2_commit = ones_h_commit;
    
    // Verify commitments
    assert!(PedersenCommitment::<EdwardsProjective>::verify(&g_key, &l_2, &l_2_commit).unwrap());
    assert!(PedersenCommitment::<EdwardsProjective>::verify(&h_prime_key, &r_2, &r_2_commit).unwrap());
    assert!(PedersenCommitment::<EdwardsProjective>::verify(&[out_key], &[c_2], &c_2_commit).unwrap());

    // Compute IPA proof
    let vecs = (l_2.as_slice(), r_2.as_slice(), &c_2);
    let keys = (g_key.as_slice(), h_prime_key.as_slice(), &out_key);
    let commitments = (&l_2_commit, &r_2_commit, &c_2_commit);
    let ipa_proof = ScalarIPA::prove(vecs, keys, commitments).unwrap();
    let prove_time = start_time.elapsed();
    let prove_time_ms = prove_time.as_millis() - commit_time_ms;
    println!("Done proving, took {}ms", prove_time_ms);

    // Verify proof
    assert!(ScalarIPA::verify(keys, commitments, &ipa_proof).unwrap());
    let verify_time = start_time.elapsed();
    let verify_time_ms = verify_time.as_millis() - prove_time_ms;
    println!("Proof verified successfully!");
    println!("Took {}ms", verify_time_ms);

    // Third IPA
    let l_3: Vec<Fr> = d_vec; 
    let r_3: Vec<Fr> = r_vec.iter().zip(d_hat_vec).map(|(r, d_hat)| *r * d_hat).collect();
    let c_3 = ScalarInnerProduct::<Fr>::inner_product(&l_3, &r_3).unwrap();
    let c_3_commit = PedersenCommitment::<EdwardsProjective>::commit(&[out_key], &[c_3]).unwrap();

    // VERIFIER: Compute commitment to l_3 and r_3
    let l_3_commit = d_commit; 
    let r_3_commit = d_hat_commit; 
    
    // Verify commitments
    assert!(PedersenCommitment::<EdwardsProjective>::verify(&g_key, &l_3, &l_3_commit).unwrap());
    assert!(PedersenCommitment::<EdwardsProjective>::verify(&h_prime_key, &r_3, &r_3_commit).unwrap());
    assert!(PedersenCommitment::<EdwardsProjective>::verify(&[out_key], &[c_3], &c_3_commit).unwrap());

    // Compute IPA proof
    let vecs = (l_3.as_slice(), r_3.as_slice(), &c_3);
    let keys = (g_key.as_slice(), h_prime_key.as_slice(), &out_key);
    let commitments = (&l_3_commit, &r_3_commit, &c_3_commit);
    let ipa_proof = ScalarIPA::prove(vecs, keys, commitments).unwrap();
    let prove_time = start_time.elapsed();
    let prove_time_ms = prove_time.as_millis() - commit_time_ms;
    println!("Done proving, took {}ms", prove_time_ms);

    // Verify proof
    assert!(ScalarIPA::verify(keys, commitments, &ipa_proof).unwrap());
    let verify_time = start_time.elapsed();
    let verify_time_ms = verify_time.as_millis() - prove_time_ms;
    println!("Proof verified successfully!");
    println!("Took {}ms", verify_time_ms);


    // Final Check
    // Verifier checks that c_1 + c_2 - z*z*c_3 = 0
    let c_final = c_1 + c_2 - z*z * c_3;
    assert!(c_final == Fr::zero());
    println!("Final check passed!");

    
}
