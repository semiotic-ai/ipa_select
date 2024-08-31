use ark_dh_commitments::{pedersen::PedersenCommitment, DoublyHomomorphicCommitment};
use ark_ed_on_bls12_381_bandersnatch::{EdwardsProjective, Fr};
use ark_inner_products::{InnerProduct, ScalarInnerProduct};
use ark_ip_proofs::gipa::GIPA;
use ark_std::UniformRand;
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

    // Create random y_vec and t_vec
    let n = 8192usize;
    let mut rng = ark_std::test_rng();
    let y_vec: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
    let t = Fr::rand(&mut rng);
    let z_vec = (0..n).map(|z| (t - Fr::from(z as u64)).inverse().ok_or("bad inverse").unwrap()).collect::<Vec<Fr>>();
    
    // Calculate the inner inner product
    let out = ScalarInnerProduct::<Fr>::inner_product(&y_vec, &z_vec).unwrap();

    // Setup the IPA
    let (g_key, h_key, out_key) = ScalarIPA::setup(&mut rng, n).unwrap();

    // Commit to vectors and output
    let start_time = Instant::now();
    let a_commit = PedersenCommitment::<EdwardsProjective>::commit(&g_key, &y_vec).unwrap();
    let b_commit = PedersenCommitment::<EdwardsProjective>::commit(&h_key, &z_vec).unwrap();
    let out_commit = PedersenCommitment::<EdwardsProjective>::commit(&[out_key], &[out]).unwrap();
    let commit_time = start_time.elapsed();
    let commit_time_ms = commit_time.as_millis();
    println!("Done committing, took {}ms", commit_time_ms);

    // Compute IPA proof
    let vecs = (y_vec.as_slice(), z_vec.as_slice(), &out);
    let keys = (g_key.as_slice(), h_key.as_slice(), &out_key);
    let commitments = (&a_commit, &b_commit, &out_commit);
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
}
