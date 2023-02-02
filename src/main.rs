use std::io::Write;
use std::fs::File;
use std::path::Path;
use anyhow::Result;
use log::{Level, LevelFilter};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig, AlgebraicHasher, Hasher};
use plonky2::plonk::proof::ProofWithPublicInputs;
use plonky2::util::timing::TimingTree;
use plonky2_sha256::circuit::{array_to_bits, make_circuits};
use sha2::{Digest, Sha256};
use plonky2::plonk::circuit_data::{
    CircuitConfig, CommonCircuitData, VerifierCircuitTarget, VerifierOnlyCircuitData,
};
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::prover::prove;
use plonky2_field::extension::Extendable;

use plonky2_circom_verifier::verifier::{generate_verifier_config, generate_circom_verifier, generate_proof_base64};

type ProofTuple<F, C, const D: usize> = (
    ProofWithPublicInputs<F, C, D>,
    VerifierOnlyCircuitData<C, D>,
    CommonCircuitData<F, D>,
);

pub fn prove_sha256(msg: &[u8]) -> Result<()> {
    let mut hasher = Sha256::new();
    hasher.update(msg);
    let hash = hasher.finalize();
    // println!("Hash: {:#04X}", hash);

    let msg_bits = array_to_bits(msg);
    let len = msg.len() * 8;
    println!("block count: {}", (len + 65 + 511) / 512);
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    let config = CircuitConfig::standard_recursion_config();
    // config.fri_config.rate_bits = 3;
    println!("{:?}", config);

    let mut builder = CircuitBuilder::<F, D>::new(config);
    let mut pw = PartialWitness::new();
    let expected_res = array_to_bits(hash.as_slice());
    let mut targets = vec![];


    for _ in 0..2 {
        let curr = targets.len();
        targets.push(make_circuits(&mut builder, len as u64));

        for i in 0..len {
            pw.set_bool_target(targets[curr].message[i], msg_bits[i]);
        }

        for i in 0..expected_res.len() {
            if expected_res[i] {
                builder.assert_one(targets[curr].digest[i].target);
            } else {
                builder.assert_zero(targets[curr].digest[i].target);
            }
        }
    }

    println!(
        "Constructing inner proof with {} gates",
        builder.num_gates()
    );
    let data = builder.build::<C>();
    let timing = TimingTree::new("prove", Level::Debug);
    let sha256proof = data.prove(pw).unwrap();
    timing.print();
    println!("proof steps length {}", sha256proof.proof.opening_proof.query_round_proofs[0].steps.len());

    let config = CircuitConfig::standard_recursion_config();
    let proof = recursive_proof::<F, C, C, D>(&(sha256proof, data.verifier_only, data.common), None, &config, None)?;

    println!("middle proof steps {:?}", proof.0.proof.opening_proof.query_round_proofs[0].steps.len());

    let conf = generate_verifier_config(&proof.0)?;
    let (circom_constants, circom_gates) = generate_circom_verifier(&conf, &proof.2, &proof.1)?;

    let mut circom_file = File::create("./circom/circuits/constants.circom")?;
    circom_file.write_all(circom_constants.as_bytes())?;
    circom_file = File::create("./circom/circuits/gates.circom")?;
    circom_file.write_all(circom_gates.as_bytes())?;

    let proof_json = generate_proof_base64(&proof.0, &conf)?;

    if !Path::new("./circom/test/data").is_dir() {
        std::fs::create_dir("./circom/test/data")?;
    }

    let mut proof_file = File::create("./circom/test/data/proof.json")?;
    proof_file.write_all(proof_json.as_bytes())?;

    let mut conf_file = File::create("./circom/test/data/conf.json")?;
    conf_file.write_all(serde_json::to_string(&conf)?.as_ref())?;

    // let timing = TimingTree::new("verify", Level::Debug);
    // let res = data.verify(proof);
    // timing.print();

    // res
    Ok(())
}

fn main() -> Result<()> {
    // Initialize logging
    let mut builder = env_logger::Builder::from_default_env();
    builder.format_timestamp(None);
    builder.filter_level(LevelFilter::Debug);
    builder.try_init()?;

    const MSG_SIZE: usize = 512;
    let mut msg = vec![0; MSG_SIZE as usize];
    for i in 0..MSG_SIZE - 1 {
        msg[i] = i as u8;
    }
    prove_sha256(&msg)
}

fn recursive_proof<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F>,
    const D: usize,
>(
    inner1: &ProofTuple<F, InnerC, D>,
    inner2: Option<ProofTuple<F, InnerC, D>>,
    config: &CircuitConfig,
    min_degree_bits: Option<usize>,
) -> Result<ProofTuple<F, C, D>>
where
    InnerC::Hasher: AlgebraicHasher<F>,
    // [(); C::Hasher::HASH_SIZE]:,
{
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let mut pw = PartialWitness::new();

    {
        let (inner_proof, inner_vd, inner_cd) = inner1;
        let pt = builder.add_virtual_proof_with_pis::<InnerC>(inner_cd);
        pw.set_proof_with_pis_target(&pt, inner_proof);
        builder.register_public_inputs(&*pt.public_inputs);

        let inner_data = VerifierCircuitTarget {
            constants_sigmas_cap: builder.add_virtual_cap(inner_cd.config.fri_config.cap_height),
            circuit_digest: builder.add_virtual_hash(),
        };
        pw.set_cap_target(
            &inner_data.constants_sigmas_cap,
            &inner_vd.constants_sigmas_cap,
        );
        pw.set_hash_target(inner_data.circuit_digest, inner_vd.circuit_digest);

        builder.verify_proof::<InnerC>(&pt, &inner_data, inner_cd);
    }

    if inner2.is_some() {
        let (inner_proof, inner_vd, inner_cd) = inner2.unwrap();
        let pt = builder.add_virtual_proof_with_pis::<InnerC>(&inner_cd);
        pw.set_proof_with_pis_target(&pt, &inner_proof);
        builder.register_public_inputs(&*pt.public_inputs);

        let inner_data = VerifierCircuitTarget {
            constants_sigmas_cap: builder.add_virtual_cap(inner_cd.config.fri_config.cap_height),
            circuit_digest: builder.add_virtual_hash(),
        };
        pw.set_hash_target(inner_data.circuit_digest, inner_vd.circuit_digest);
        pw.set_cap_target(
            &inner_data.constants_sigmas_cap,
            &inner_vd.constants_sigmas_cap,
        );

        builder.verify_proof::<InnerC>(&pt, &inner_data, &inner_cd);
    }
    builder.print_gate_counts(0);

    if let Some(min_degree_bits) = min_degree_bits {
        // We don't want to pad all the way up to 2^min_degree_bits, as the builder will
        // add a few special gates afterward. So just pad to 2^(min_degree_bits
        // - 1) + 1. Then the builder will pad to the next power of two,
        // 2^min_degree_bits.
        let min_gates = (1 << (min_degree_bits - 1)) + 1;
        for _ in builder.num_gates()..min_gates {
            builder.add_gate(NoopGate, vec![]);
        }
    }

    let data = builder.build::<C>();

    let mut timing = TimingTree::new("prove", Level::Info);
    let proof = prove(&data.prover_only, &data.common, pw, &mut timing)?;
    timing.print();

    data.verify(proof.clone())?;

    // test_serialization(&proof, &data.verifier_only, &data.common)?;
    Ok((proof, data.verifier_only, data.common))
}
