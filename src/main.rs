use std::io::Write;
use std::fs::File;
use std::path::Path;
use anyhow::Result;
use log::{Level, LevelFilter};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig};
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::util::timing::TimingTree;
use plonky2_sha256::circuit::{array_to_bits, make_circuits};
use sha2::{Digest, Sha256};
use plonky2_circom_verifier::verifier::{generate_verifier_config, generate_circom_verifier, generate_proof_base64};

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
    let mut config = CircuitConfig::standard_recursion_config();
    config.fri_config.rate_bits = 3;
    println!("{:?}", config);

    let mut builder = CircuitBuilder::<F, D>::new(config);
    let mut pw = PartialWitness::new();
    let expected_res = array_to_bits(hash.as_slice());
    let mut targets = vec![];

    for _ in 0..1 {
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
    let proof = data.prove(pw).unwrap();
    timing.print();
    println!("proof size {}", proof.to_bytes().len());

    let conf = generate_verifier_config(&proof)?;
    let (circom_constants, circom_gates) = generate_circom_verifier(&conf, &data.common, &data.verifier_only)?;

    let mut circom_file = File::create("./circom/circuits/constants.circom")?;
    circom_file.write_all(circom_constants.as_bytes())?;
    circom_file = File::create("./circom/circuits/gates.circom")?;
    circom_file.write_all(circom_gates.as_bytes())?;

    let proof_json = generate_proof_base64(&proof, &conf)?;

    if !Path::new("./circom/test/data").is_dir() {
        std::fs::create_dir("./circom/test/data")?;
    }

    let mut proof_file = File::create("./circom/test/data/proof.json")?;
    proof_file.write_all(proof_json.as_bytes())?;

    let mut conf_file = File::create("./circom/test/data/conf.json")?;
    conf_file.write_all(serde_json::to_string(&conf)?.as_ref())?;

    let timing = TimingTree::new("verify", Level::Debug);
    let res = data.verify(proof);
    timing.print();

    res
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
