use clap::{Parser, Subcommand, Args};
use tau_core::{Envelope, MotiveCapsule, NonZeroRational};
use std::fs;
use std::path::PathBuf;
use sha2::{Digest, Sha256};
use serde::{Serialize, Deserialize};

#[derive(Parser)]
#[command(name="tau", version, about="τ‑Crystal CLI (bootstrap)")]
struct Cli { #[command(subcommand)] cmd: Cmd }

#[derive(Subcommand)]
enum Cmd {
    #[command(name="motive")] Motive { #[command(subcommand)] sub: MotiveSub },
    #[command(name="ledger")] Ledger { #[command(subcommand)] sub: LedgerSub },
}

#[derive(Subcommand)]
enum MotiveSub {
    #[command(name="init", about="emit a minimal MOTIVE receipt")]
    Init { #[arg(long)] mu0: String, #[arg(long)] b: String },
}

#[derive(Subcommand)]
enum LedgerSub {
    #[command(name="seal", about="Merkle-seal a list of capsule JSON files")]
    Seal(SealArgs),
}

#[derive(Args, Debug, Clone)]
struct SealArgs { #[arg(required=true)] capsules: Vec<PathBuf> }

#[derive(Serialize, Deserialize, Debug, Clone)]
struct Leaf { name: String, sha256_hex: String }
#[derive(Serialize, Deserialize, Debug, Clone)]
struct Master { schema_version: &'static str, kind: &'static str, leaves: Vec<Leaf>, master_hash: String }

fn main() {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Motive { sub } => match sub { MotiveSub::Init { mu0, b } => motive_init(&mu0, &b) },
        Cmd::Ledger { sub } => match sub { LedgerSub::Seal(args) => ledger_seal(args) },
    }
}

fn motive_init(mu0: &str, b: &str) {
    let mu0 = NonZeroRational::parse(mu0).unwrap_or_else(|e| panic!("mu0: {}", e));
    let b = NonZeroRational::parse(b).unwrap_or_else(|e| panic!("b: {}", e));
    let payload = MotiveCapsule { mu0, b };
    let env = Envelope::seal(payload);
    let json = tau_core::jcs::to_string(&env);
    print!("{}", json);
    eprintln!("{}", env.hash_hex);
}

