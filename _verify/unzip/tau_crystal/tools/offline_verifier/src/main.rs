use sha2::{Digest, Sha256};
use serde::Deserialize;
use std::{fs, io, path::Path};
use thiserror::Error;

#[derive(Error, Debug)]
enum VerifyError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("Hash mismatch: expected {expected}, got {got}")]
    HashMismatch { expected: String, got: String },
    #[error("CHAIN too short")]
    ChainTooShort,
    #[error("Receipt file missing")]
    ReceiptMissing,
}

type Result<T> = std::result::Result<T, VerifyError>;

#[derive(Deserialize)]
struct Receipt {
    merkle_root: String,
    prev: Option<String>,
}

fn hash_file(path: impl AsRef<Path>) -> Result<String> {
    let mut hasher = Sha256::new();
    let bytes = fs::read(path)?;
    hasher.update(&bytes);
    Ok(hex::encode(hasher.finalize()))
}

fn hash_string(s: &str) -> String {
    hex::encode(Sha256::digest(s.as_bytes()))
}

fn merkle_from_git_index(root: impl AsRef<Path>) -> Result<String> {
    let mut hashes = Vec::new();
    let out = std::process::Command::new("git")
        .current_dir(&root)
        .args(["ls-files", "-z"])
        .output()?;
    if !out.status.success() {
        return Err(io::Error::new(io::ErrorKind::Other, "git ls-files failed").into());
    }
    let stdout = out.stdout;
    for path in stdout.split(|&b| b == 0).filter(|s| !s.is_empty()) {
        let path_str = std::str::from_utf8(path).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        let full = root.as_ref().join(path_str);
        hashes.push(hash_file(full)?);
    }
    if hashes.is_empty() {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "no tracked files").into());
    }
    hashes.sort();
    while hashes.len() > 1 {
        let mut next = Vec::with_capacity((hashes.len() + 1) / 2);
        let mut iter = hashes.into_iter();
        while let Some(a) = iter.next() {
            let b = iter.next().unwrap_or_else(|| a.clone());
            next.push(hash_string(&format!("{}{}", a, b)));
        }
        hashes = next;
    }
    Ok(hashes.pop().unwrap())
}

fn verify_chain(root: impl AsRef<Path>) -> Result<()> {
    let chain_path = root.as_ref().join(".tau_ledger/CHAIN");
    let chain = fs::read_to_string(chain_path)?;
    let mut lines = chain.lines().collect::<Vec<_>>();
    if lines.len() < 2 {
        return Err(VerifyError::ChainTooShort);
    }
    let last = lines.pop().unwrap();
    let prev_line = lines.pop().unwrap();
    let (last_hash, receipt_path) = last.split_once('\t').ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "malformed CHAIN line"))?;
    let receipt_full = root.as_ref().join(receipt_path.trim());
    if !receipt_full.exists() {
        return Err(VerifyError::ReceiptMissing);
    }
    let receipt_json = fs::read_to_string(&receipt_full)?;
    let receipt: Receipt = serde_json::from_str(&receipt_json)?;
    let computed_hash = hash_string(&fs::read_to_string(&receipt_full)?);
    if computed_hash != last_hash {
        return Err(VerifyError::HashMismatch { expected: last_hash.into(), got: computed_hash });
    }
    let computed_root = merkle_from_git_index(&root)?;
    if computed_root != receipt.merkle_root {
        return Err(VerifyError::HashMismatch { expected: receipt.merkle_root.clone(), got: computed_root });
    }
    if let Some(prev) = receipt.prev {
        let (prev_hash, _) = prev_line.split_once('\t').ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "malformed prev CHAIN line"))?;
        if prev != prev_hash {
            return Err(VerifyError::HashMismatch { expected: prev, got: prev_hash.into() });
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let root = std::env::args().nth(1).unwrap_or_else(|| ".".into());
    verify_chain(&root)?;
    println!("[tau_verify] OK");
    Ok(())
}
