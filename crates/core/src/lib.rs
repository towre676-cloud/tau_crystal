use serde::{Serialize, Deserialize};
use num_integer::Integer;
pub mod jcs;

pub type Hash256 = [u8; 32];
pub fn sha2_256(bytes: &[u8]) -> Hash256 {
    use sha2::{Digest, Sha256};
    let mut h = Sha256::new(); h.update(bytes);
    let out = h.finalize(); let mut a = [0u8; 32]; a.copy_from_slice(&out[..]); a
}

pub trait Canonicalize { fn canonical_bytes(&self) -> Vec<u8>; }
pub trait Receipt: Serialize + Canonicalize { const KIND: &'static str; fn hash(&self) -> Hash256 { sha2_256(&self.canonical_bytes()) } }

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Envelope<T: Receipt> { pub schema_version: &'static str, pub kind: &'static str, pub payload: T, pub hash_hex: String }
impl<T: Receipt> Envelope<T> { pub fn seal(payload: T) -> Self { let h = payload.hash(); Self { schema_version: "0.1.0", kind: T::KIND, payload, hash_hex: hex::encode(h) } } }
impl<T: Receipt> Canonicalize for Envelope<T> { fn canonical_bytes(&self) -> Vec<u8> { crate::jcs::to_vec(self) } }

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct NonZeroRational { pub num: i128, pub den: i128 }
impl NonZeroRational {
  pub fn parse(s: &str) -> Result<Self, String> {
    let parts: Vec<&str> = s.split('/').collect();
    let (n, d): (i128, i128) = match parts.as_slice() {
        [a]    => (a.parse::<i128>().map_err(|_| "bad num")?, 1i128),
        [a, b] => (a.parse::<i128>().map_err(|_| "bad num")?, b.parse::<i128>().map_err(|_| "bad den")?),
        _ => return Err("bad rational".into()),
    };
    if d == 0 || n == 0 { return Err("zero not allowed".into()); }
    let g = n.abs().gcd(&d.abs());
    let mut num = n / g; let mut den = d / g; if den < 0 { num = -num; den = -den; }
    Ok(Self { num, den })
  }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct MotiveCapsule { pub mu0: NonZeroRational, pub b: NonZeroRational }
impl Canonicalize for MotiveCapsule { fn canonical_bytes(&self) -> Vec<u8> { crate::jcs::to_vec(self) } }
impl Receipt for MotiveCapsule { const KIND: &'static str = "MOTIVE"; }
