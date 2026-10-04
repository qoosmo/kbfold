//! The prover's randomness: seeds for the Merkle salts and the round salts, drawn from the
//! operating system.

use kbfold::error::Error;
use kbfold::merkle::Digest;

/// A fresh 32-byte seed from the operating system's secure random number generator.
pub(crate) fn fresh_seed() -> Result<Digest, Error> {
    let mut s = [0u8; 32];
    getrandom::fill(&mut s).map_err(|_| Error::Randomness)?;
    Ok(s)
}

/// `len` bytes of the stream keyed by `seed` on `label` (keyed BLAKE3 XOF).
pub(crate) fn derive(seed: &Digest, label: &[u8], index: u64, len: usize) -> Vec<u8> {
    let mut h = blake3::Hasher::new_keyed(seed);
    h.update(b"sumfri/v0.1/derive");
    h.update(&(label.len() as u64).to_le_bytes());
    h.update(label);
    h.update(&index.to_le_bytes());
    let mut out = vec![0u8; len];
    h.finalize_xof().fill(&mut out);
    out
}
