//! Test vectors: transcript challenges and a complete seeded proof. Other implementations can
//! check themselves against `vectors/`. Regenerate with `KBFOLD_BLESS=1` (only after an intended
//! change of the proof format, together with `pcs::LABEL`).

use kbfold::field::{ExtField, Fp2, Fp4};
use kbfold::merkle::Transcript;

#[cfg(feature = "insecure-test-vectors")]
fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn digits<E: ExtField>(x: E) -> String {
    x.digits().iter().map(|d| d.0.to_string()).collect::<Vec<_>>().join(",")
}

fn check(name: &str, got: &str) {
    let path = format!("{}/vectors/{name}", env!("CARGO_MANIFEST_DIR"));
    if std::env::var("KBFOLD_BLESS").is_ok() {
        std::fs::write(&path, got).unwrap();
    }
    let want = std::fs::read_to_string(&path).expect("missing vector file");
    assert_eq!(got, want, "vector {name} changed");
}

#[test]
fn transcript_vectors() {
    let mut out = String::new();
    let mut tr = Transcript::new(b"kbfold/test-vectors");
    tr.absorb(b"data", b"abc");
    for i in 0..3 {
        let c: Fp2 = tr.challenge();
        out += &format!("fp2 {i}: {}\n", digits(c));
    }
    for i in 0..3 {
        let c: Fp4 = tr.challenge();
        out += &format!("fp4 {i}: {}\n", digits(c));
    }
    let idx = tr.query_indices(8, 13);
    out += &format!("indices: {idx:?}\n");
    check("transcript.txt", &out);
}

#[cfg(feature = "insecure-test-vectors")]
#[test]
fn proof_vectors() {
    use kbfold::field::Fp;
    use kbfold::insecure;
    use kbfold::pcs::{Params, verify};
    let mut out = String::new();
    for (m, s, e) in [(6usize, 3usize, 2usize), (6, 6, 4)] {
        let p = Params::new(m, 2, s, 8);
        let table: Vec<Fp> = (0..1u64 << m).map(|i| Fp::new(i * i + 1)).collect();
        let (root, pd) = insecure::commit(&p, &table, &[1u8; 32]).unwrap();
        out += &format!("m={m} R=2 s={s} queries=8 salt_len=32 e={e}\nroot: {}\n", hex(&root));
        let bytes = if e == 2 {
            let z: Vec<Fp2> = (0..m as u64).map(|i| Fp2(Fp::new(i + 2), Fp::new(3 * i))).collect();
            let (v, proof) = insecure::open(&p, &pd, &z, &[2u8; 32]).unwrap();
            assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()));
            assert_eq!(proof.to_bytes().len(), proof.size_bytes());
            out += &format!("value: {}\n", digits(v));
            proof.to_bytes()
        } else {
            let z: Vec<Fp4> = (0..m as u64)
                .map(|i| Fp4::from_digits(&[Fp::new(i + 2), Fp::new(3 * i), Fp::new(5), Fp::new(i)]))
                .collect();
            let (v, proof) = insecure::open(&p, &pd, &z, &[2u8; 32]).unwrap();
            assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()));
            assert_eq!(proof.to_bytes().len(), proof.size_bytes());
            out += &format!("value: {}\n", digits(v));
            proof.to_bytes()
        };
        out += &format!(
            "proof bytes: {}\nproof blake3: {}\nproof: {}\n\n",
            bytes.len(),
            hex(blake3::hash(&bytes).as_bytes()),
            hex(&bytes)
        );
    }
    check("proofs.txt", &out);
}
