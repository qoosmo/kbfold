//! Number-theoretic facts about Goldilocks used in the paper (Section 8 and Remark 7.x).
use kbfold::field::{Field, Fp, GENERATOR, P};

/// p - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537.
#[test]
fn factorisation_of_p_minus_one() {
    let f: u128 = (1u128 << 32) * 3 * 5 * 17 * 257 * 65537;
    assert_eq!(f, (P - 1) as u128);
}

/// 7 generates F_p^*: 7^((p-1)/l) != 1 for every prime l dividing p - 1.
#[test]
fn seven_is_a_generator() {
    let g = Fp::from_u64(GENERATOR);
    for l in [2u64, 3, 5, 17, 257, 65537] {
        assert_ne!(g.pow((P - 1) / l), Fp::ONE, "7^((p-1)/{l}) = 1");
    }
    // In particular 7 is a non-square, and p = 1 mod 4.
    assert_ne!(g.pow((P - 1) / 2), Fp::ONE);
    assert_eq!(P % 4, 1);
}
