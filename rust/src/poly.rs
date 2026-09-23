//! Boolean-kernel transforms (Corollary 3.8), multilinear helpers and the radix-2 NTT.

use crate::field::{Field, Fp};

/// Kernel coordinates -> monomial coefficients:  u = C^{(x)m} lambda,  C = [[0,1],[1,1]].
/// Each tensor factor maps (v0, v1) -> (v1, v0 + v1).  Cost: (m/2) N additions.
pub fn kernel_to_mono<F: Field>(v: &mut [F]) {
    let n = v.len();
    assert!(n.is_power_of_two());
    let mut half = 1;
    while half < n {
        for block in v.chunks_exact_mut(2 * half) {
            let (lo, hi) = block.split_at_mut(half);
            for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
                let v0 = *a;
                let v1 = *b;
                *a = v1;
                *b = v0 + v1;
            }
        }
        half *= 2;
    }
}

/// Monomial coefficients -> kernel coordinates:  (C^{-1})^{(x)m},  (v0, v1) -> (v1 - v0, v0).
pub fn mono_to_kernel<F: Field>(v: &mut [F]) {
    let n = v.len();
    assert!(n.is_power_of_two());
    let mut half = 1;
    while half < n {
        for block in v.chunks_exact_mut(2 * half) {
            let (lo, hi) = block.split_at_mut(half);
            for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
                let v0 = *a;
                let v1 = *b;
                *a = v1 - v0;
                *b = v0;
            }
        }
        half *= 2;
    }
}

/// Table -> monomial coefficients of its multilinear extension (Moebius inversion, Lemma 2.3):
/// c_a = sum_{b <= a} (-1)^{wt(a)-wt(b)} f(b).  Cost: (m/2) N subtractions.
pub fn mobius<F: Field>(v: &mut [F]) {
    let n = v.len();
    assert!(n.is_power_of_two());
    let mut half = 1;
    while half < n {
        for block in v.chunks_exact_mut(2 * half) {
            let (lo, hi) = block.split_at_mut(half);
            for (a, b) in lo.iter().zip(hi.iter_mut()) {
                *b = *b - *a;
            }
        }
        half *= 2;
    }
}

/// Restriction of the first (least significant) variable: t -> (1-T) t[2b] + T t[2b+1]  (Lemma 2.4).
pub fn restrict<F: Field>(t: &[F], r: F) -> Vec<F> {
    t.chunks_exact(2).map(|p| p[0] + r * (p[1] - p[0])).collect()
}

/// Multilinear extension of a table at a point (little-endian variable order).
pub fn mle_eval<F: Field>(t: &[F], z: &[F]) -> F {
    assert_eq!(t.len(), 1 << z.len());
    let mut cur = t.to_vec();
    for &zi in z {
        cur = restrict(&cur, zi);
    }
    cur[0]
}

/// eq(b, z) for all b in [2^m], little-endian.
pub fn eq_table<F: Field>(z: &[F]) -> Vec<F> {
    let mut t = vec![F::ONE];
    for &zi in z.iter().rev() {
        // new variable becomes the least significant bit
        let mut nt = Vec::with_capacity(2 * t.len());
        for &x in &t {
            nt.push(x * (F::ONE - zi));
            nt.push(x * zi);
        }
        t = nt;
    }
    t
}

/// Horner evaluation of a coefficient vector.
pub fn horner<F: Field>(c: &[F], x: F) -> F {
    c.iter().rev().fold(F::ZERO, |acc, &a| acc * x + a)
}

fn bit_reverse<T>(v: &mut [T]) {
    let n = v.len();
    let bits = n.trailing_zeros();
    if bits == 0 {
        return;
    }
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - bits);
        if i < j {
            v.swap(i, j);
        }
    }
}

/// In-place NTT: coefficients -> evaluations at omega^i (natural order), omega of order n.
pub fn ntt(v: &mut [Fp], omega: Fp) {
    let n = v.len();
    assert!(n.is_power_of_two());
    bit_reverse(v);
    let mut len = 2;
    while len <= n {
        let w_len = omega.pow((n / len) as u64);
        let half = len / 2;
        // twiddles for this stage
        let mut tw = Vec::with_capacity(half);
        let mut w = Fp::ONE;
        for _ in 0..half {
            tw.push(w);
            w = w * w_len;
        }
        for block in v.chunks_exact_mut(len) {
            let (lo, hi) = block.split_at_mut(half);
            for k in 0..half {
                let u = lo[k];
                let t = hi[k] * tw[k];
                lo[k] = u + t;
                hi[k] = u - t;
            }
        }
        len *= 2;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::Fp2;

    fn rnd(state: &mut u64) -> Fp {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        Fp::new(*state)
    }

    #[test]
    fn transforms_are_inverse_and_match_kernel_expansion() {
        let mut s = 42u64;
        for m in 0..8 {
            let n = 1 << m;
            let lam: Vec<Fp> = (0..n).map(|_| rnd(&mut s)).collect();
            let mut u = lam.clone();
            kernel_to_mono(&mut u);
            // explicit: coefficient a of K_b is 1 iff ~b subset a
            for a in 0..n {
                let mut acc = Fp::ZERO;
                for b in 0..n {
                    if (!b & (n - 1)) & !a == 0 {
                        acc = acc + lam[b];
                    }
                }
                assert_eq!(u[a], acc);
            }
            let mut back = u.clone();
            mono_to_kernel(&mut back);
            assert_eq!(back, lam);
        }
    }

    #[test]
    fn ntt_matches_horner() {
        let mut s = 7u64;
        for k in 1..10 {
            let n = 1 << k;
            let omega = Fp::two_adic_root(k);
            let c: Vec<Fp> = (0..n).map(|_| rnd(&mut s)).collect();
            let mut e = c.clone();
            ntt(&mut e, omega);
            for i in 0..n {
                assert_eq!(e[i], horner(&c, omega.pow(i as u64)));
            }
        }
    }

    #[test]
    fn eq_table_matches_mle() {
        let mut s = 9u64;
        let z: Vec<Fp2> = (0..5).map(|_| Fp2(rnd(&mut s), rnd(&mut s))).collect();
        let t: Vec<Fp2> = (0..32).map(|_| Fp2(rnd(&mut s), rnd(&mut s))).collect();
        let e = eq_table(&z);
        let direct = t.iter().zip(&e).fold(Fp2::ZERO, |acc, (&a, &b)| acc + a * b);
        assert_eq!(direct, mle_eval(&t, &z));
    }
}

#[cfg(test)]
mod mobius_tests {
    use super::*;
    use crate::field::Fp;
    #[test]
    fn mobius_gives_mle_coefficients() {
        let t: Vec<Fp> = (0..16u64).map(|i| Fp::new(i * i + 3)).collect();
        let mut c = t.clone();
        mobius(&mut c);
        // f(b) = sum_{a <= b} c_a
        for b in 0..16usize {
            let s = (0..16usize).filter(|a| a & !b == 0).fold(Fp::ZERO, |acc, a| acc + c[a]);
            assert_eq!(s, t[b]);
        }
    }
}
