//! Reproducible regression tests for Chapter 4 of the ZK-KBFold manuscript.
//! Standalone: `rustc --edition=2021 --test audit/kernel_algebra.rs -o /tmp/kbtest && /tmp/kbtest`
//! These tests support the proofs but are not substitutes for Lean 4 certification.

fn modulo(x: i64, p: i64) -> i64 { x.rem_euclid(p) }

fn mul(a: &[i64], b: &[i64], p: i64) -> Vec<i64> {
    let mut c = vec![0i64; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            c[i + j] = modulo(c[i + j] + x * y, p);
        }
    }
    c
}

fn kernel_polys(m: usize, p: i64) -> Vec<Vec<i64>> {
    let n = 1usize << m;
    let mut out = Vec::with_capacity(n);
    for b in 0..n {
        let mut poly = vec![1i64];
        for i in 0..m {
            let mut factor = vec![0i64; (1usize << i) + 1];
            factor[0] = ((b >> i) & 1) as i64;
            factor[1 << i] = 1;
            poly = mul(&poly, &factor, p);
        }
        out.push(poly);
    }
    out
}

fn encode(f: &[i64], kernels: &[Vec<i64>], p: i64) -> Vec<i64> {
    let mut a = vec![0i64; kernels[0].len()];
    for (fb, kb) in f.iter().zip(kernels) {
        for (i, &coeff) in kb.iter().enumerate() {
            a[i] = modulo(a[i] + fb * coeff, p);
        }
    }
    a
}

fn inverse_mobius(a: &[i64], m: usize, p: i64) -> Vec<i64> {
    let n = 1usize << m;
    let mut f = vec![0i64; n];
    for (b, fb) in f.iter_mut().enumerate() {
        let zeros: Vec<_> = (0..m).filter(|i| b & (1 << i) == 0).collect();
        let mut sum = 0i64;
        for mask in 0..(1usize << zeros.len()) {
            let mut e = 0usize;
            for (j, bit) in zeros.iter().enumerate() {
                if mask & (1 << j) != 0 { e |= 1 << bit; }
            }
            let exponent = zeros.len() - mask.count_ones() as usize;
            let sign = if exponent % 2 == 0 { 1 } else { -1 };
            sum += sign * a[e];
        }
        *fb = modulo(sum, p);
    }
    f
}

fn fold(a: &[i64], r: i64, p: i64) -> Vec<i64> {
    let mut result = vec![0i64; (a.len() + 1) / 2];
    for (j, out) in result.iter_mut().enumerate() {
        let even = a[2 * j];
        let odd = a.get(2 * j + 1).copied().unwrap_or(0);
        *out = modulo((2 * r - 1) * even + (1 - r) * odd, p);
    }
    result
}

fn mle(f: &[i64], theta: &[i64], p: i64) -> i64 {
    let mut value = 0i64;
    for (b, fb) in f.iter().enumerate() {
        let mut weight = 1i64;
        for (i, &r) in theta.iter().enumerate() {
            weight = modulo(weight * (if b & (1 << i) != 0 { r } else { 1 - r }), p);
        }
        value = modulo(value + fb * weight, p);
    }
    value
}

fn powmod(mut base: i64, mut exp: usize, p: i64) -> i64 {
    let mut out = 1i64;
    while exp > 0 {
        if exp & 1 != 0 { out = modulo(out * base, p); }
        base = modulo(base * base, p);
        exp >>= 1;
    }
    out
}

fn eval(coeffs: &[i64], x: i64, p: i64) -> i64 {
    coeffs.iter().rev().fold(0i64, |acc, &c| modulo(acc * x + c, p))
}

#[derive(Clone)]
struct Lcg { state: u64 }
impl Lcg {
    fn new(seed: u64) -> Self { Self { state: seed } }
    fn next(&mut self, p: i64) -> i64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((self.state >> 20) % p as u64) as i64
    }
}

#[test]
fn basis_transform_fold_and_tensor_formula() {
    let mut rng = Lcg::new(20261107);
    for p in [2i64, 3, 5, 17, 97] {
        for m in 1usize..=5 {
            let n = 1usize << m;
            let kernels = kernel_polys(m, p);
            for _ in 0..80 {
                let f: Vec<i64> = (0..n).map(|_| rng.next(p)).collect();
                let a = encode(&f, &kernels, p);
                assert_eq!(inverse_mobius(&a, m, p), f);
                assert_eq!(a[0], f[n - 1]);
                assert_eq!(a[n - 1], modulo(f.iter().sum(), p));
                let theta: Vec<i64> = (0..m).map(|_| rng.next(p)).collect();
                let mut folded = a.clone();
                for &r in &theta { folded = fold(&folded, r, p); }
                assert_eq!(folded.len(), 1);
                assert_eq!(folded[0], mle(&f, &theta, p));
                let mut tensor = 0i64;
                for (e, &ae) in a.iter().enumerate() {
                    let mut weight = 1i64;
                    for (i, &r) in theta.iter().enumerate() {
                        weight = modulo(weight * (if e & (1 << i) != 0 { 1 - r } else { 2 * r - 1 }), p);
                    }
                    tensor = modulo(tensor + ae * weight, p);
                }
                assert_eq!(tensor, folded[0]);
            }
        }
    }
}

#[test]
fn low_degree_pattern_and_scaled_curve() {
    let mut rng = Lcg::new(101010);
    for p in [2i64, 3, 5, 17, 97] {
        for m in 1usize..=5 {
            let n = 1usize << m;
            let kernels = kernel_polys(m, p);
            for _ in 0..60 {
                let t = rng.next((m + 1) as i64) as usize;
                let b = 1usize << t;
                let h = m - t;
                let phi: Vec<i64> = (0..b).map(|_| rng.next(p)).collect();
                let mut f = vec![0i64; n];
                for high in 0..(1usize << h) {
                    let sign = if (h - high.count_ones() as usize) % 2 == 0 { 1 } else { -1 };
                    for low in 0..b { f[low + (high << t)] = modulo(sign * phi[low], p); }
                }
                let u = encode(&f, &kernels, p);
                assert!(u[b..].iter().all(|&x| x == 0));
                assert_eq!(&u[..b], &encode(&phi, &kernel_polys(t, p), p));
                let x = rng.next(p);
                let all_f: Vec<i64> = (0..n).map(|_| rng.next(p)).collect();
                let all_u = encode(&all_f, &kernels, p);
                let mut gamma = 1i64;
                let mut psi = vec![0i64; m];
                for (i, item) in psi.iter_mut().enumerate() {
                    let xi = powmod(x, 1 << i, p);
                    let g = modulo(2 * xi + 1, p);
                    gamma = modulo(gamma * g, p);
                    if g != 0 { *item = modulo((xi + 1) * powmod(g, (p - 2) as usize, p), p); }
                }
                if gamma != 0 { assert_eq!(eval(&all_u, x, p), modulo(gamma * mle(&all_f, &psi, p), p)); }
            }
        }
    }
}

#[test]
fn exact_two_query_mask_distribution() {
    let p = 5i64;
    let n = 4usize;
    for poly in [vec![0i64], vec![3i64, 1, 4, 2]] {
        let mut counts = [[0usize; 5]; 5];
        for a in 0..p {
            for b in 0..p {
                let v1 = modulo(eval(&poly, 1, p) + a + b, p) as usize;
                let v2 = modulo(eval(&poly, 2, p) + powmod(2, n, p) * (a + 2*b), p) as usize;
                counts[v1][v2] += 1;
            }
        }
        assert!(counts.iter().all(|row| row.iter().all(|&x| x == 1)));
    }
}
