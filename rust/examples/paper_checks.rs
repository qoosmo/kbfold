//! Numerical fact-check of the Kronecker-FRI / Boolean-kernel claims.
//! Conventions (0-indexed): K_y(X) = prod_{i=0}^{m-1} (X^{2^i} + y_i), N = 2^m.
//! Boolean-kernel coordinates: U = sum_{y in {0,1}^m} lambda_y K_y, y read as an integer (bit i = y_i).

#[derive(Clone, Copy)]
struct F {
    p: u64,
}
impl F {
    fn add(&self, a: u64, b: u64) -> u64 { (a + b) % self.p }
    fn sub(&self, a: u64, b: u64) -> u64 { (a + self.p - b) % self.p }
    fn mul(&self, a: u64, b: u64) -> u64 { (a as u128 * b as u128 % self.p as u128) as u64 }
    fn neg(&self, a: u64) -> u64 { (self.p - a) % self.p }
    fn pow(&self, mut a: u64, mut e: u64) -> u64 {
        let mut r = 1;
        a %= self.p;
        while e > 0 {
            if e & 1 == 1 { r = self.mul(r, a); }
            a = self.mul(a, a);
            e >>= 1;
        }
        r
    }
    fn inv(&self, a: u64) -> u64 { self.pow(a, self.p - 2) }
    /// element of multiplicative order exactly n (n | p-1)
    fn root(&self, n: u64) -> u64 {
        assert_eq!((self.p - 1) % n, 0);
        for c in 2..self.p {
            let g = self.pow(c, (self.p - 1) / n);
            if (1..n).all(|d| n % d != 0 || self.pow(g, d) != 1) { return g; }
        }
        panic!("no root")
    }
    fn pmul(&self, a: &[u64], b: &[u64]) -> Vec<u64> {
        let mut r = vec![0; a.len() + b.len() - 1];
        for (i, &x) in a.iter().enumerate() {
            if x == 0 { continue; }
            for (j, &y) in b.iter().enumerate() {
                r[i + j] = self.add(r[i + j], self.mul(x, y));
            }
        }
        r
    }
    fn peval(&self, a: &[u64], x: u64) -> u64 {
        a.iter().rev().fold(0, |acc, &c| self.add(self.mul(acc, x), c))
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn fe(&mut self, f: &F) -> u64 { self.next() % f.p }
}

/// K_y(X) = prod_i (X^{2^i} + y_i), coefficient vector of length N
fn kernel(f: &F, y: &[u64]) -> Vec<u64> {
    let mut r = vec![1u64];
    for (i, &yi) in y.iter().enumerate() {
        let mut fac = vec![0u64; (1 << i) + 1];
        fac[0] = yi;
        fac[1 << i] = 1;
        r = f.pmul(&r, &fac);
    }
    r
}

fn bits(y: usize, m: usize) -> Vec<u64> { (0..m).map(|i| ((y >> i) & 1) as u64).collect() }

/// kernel coordinates -> monomial coefficients: u_a = sum_{y : ~y subset a} lambda_y
fn kernel_to_mono(f: &F, lam: &[u64], m: usize) -> Vec<u64> {
    let n = 1 << m;
    let mut nu: Vec<u64> = (0..n).map(|s| lam[(!s) & (n - 1)]).collect();
    for i in 0..m {
        for s in 0..n {
            if s >> i & 1 == 1 { nu[s] = f.add(nu[s], nu[s ^ (1 << i)]); }
        }
    }
    nu
}
fn mono_to_kernel(f: &F, u: &[u64], m: usize) -> Vec<u64> {
    let n = 1 << m;
    let mut nu = u.to_vec();
    for i in 0..m {
        for s in 0..n {
            if s >> i & 1 == 1 { nu[s] = f.sub(nu[s], nu[s ^ (1 << i)]); }
        }
    }
    (0..n).map(|y| nu[(!y) & (n - 1)]).collect()
}

fn check(name: &str, ok: bool) {
    println!("[{}] {}", if ok { "PASS" } else { "FAIL" }, name);
}

fn main() {
    let mut rng = Rng(0x9E3779B97F4A7C15);

    // ---------- Algebraic identities over p = 257 ----------
    let f = F { p: 257 };
    for m in 1..=6usize {
        let n = 1usize << m;
        // (1) evaluation identity  f(y) = [X^{N-1}] U(X) K_y(X), f in monomial (coefficient) form
        let c: Vec<u64> = (0..n).map(|_| rng.fe(&f)).collect();
        let mut ok1 = true;
        let mut ok2 = true;
        let mut ok3 = true;
        let mut ok4 = true;
        let mut ok5 = true;
        for _ in 0..20 {
            let y: Vec<u64> = (0..m).map(|_| rng.fe(&f)).collect();
            let z: Vec<u64> = (0..m).map(|_| rng.fe(&f)).collect();
            let fy = (0..n).fold(0, |acc, a| {
                let mono = (0..m).filter(|&i| a >> i & 1 == 1).fold(1, |t, i| f.mul(t, y[i]));
                f.add(acc, f.mul(c[a], mono))
            });
            let ky = kernel(&f, &y);
            ok1 &= f.pmul(&c, &ky)[n - 1] == fy;
            // (2) bilinear: [X^{N-1}] K_y K_z = prod (y_i + z_i)
            let kz = kernel(&f, &z);
            let rhs = (0..m).fold(1, |t, i| f.mul(t, f.add(y[i], z[i])));
            ok2 &= f.pmul(&ky, &kz)[n - 1] == rhs;
            // (3) squaring: K_y K_{-y} = prod (X^{2^{i+1}} - y_i^2)
            let ym: Vec<u64> = y.iter().map(|&v| f.neg(v)).collect();
            let lhs = f.pmul(&ky, &kernel(&f, &ym));
            let mut r = vec![1u64];
            for i in 0..m {
                let mut fac = vec![0u64; (2 << i) + 1];
                fac[0] = f.neg(f.mul(y[i], y[i]));
                fac[2 << i] = 1;
                r = f.pmul(&r, &fac);
            }
            ok3 &= lhs == r;
            // (4) coefficient formula: coeff of X^a in K_y = prod_{i : a_i = 0} y_i
            ok4 &= (0..n).all(|a| {
                ky[a] == (0..m).filter(|&i| a >> i & 1 == 0).fold(1, |t, i| f.mul(t, y[i]))
            });
        }
        // (5) hypercube sum: sum_{w} f(w) = [X^{N-1}] U * prod(1 + 2 X^{2^i})
        let sum_cube = (0..n).fold(0, |acc, w| {
            let fw = (0..n).fold(0, |s, a| if a & !w == 0 { f.add(s, c[a]) } else { s });
            f.add(acc, fw)
        });
        let mut q = vec![1u64];
        for i in 0..m {
            let mut fac = vec![0u64; (1 << i) + 1];
            fac[0] = 1;
            fac[1 << i] = 2;
            q = f.pmul(&q, &fac);
        }
        ok5 &= f.pmul(&c, &q)[n - 1] == sum_cube;
        check(&format!("m={m}: evaluation identity f(y)=[X^(N-1)] U K_y"), ok1);
        check(&format!("m={m}: bilinear [X^(N-1)] K_y K_z = prod(y_i+z_i)"), ok2);
        check(&format!("m={m}: squaring K_y K_(-y) = prod(X^(2^(i+1)) - y_i^2)"), ok3);
        check(&format!("m={m}: coefficient formula"), ok4);
        check(&format!("m={m}: hypercube-sum identity"), ok5);

        // (6) Boolean kernel basis: transforms are inverse and match explicit expansion
        let lam: Vec<u64> = (0..n).map(|_| rng.fe(&f)).collect();
        let u = kernel_to_mono(&f, &lam, m);
        let mut explicit = vec![0u64; n];
        for y in 0..n {
            let ky = kernel(&f, &bits(y, m));
            for a in 0..n { explicit[a] = f.add(explicit[a], f.mul(lam[y], ky[a])); }
        }
        check(&format!("m={m}: zeta/Moebius basis change"), u == explicit && mono_to_kernel(&f, &u, m) == lam);

        // (7) Level theorem + partition on D = <g>, |D| = N
        let g = f.root(n as u64);
        let mut ok7 = true;
        for y in 0..n {
            let ky = kernel(&f, &bits(y, m));
            let mut zeros = 0;
            for t in 0..n {
                let is_zero = f.peval(&ky, f.pow(g, t as u64)) == 0;
                let pred = t != 0 && (y >> (m - 1 - t.trailing_zeros() as usize)) & 1 == 1;
                ok7 &= is_zero == pred;
                zeros += is_zero as usize;
            }
            ok7 &= zeros == y; // |Z(K_y)| = val(y)
        }
        let sizes: Vec<usize> = (0..m).map(|j| (1..n).filter(|t| m - 1 - t.trailing_zeros() as usize == j).count()).collect();
        let part_ok = sizes.iter().enumerate().all(|(j, &s)| s == 1 << j);
        check(&format!("m={m}: level theorem + zero count = val(y)"), ok7);
        check(&format!("m={m}: level partition sizes {:?}", sizes), part_ok);

        // (8) character condition  <=>  deg < 2^k
        let mut ok8 = true;
        for k in 0..=m {
            // CH -> low degree
            let mu: Vec<u64> = (0..1 << k).map(|_| rng.fe(&f)).collect();
            let lam: Vec<u64> = (0..n).map(|y| {
                let x = y & ((1 << k) - 1);
                let h = y >> k;
                let sgn = ((m - k) - h.count_ones() as usize) % 2;
                if sgn == 0 { mu[x] } else { f.neg(mu[x]) }
            }).collect();
            let u = kernel_to_mono(&f, &lam, m);
            ok8 &= u[1 << k..].iter().all(|&v| v == 0);
            // low degree -> CH
            let mut u2 = vec![0u64; n];
            for a in 0..1 << k { u2[a] = rng.fe(&f); }
            let l2 = mono_to_kernel(&f, &u2, m);
            ok8 &= (0..n).all(|y| {
                let x = y & ((1 << k) - 1);
                let h = y >> k;
                let top = l2[x | (((1 << (m - k)) - 1) << k)];
                let sgn = ((m - k) - h.count_ones() as usize) % 2;
                l2[y] == if sgn == 0 { top } else { f.neg(top) }
            });
        }
        check(&format!("m={m}: character condition <=> deg < 2^k (all k)"), ok8);

        // (9) FRI fold <-> kernel fold  (rho, 1+rho) ; and (1-T, T) = (2T-1) U_e + (1-T) U_o
        if m >= 2 {
            let lam: Vec<u64> = (0..n).map(|_| rng.fe(&f)).collect();
            let u = kernel_to_mono(&f, &lam, m);
            let rho = rng.fe(&f);
            let fri: Vec<u64> = (0..n / 2).map(|j| f.add(u[2 * j], f.mul(rho, u[2 * j + 1]))).collect();
            let kf: Vec<u64> = (0..n / 2).map(|j| f.add(f.mul(rho, lam[2 * j]), f.mul(f.add(1, rho), lam[2 * j + 1]))).collect();
            let ok9a = kernel_to_mono(&f, &kf, m - 1) == fri;
            let t = rng.fe(&f);
            let ml: Vec<u64> = (0..n / 2).map(|j| f.add(f.mul(f.sub(1, t), lam[2 * j]), f.mul(t, lam[2 * j + 1]))).collect();
            let fri_t: Vec<u64> = (0..n / 2).map(|j| f.add(f.mul(f.sub(f.mul(2, t), 1), u[2 * j]), f.mul(f.sub(1, t), u[2 * j + 1]))).collect();
            let ok9b = kernel_to_mono(&f, &ml, m - 1) == fri_t;
            check(&format!("m={m}: FRI fold U_e+rho U_o  <->  rho*lam0+(1+rho)*lam1"), ok9a);
            check(&format!("m={m}: ML fold (1-T)lam0+T lam1 <-> (2T-1)U_e+(1-T)U_o"), ok9b);
        }
    }

    // ---------- Refuted conjecture ("Theorem G", local-to-global) over p = 17 ----------
    // This block documents why a local-to-global distance claim from an early draft was
    // dropped: it finds counterexamples. The claim is NOT part of the paper.
    // dist = relative Hamming distance of M_D(lambda) to RS_{D,<2^k} on D = <g>, |D| = N.
    // eps_D(lambda) = min over lambda* in CH of sum_y (N - val(y))/N * [lambda_y != lambda*_y]
    // Claim: dist >= c * eps_D with c = 2(2^k+1)/(N(N+1)).
    println!("\n--- Refuted early-draft conjecture \"Theorem G\" (not in the paper; counterexamples expected), p = 17 ---");
    let f = F { p: 17 };
    for &(m, k) in &[(2usize, 1usize), (3, 1), (3, 2), (4, 1), (4, 2)] {
        let n = 1usize << m;
        let g = f.root(n as u64);
        let dom: Vec<u64> = (0..n).map(|t| f.pow(g, t as u64)).collect();
        let c_inf = 2.0 * ((1 << k) as f64 + 1.0) / (n as f64 * (n as f64 + 1.0));
        // exact distance to RS by brute force over all p^(2^k) codewords
        let dist = |w: &[u64]| -> usize {
            let kk = 1usize << k;
            let total = (f.p as usize).pow(kk as u32);
            let mut best = n;
            for idx in 0..total {
                let mut coeffs = vec![0u64; kk];
                let mut v = idx;
                for cf in coeffs.iter_mut() { *cf = (v % f.p as usize) as u64; v /= f.p as usize; }
                let d = dom.iter().zip(w).filter(|&(&x, &wv)| f.peval(&coeffs, x) != wv).count();
                best = best.min(d);
            }
            best
        };
        let eps = |w: &[u64]| -> f64 {
            // interpolate on D (inverse DFT), then to kernel coords
            let ninv = f.inv(n as u64);
            let ginv = f.inv(g);
            let u: Vec<u64> = (0..n).map(|a| {
                let s = (0..n).fold(0, |acc, t| f.add(acc, f.mul(w[t], f.pow(ginv, (a * t) as u64))));
                f.mul(s, ninv)
            }).collect();
            let lam = mono_to_kernel(&f, &u, m);
            let mut tot = 0.0;
            for x in 0..1usize << k {
                let mut best = f64::MAX;
                for mu in 0..f.p {
                    let mut cost = 0.0;
                    for h in 0..1usize << (m - k) {
                        let y = x | (h << k);
                        let sgn = ((m - k) - h.count_ones() as usize) % 2;
                        let target = if sgn == 0 { mu } else { f.neg(mu) };
                        if lam[y] != target { cost += (n - y) as f64 / n as f64; }
                    }
                    best = best.min(cost);
                }
                tot += best;
            }
            tot
        };
        let mut worst_ratio = f64::MAX;
        let mut violations = 0;
        let trials = 300;
        for trial in 0..trials {
            // mix of: codeword + e errors, and fully random words
            let kk = 1usize << k;
            let coeffs: Vec<u64> = (0..kk).map(|_| rng.fe(&f)).collect();
            let mut w: Vec<u64> = dom.iter().map(|&x| f.peval(&coeffs, x)).collect();
            let errs = if trial % 3 == 2 { n } else { 1 + trial % 2 };
            for _ in 0..errs {
                let pos = (rng.next() % n as u64) as usize;
                w[pos] = f.add(w[pos], 1 + rng.next() % (f.p - 1));
            }
            let d = dist(&w) as f64 / n as f64;
            let e = eps(&w);
            if e > 0.0 {
                worst_ratio = worst_ratio.min(d / e);
                if d + 1e-12 < c_inf * e { violations += 1; }
            }
        }
        println!(
            "m={m} k={k}: claimed c_inf = {:.5}, empirical min dist/eps = {:.5}, violations {}/{}",
            c_inf, worst_ratio, violations, trials
        );
    }

    // ---------- explicit counterexample: w = e_1 (indicator of the point 1), m=3, k=1, p=17 ----------
    {
        let f = F { p: 17 };
        let (m, k) = (3usize, 1usize);
        let n = 1usize << m;
        let g = f.root(n as u64);
        let ninv = f.inv(n as u64);
        let ginv = f.inv(g);
        let mut w = vec![0u64; n];
        w[1] = 1; // word = indicator of alpha = g ; distance 1/N from the zero codeword
        let u: Vec<u64> = (0..n).map(|a| {
            let s = (0..n).fold(0, |acc, t| f.add(acc, f.mul(w[t], f.pow(ginv, (a * t) as u64))));
            f.mul(s, ninv)
        }).collect();
        let lam = mono_to_kernel(&f, &u, m);
        println!("\ncounterexample m=3,k=1,p=17: w = e_(alpha=g), dist = 1/8");
        println!("  U coefficients  = {:?}", u);
        println!("  lambda (kernel) = {:?}", lam);
        let mut tot = 0.0;
        for x in 0..1usize << k {
            let mut best = (f64::MAX, 0);
            for mu in 0..f.p {
                let mut cost = 0.0;
                for h in 0..1usize << (m - k) {
                    let y = x | (h << k);
                    let sgn = ((m - k) - h.count_ones() as usize) % 2;
                    let target = if sgn == 0 { mu } else { f.neg(mu) };
                    if lam[y] != target { cost += (n - y) as f64 / n as f64; }
                }
                if cost < best.0 { best = (cost, mu); }
            }
            tot += best.0;
        }
        let c = 2.0 * 3.0 / (8.0 * 9.0);
        println!("  min eps_D over CH = {tot:.4}; c_inf*eps = {:.4} vs dist = 0.125 -> {}", c * tot, if c * tot > 0.125 { "counterexample to the dropped conjecture" } else { "ok" });
    }

    // ---------- Scheme B core: codeword folding computes the evaluation-form MLE ----------
    // f: table on {0,1}^m (lambda = f), U = sum_y f(y) K_y, codeword = U on L = <w>, |L| = N/rho.
    // Fold each round on EVALUATIONS: U_e(x^2) = (w(x)+w(-x))/2, U_o(x^2) = (w(x)-w(-x))/(2x),
    // new word = (2T-1) U_e + (1-T) U_o.  After m rounds the word must be the constant f~(T_1..T_m).
    {
        let f = F { p: 257 };
        let mut ok = true;
        for m in 1..=5usize {
            let n = 1usize << m;
            let lsize = 4 * n; // rate 1/4
            let wgen = f.root(lsize as u64);
            for _ in 0..10 {
                let table: Vec<u64> = (0..n).map(|_| rng.fe(&f)).collect();
                let u = kernel_to_mono(&f, &table, m);
                let mut dom: Vec<u64> = (0..lsize).map(|t| f.pow(wgen, t as u64)).collect();
                let mut word: Vec<u64> = dom.iter().map(|&x| f.peval(&u, x)).collect();
                let ts: Vec<u64> = (0..m).map(|_| rng.fe(&f)).collect();
                let inv2 = f.inv(2);
                for &t in &ts {
                    let half = dom.len() / 2; // dom[j+half] = -dom[j]
                    let mut nw = Vec::with_capacity(half);
                    for j in 0..half {
                        let (a, b, x) = (word[j], word[j + half], dom[j]);
                        let ue = f.mul(f.add(a, b), inv2);
                        let uo = f.mul(f.sub(a, b), f.inv(f.mul(2, x)));
                        nw.push(f.add(f.mul(f.sub(f.mul(2, t), 1), ue), f.mul(f.sub(1, t), uo)));
                    }
                    word = nw;
                    dom = (0..half).map(|j| f.mul(dom[j], dom[j])).collect();
                }
                // multilinear extension of table at T (bit i <-> T_i, i = 0 folded first)
                let mut v = table.clone();
                for &t in &ts {
                    v = (0..v.len() / 2).map(|j| f.add(f.mul(f.sub(1, t), v[2 * j]), f.mul(t, v[2 * j + 1]))).collect();
                }
                ok &= word.iter().all(|&x| x == v[0]);
            }
        }
        check("scheme B: m codeword folds (2T-1)U_e+(1-T)U_o give constant f~(T) (m=1..5, rate 1/4)", ok);
    }

    // ---------- Evaluation as a scaled MLE: U(x) = prod_i (2x^{2^i}+1) * lam~(z(x)), z_i = (x^{2^i}+1)/(2x^{2^i}+1) ----------
    {
        let f = F { p: 257 };
        let mut ok = true;
        for m in 1..=6usize {
            let n = 1usize << m;
            for _ in 0..30 {
                let lam: Vec<u64> = (0..n).map(|_| rng.fe(&f)).collect();
                let u = kernel_to_mono(&f, &lam, m);
                let x = rng.fe(&f);
                let mut scale = 1u64;
                let mut z = vec![0u64; m];
                let mut bad = false;
                for i in 0..m {
                    let xp = f.pow(x, 1u64 << i);
                    let s = f.add(f.mul(2, xp), 1);
                    if s == 0 { bad = true; break; }
                    scale = f.mul(scale, s);
                    z[i] = f.mul(f.add(xp, 1), f.inv(s));
                }
                if bad { continue; }
                let mut v = lam.clone();
                for &t in &z {
                    v = (0..v.len() / 2).map(|j| f.add(f.mul(f.sub(1, t), v[2 * j]), f.mul(t, v[2 * j + 1]))).collect();
                }
                ok &= f.peval(&u, x) == f.mul(scale, v[0]);
            }
        }
        check("U(x) = prod(2x^(2^i)+1) * lam~((x^(2^i)+1)/(2x^(2^i)+1))", ok);
    }

    // ---------- explicit inverse: lambda_b = sum_{a <= ~b} (-1)^{wt(~b)-wt(a)} u_a ; constant 1 in kernel coords ----------
    {
        let f = F { p: 257 };
        let mut ok = true;
        for m in 1..=6usize {
            let n = 1usize << m;
            let u: Vec<u64> = (0..n).map(|_| rng.fe(&f)).collect();
            let lam = mono_to_kernel(&f, &u, m);
            for b in 0..n {
                let nb = !b & (n - 1);
                let mut s = 0u64;
                for a in 0..n {
                    if a & !nb == 0 {
                        let sg = (nb.count_ones() - a.count_ones()) % 2;
                        s = if sg == 0 { f.add(s, u[a]) } else { f.sub(s, u[a]) };
                    }
                }
                ok &= s == lam[b];
            }
            let mut one = vec![0u64; n];
            one[0] = 1;
            let l1 = mono_to_kernel(&f, &one, m);
            ok &= (0..n).all(|h| l1[h] == if (m - h.count_ones() as usize) % 2 == 0 { 1 } else { f.neg(1) });
        }
        check("explicit inverse formula + kernel coordinates of the constant 1", ok);
    }

    // ---------- Section 4 checks ----------
    {
        let f = F { p: 257 };
        let inv2 = f.inv(2);
        let mut ok_word = true;
        let mut ok_line = true;
        let mut ok_fri = true;
        let mut ok_even_odd = true;
        for m in 1..=5usize {
            let n = 1usize << m;
            let lsize = 4 * n;
            let wg = f.root(lsize as u64);
            let dom: Vec<u64> = (0..lsize).map(|t| f.pow(wg, t as u64)).collect();
            let half = lsize / 2;
            for _ in 0..10 {
                // arbitrary word (not a codeword)
                let w: Vec<u64> = (0..lsize).map(|_| rng.fe(&f)).collect();
                let t = rng.fe(&f);
                for j in 0..half {
                    let (x, a, b) = (dom[j], w[j], w[j + half]);
                    let we = f.mul(f.add(a, b), inv2);
                    let wo = f.mul(f.sub(a, b), f.inv(f.mul(2, x)));
                    let def = f.add(f.mul(f.sub(f.mul(2, t), 1), we), f.mul(f.sub(1, t), wo));
                    let c1 = f.add(f.mul(f.sub(f.mul(2, t), 1), x), f.sub(1, t));
                    let c2 = f.sub(f.mul(f.sub(f.mul(2, t), 1), x), f.sub(1, t));
                    let expl = f.mul(f.add(f.mul(c1, a), f.mul(c2, b)), f.inv(f.mul(2, x)));
                    ok_word &= def == expl;
                    let uu = f.sub(wo, we);
                    let vv = f.sub(f.mul(2, we), wo);
                    ok_line &= def == f.add(uu, f.mul(t, vv));
                    ok_line &= f.add(uu, vv) == we && f.add(f.mul(2, uu), vv) == wo;
                }
            }
            // even/odd in kernel coordinates
            let lam: Vec<u64> = (0..n).map(|_| rng.fe(&f)).collect();
            let u = kernel_to_mono(&f, &lam, m);
            if m >= 1 {
                let ue: Vec<u64> = (0..n / 2).map(|j| u[2 * j]).collect();
                let uo: Vec<u64> = (0..n / 2).map(|j| u[2 * j + 1]).collect();
                let le: Vec<u64> = (0..n / 2).map(|j| lam[2 * j + 1]).collect();
                let lo: Vec<u64> = (0..n / 2).map(|j| f.add(lam[2 * j], lam[2 * j + 1])).collect();
                ok_even_odd &= kernel_to_mono(&f, &le, m - 1) == ue && kernel_to_mono(&f, &lo, m - 1) == uo;
            }
            // m classical FRI folds U_e + rho U_o on coefficients = prod(1+2rho_i) * lam~((1+rho_i)/(1+2rho_i))
            let rhos: Vec<u64> = (0..m).map(|_| rng.fe(&f)).collect();
            let mut c = u.clone();
            for &r in &rhos { c = (0..c.len() / 2).map(|j| f.add(c[2 * j], f.mul(r, c[2 * j + 1]))).collect(); }
            let mut v = lam.clone();
            let mut sc = 1u64;
            let mut skip = false;
            for &r in &rhos {
                let d = f.add(1, f.mul(2, r));
                if d == 0 { skip = true; break; }
                sc = f.mul(sc, d);
                let t = f.mul(f.add(1, r), f.inv(d));
                v = (0..v.len() / 2).map(|j| f.add(f.mul(f.sub(1, t), v[2 * j]), f.mul(t, v[2 * j + 1]))).collect();
            }
            if !skip { ok_fri &= c[0] == f.mul(sc, v[0]); }
        }
        check("sec4: even/odd split in kernel coordinates", ok_even_odd);
        check("sec4: explicit per-fibre fold formula on arbitrary words", ok_word);
        check("sec4: line form u + T v and its inverse", ok_line);
        check("sec4: m classical FRI folds = prod(1+2rho) * lam~((1+rho)/(1+2rho))", ok_fri);
    }

    // ---------- Section 5: end-to-end IOP simulation (no Merkle), stop after s folds ----------
    {
        let f = F { p: 257 };
        let inv2 = f.inv(2);
        let eq1 = |a: u64, b: u64| -> u64 { f.add(f.mul(a, b), f.mul(f.sub(1, a), f.sub(1, b))) };
        // returns true if verifier accepts
        let run = |rng: &mut Rng, m: usize, s: usize, cheat: bool| -> bool {
            let n = 1usize << m;
            let lsize = 4 * n;
            let wg = f.root(lsize as u64);
            let table: Vec<u64> = (0..n).map(|_| rng.fe(&f)).collect();
            let z: Vec<u64> = (0..m).map(|_| rng.fe(&f)).collect();
            // true value
            let mut tv = table.clone();
            for &t in &z { tv = (0..tv.len() / 2).map(|j| f.add(f.mul(f.sub(1, t), tv[2 * j]), f.mul(t, tv[2 * j + 1]))).collect(); }
            let v = if cheat { f.add(tv[0], 1) } else { tv[0] };
            // commit
            let u = kernel_to_mono(&f, &table, m);
            let mut doms: Vec<Vec<u64>> = vec![(0..lsize).map(|t| f.pow(wg, t as u64)).collect()];
            let mut words: Vec<Vec<u64>> = vec![doms[0].iter().map(|&x| f.peval(&u, x)).collect()];
            // prover state
            let mut a = table.clone();
            let mut e: Vec<u64> = (0..n).map(|b| (0..m).fold(1, |acc, i| f.mul(acc, eq1(((b >> i) & 1) as u64, z[i])))).collect();
            let mut claim = v;
            let mut ts = vec![];
            for j in 0..s {
                // h_j at 0,1,2
                let half = a.len() / 2;
                let mut h = [0u64; 3];
                for (k, x) in [0u64, 1, 2].iter().enumerate() {
                    for b in 0..half {
                        let av = f.add(f.mul(f.sub(1, *x), a[2 * b]), f.mul(*x, a[2 * b + 1]));
                        let ev = f.add(f.mul(f.sub(1, *x), e[2 * b]), f.mul(*x, e[2 * b + 1]));
                        h[k] = f.add(h[k], f.mul(av, ev));
                    }
                }
                if cheat && j == 0 { // cheating prover shifts h_0 so the round-0 check passes
                    let d = f.sub(claim, f.add(h[0], h[1]));
                    let d2 = f.mul(d, inv2);
                    for k in 0..3 { h[k] = f.add(h[k], d2); }
                }
                if f.add(h[0], h[1]) != claim { return false; }
                let t = rng.fe(&f);
                // h(t) by quadratic interpolation through 0,1,2
                let l0 = f.mul(f.mul(f.sub(t, 1), f.sub(t, 2)), inv2);
                let l1 = f.neg(f.mul(t, f.sub(t, 2)));
                let l2 = f.mul(f.mul(t, f.sub(t, 1)), inv2);
                claim = f.add(f.add(f.mul(l0, h[0]), f.mul(l1, h[1])), f.mul(l2, h[2]));
                ts.push(t);
                a = (0..half).map(|b| f.add(f.mul(f.sub(1, t), a[2 * b]), f.mul(t, a[2 * b + 1]))).collect();
                e = (0..half).map(|b| f.add(f.mul(f.sub(1, t), e[2 * b]), f.mul(t, e[2 * b + 1]))).collect();
                // fold committed word
                let w = words.last().unwrap();
                let d = doms.last().unwrap();
                let hl = d.len() / 2;
                let nw: Vec<u64> = (0..hl).map(|i| {
                    let we = f.mul(f.add(w[i], w[i + hl]), inv2);
                    let wo = f.mul(f.sub(w[i], w[i + hl]), f.inv(f.mul(2, d[i])));
                    f.add(f.mul(f.sub(f.mul(2, t), 1), we), f.mul(f.sub(1, t), wo))
                }).collect();
                let nd: Vec<u64> = (0..hl).map(|i| f.mul(d[i], d[i])).collect();
                words.push(nw);
                doms.push(nd);
            }
            // final message g (honest: a). Cheater: must make final claim hold -> adjust g
            let mut g = a.clone();
            let eqt = (0..s).fold(1, |acc, j| f.mul(acc, eq1(ts[j], z[j])));
            let gz = |g: &Vec<u64>| -> u64 {
                let mut vv = g.clone();
                for &t in &z[s..] { vv = (0..vv.len() / 2).map(|j| f.add(f.mul(f.sub(1, t), vv[2 * j]), f.mul(t, vv[2 * j + 1]))).collect(); }
                vv[0]
            };
            if cheat {
                // shift g by c*delta_0 so that eqt * g~(z_{>=s}) == claim
                let cur = f.mul(eqt, gz(&g));
                let e0 = { let mut d0 = vec![0u64; g.len()]; d0[0] = 1; f.mul(eqt, gz(&d0)) };
                if e0 != 0 { let c = f.mul(f.sub(claim, cur), f.inv(e0)); g[0] = f.add(g[0], c); }
            }
            if f.mul(eqt, gz(&g)) != claim { return false; }
            // queries
            let gm = kernel_to_mono(&f, &g, m - s);
            for _ in 0..20 {
                let mut idx = (rng.next() % lsize as u64) as usize;
                for j in 0..s {
                    let d = &doms[j];
                    let hl = d.len() / 2;
                    let i = idx % hl;
                    let (x, w0, w1) = (d[i], words[j][i], words[j][i + hl]);
                    let t = ts[j];
                    let c1 = f.add(f.mul(f.sub(f.mul(2, t), 1), x), f.sub(1, t));
                    let c2 = f.sub(f.mul(f.sub(f.mul(2, t), 1), x), f.sub(1, t));
                    let folded = f.mul(f.add(f.mul(c1, w0), f.mul(c2, w1)), f.inv(f.mul(2, x)));
                    let next = if j + 1 < s { words[j + 1][i] } else { f.peval(&gm, doms[j + 1][i]) };
                    if folded != next { return false; }
                    idx = i;
                }
                if s == 0 {
                    let i = idx;
                    if words[0][i] != f.peval(&gm, doms[0][i]) { return false; }
                }
            }
            true
        };
        let mut honest_ok = true;
        let mut cheat_rej = 0;
        let mut cheat_tot = 0;
        for m in 1..=5usize {
            for s in 0..=m {
                for _ in 0..5 {
                    honest_ok &= run(&mut rng, m, s, false);
                    if m >= 2 && s >= 1 { cheat_tot += 1; if !run(&mut rng, m, s, true) { cheat_rej += 1; } }
                }
            }
        }
        check("sec5: honest prover always accepted (m=1..5, all stop rounds s)", honest_ok);
        println!("sec5: cheating prover (wrong value, consistent sumcheck, adjusted final table) rejected {cheat_rej}/{cheat_tot}");
    }

    // ---------- Section 6 checks ----------
    {
        // Lemma: a nonzero fibre error survives fold_T for all but at most one T (exhaustive over F_17)
        let f = F { p: 17 };
        let mut ok = true;
        for x in 1..17u64 {
            for e1 in 0..17u64 { for e2 in 0..17u64 {
                if e1 == 0 && e2 == 0 { continue; }
                let mut killed = 0;
                for t in 0..17u64 {
                    let c1 = f.add(f.mul(f.sub(f.mul(2, t), 1), x), f.sub(1, t));
                    let c2 = f.sub(f.mul(f.sub(f.mul(2, t), 1), x), f.sub(1, t));
                    if f.add(f.mul(c1, e1), f.mul(c2, e2)) == 0 { killed += 1; }
                }
                ok &= killed <= 1;
            }}
        }
        check("sec6: nonzero fibre error killed by at most one T (exhaustive F_17)", ok);

        // Lemma (via BCIKS): fibre-far word => at most n_{j+1} challenges T give a delta-close fold.
        // F_17, L of order 8, C_j = RS[L,4] (rate 1/2), C_{j+1} = RS[L^2,2], delta = 1/4.
        let n = 8usize;
        let g = f.root(n as u64);
        let dom: Vec<u64> = (0..n).map(|t| f.pow(g, t as u64)).collect(); // dom[i+4] = -dom[i]
        let dom2: Vec<u64> = (0..4).map(|i| f.mul(dom[i], dom[i])).collect();
        let cw4: Vec<Vec<u64>> = (0..17u64.pow(4)).map(|idx| {
            let c = [idx % 17, idx / 17 % 17, idx / 289 % 17, idx / 4913 % 17];
            dom.iter().map(|&x| f.peval(&c, x)).collect()
        }).collect();
        let cw2: Vec<Vec<u64>> = (0..289u64).map(|idx| {
            let c = [idx % 17, idx / 17];
            dom2.iter().map(|&x| f.peval(&c, x)).collect()
        }).collect();
        let inv2 = f.inv(2);
        let mut ok2 = true;
        let mut far_words = 0;
        let mut worst = 0;
        for trial in 0..400 {
            // words at various distances: codeword + errors on k fibres
            let base = &cw4[(rng.next() % cw4.len() as u64) as usize];
            let mut w = base.clone();
            let k = trial % 5;
            for fib in 0..k { let i = (fib + (rng.next() % 4) as usize) % 4; w[i] = f.add(w[i], 1 + rng.next() % 16); if rng.next() % 2 == 0 { w[i+4] = f.add(w[i+4], 1 + rng.next() % 16); } }
            // fibre distance to C_j
            let fd = cw4.iter().map(|c| (0..4).filter(|&i| w[i] != c[i] || w[i + 4] != c[i + 4]).count()).min().unwrap();
            if fd * 4 <= 4 { continue; } // fibre distance <= 1/4: not far
            far_words += 1;
            let mut close_t = 0;
            for t in 0..17u64 {
                let fw: Vec<u64> = (0..4).map(|i| {
                    let we = f.mul(f.add(w[i], w[i + 4]), inv2);
                    let wo = f.mul(f.sub(w[i], w[i + 4]), f.inv(f.mul(2, dom[i])));
                    f.add(f.mul(f.sub(f.mul(2, t), 1), we), f.mul(f.sub(1, t), wo))
                }).collect();
                let hd = cw2.iter().map(|c| (0..4).filter(|&i| fw[i] != c[i]).count()).min().unwrap();
                if hd * 4 <= 4 { close_t += 1; }
            }
            worst = worst.max(close_t);
            ok2 &= close_t <= 4;
        }
        check(&format!("sec6: fibre-far => #T with delta-close fold <= n_(j+1)=4 ({far_words} far words, worst {worst})"), ok2);
    }

    // ---------- Section 6: brute-force test of the backward-induction claim ----------
    // F_17, m=2, L order 8 (rate 1/2), s=2, delta=1/4. Claim: Good_0 & Good_1 & p > 1-delta => honest chain (G = fold^2 of decoded c_0).
    {
        let f = F { p: 17 };
        let inv2 = f.inv(2);
        let g8 = f.root(8);
        let l0: Vec<u64> = (0..8).map(|t| f.pow(g8, t as u64)).collect();
        let l1: Vec<u64> = (0..4).map(|i| f.mul(l0[i], l0[i])).collect();
        let l2: Vec<u64> = (0..2).map(|i| f.mul(l1[i], l1[i])).collect();
        let fold = |w: &Vec<u64>, d: &Vec<u64>, t: u64| -> Vec<u64> {
            let h = d.len() / 2;
            (0..h).map(|i| {
                let we = f.mul(f.add(w[i], w[i + h]), inv2);
                let wo = f.mul(f.sub(w[i], w[i + h]), f.inv(f.mul(2, d[i])));
                f.add(f.mul(f.sub(f.mul(2, t), 1), we), f.mul(f.sub(1, t), wo))
            }).collect()
        };
        let code = |d: &Vec<u64>, k: usize| -> Vec<Vec<u64>> {
            (0..17u64.pow(k as u32)).map(|idx| {
                let c: Vec<u64> = (0..k).map(|i| idx / 17u64.pow(i as u32) % 17).collect();
                d.iter().map(|&x| f.peval(&c, x)).collect()
            }).collect()
        };
        let c0s = code(&l0, 4);
        let c1s = code(&l1, 2);
        let c2s = code(&l2, 1);
        // fibre-distance decoding (returns Some(codeword) if fibre distance <= delta)
        let fdec = |w: &Vec<u64>, cs: &Vec<Vec<u64>>, dlt_fib: usize| -> Option<Vec<u64>> {
            let h = w.len() / 2;
            cs.iter().find(|c| (0..h).filter(|&i| w[i] != c[i] || w[i + h] != c[i + h]).count() <= dlt_fib).cloned()
        };
        let hclose = |w: &Vec<u64>, cs: &Vec<Vec<u64>>, dlt: usize| -> bool {
            cs.iter().any(|c| (0..w.len()).filter(|&i| w[i] != c[i]).count() <= dlt)
        };
        let good = |w: &Vec<u64>, d: &Vec<u64>, t: u64, cs: &Vec<Vec<u64>>, next: &Vec<Vec<u64>>, dlt_fib: usize, dlt_next: usize| -> bool {
            match fdec(w, cs, dlt_fib) {
                None => !hclose(&fold(w, d, t), next, dlt_next),
                Some(c) => {
                    let h = w.len() / 2;
                    let fw = fold(w, d, t);
                    let fc = fold(&c, d, t);
                    (0..h).all(|i| !(w[i] != c[i] || w[i + h] != c[i + h]) || fw[i] != fc[i])
                }
            }
        };
        let mut violations = 0;
        let mut tested = 0;
        let mut high_p = 0;
        for _ in 0..3000 {
            let mut w0 = c0s[(rng.next() % c0s.len() as u64) as usize].clone();
            let k = (rng.next() % 4) as usize;
            for _ in 0..k { let i = (rng.next() % 8) as usize; w0[i] = rng.fe(&f); }
            let t0 = rng.fe(&f);
            let mut w1 = fold(&w0, &l0, t0);
            let r = (rng.next() % 3) as usize;
            for _ in 0..r { let i = (rng.next() % 4) as usize; w1[i] = rng.fe(&f); }
            let t1 = rng.fe(&f);
            let fw1 = fold(&w1, &l1, t1);
            let gval = match rng.next() % 3 { 0 => fw1[0], 1 => fw1[1], _ => rng.fe(&f) };
            // P_0: x in L0 (index i) passes: level0 check at y=i%4, level1 check at y'=(i%4)%2
            let pass = (0..8).filter(|&i| {
                let y = i % 4;
                let fw0 = fold(&w0, &l0, t0);
                fw0[y] == w1[y] && fw1[y % 2] == gval
            }).count();
            let p_ok = pass * 4 > 8 * 3; // p > 3/4
            // delta = 1/4: fibre budget at level 0 = 1 of 4 fibres, next Hamming budget 1 of 4 ; level 1: 0 of 2 fibres, Hamming 0 of 2
            let g0 = good(&w0, &l0, t0, &c0s, &c1s, 1, 1);
            let g1 = good(&w1, &l1, t1, &c1s, &c2s, 0, 0);
            if !(g0 && g1) { continue; }
            tested += 1;
            if !p_ok { continue; }
            high_p += 1;
            let honest = match fdec(&w0, &c0s, 1) {
                None => false,
                Some(c0) => { let c1 = fold(&c0, &l0, t0); let c2 = fold(&c1, &l1, t1); c2[0] == gval && c2[1] == gval }
            };
            if !honest { violations += 1; }
        }
        check(&format!("sec6: Good & p>1-delta => honest chain ({tested} transcripts with Good, {high_p} with p>3/4, violations {violations})"), violations == 0);
    }

    // ---------- Section 6.4: brute-force test of Lemma 6.8 (one round of the chain), j = 0 and j = 1 ----------
    // F_17, m=2, L order 8 (rate 1/2), s=2, delta=1/4.
    {
        let f = F { p: 17 };
        let inv2 = f.inv(2);
        let g8 = f.root(8);
        let l0: Vec<u64> = (0..8).map(|t| f.pow(g8, t as u64)).collect();
        let l1: Vec<u64> = (0..4).map(|i| f.mul(l0[i], l0[i])).collect();
        let l2: Vec<u64> = (0..2).map(|i| f.mul(l1[i], l1[i])).collect();
        let fold = |w: &Vec<u64>, d: &Vec<u64>, t: u64| -> Vec<u64> {
            let h = d.len() / 2;
            (0..h).map(|i| {
                let we = f.mul(f.add(w[i], w[i + h]), inv2);
                let wo = f.mul(f.sub(w[i], w[i + h]), f.inv(f.mul(2, d[i])));
                f.add(f.mul(f.sub(f.mul(2, t), 1), we), f.mul(f.sub(1, t), wo))
            }).collect()
        };
        let code = |d: &Vec<u64>, k: usize| -> Vec<Vec<u64>> {
            (0..17u64.pow(k as u32)).map(|idx| {
                let c: Vec<u64> = (0..k).map(|i| idx / 17u64.pow(i as u32) % 17).collect();
                d.iter().map(|&x| f.peval(&c, x)).collect()
            }).collect()
        };
        let c0s = code(&l0, 4);
        let c1s = code(&l1, 2);
        let c2s = code(&l2, 1);
        let fib_dist = |w: &Vec<u64>, c: &Vec<u64>| -> usize { let h = w.len() / 2; (0..h).filter(|&i| w[i] != c[i] || w[i + h] != c[i + h]).count() };
        let good = |w: &Vec<u64>, d: &Vec<u64>, t: u64, cs: &Vec<Vec<u64>>, next: &Vec<Vec<u64>>, dfib: usize, dnext: usize| -> bool {
            match cs.iter().find(|c| fib_dist(w, c) <= dfib) {
                None => !next.iter().any(|c| (0..c.len()).filter(|&i| fold(w, d, t)[i] != c[i]).count() <= dnext),
                Some(c) => { let h = w.len() / 2; let fw = fold(w, d, t); let fc = fold(c, d, t);
                    (0..h).all(|i| !(w[i] != c[i] || w[i + h] != c[i + h]) || fw[i] != fc[i]) }
            }
        };
        let (mut viol, mut tested) = (0, 0);
        for _ in 0..4000 {
            let mut w0 = c0s[(rng.next() % c0s.len() as u64) as usize].clone();
            for _ in 0..(rng.next() % 4) { let i = (rng.next() % 8) as usize; w0[i] = rng.fe(&f); }
            let t0 = rng.fe(&f);
            let f1 = fold(&w0, &l0, t0);
            let mut w1 = f1.clone();
            for _ in 0..(rng.next() % 3) { let i = (rng.next() % 4) as usize; w1[i] = rng.fe(&f); }
            let t1 = rng.fe(&f);
            let f2 = fold(&w1, &l1, t1);
            // index of x in L: i in [8]; x_1 index i % 4, x_2 index i % 2
            // j = 0: gamma' in C_1, P_1(gamma') = {x : f1(x1) = gamma'(x1)}
            if good(&w0, &l0, t0, &c0s, &c1s, 1, 1) {
                for gp in &c1s {
                    let p1: Vec<usize> = (0..8).filter(|&i| f1[i % 4] == gp[i % 4]).collect();
                    if p1.len() * 4 < 8 * 3 { continue; }
                    tested += 1;
                    match c0s.iter().find(|c| fib_dist(&w0, c) <= 1) {
                        None => viol += 1,
                        Some(g0) => {
                            if &fold(g0, &l0, t0) != gp { viol += 1; }
                            // P_0(g0) = {x : w0 = g0 on fibre of x}
                            if !p1.iter().all(|&i| w0[i % 4] == g0[i % 4] && w0[i % 4 + 4] == g0[i % 4 + 4]) { viol += 1; }
                        }
                    }
                }
            }
            // j = 1: gamma' in C_2, P_2(gamma') = {x : x1 not in E1, f2(x2) = gamma'(x2)}
            if good(&w1, &l1, t1, &c1s, &c2s, 0, 0) {
                for gp in &c2s {
                    let p2: Vec<usize> = (0..8).filter(|&i| f1[i % 4] == w1[i % 4] && f2[i % 2] == gp[i % 2]).collect();
                    if p2.len() * 4 < 8 * 3 { continue; }
                    tested += 1;
                    match c1s.iter().find(|c| fib_dist(&w1, c) <= 0) {
                        None => viol += 1,
                        Some(g1) => {
                            if &fold(g1, &l1, t1) != gp { viol += 1; }
                            // P_1(g1) = {x : f1(x1) = g1(x1)}
                            if !p2.iter().all(|&i| f1[i % 4] == g1[i % 4]) { viol += 1; }
                        }
                    }
                }
            }
        }
        check(&format!("sec6.4: Lemma 6.8 (Good & d_(j+1) >= 1-delta => close, fold(gamma_j)=gamma', inclusion) {tested} cases, {viol} violations"), viol == 0 && tested > 0);
    }
}
