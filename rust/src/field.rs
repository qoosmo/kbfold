//! Goldilocks field F_p, p = 2^64 - 2^32 + 1, its quadratic extension F_p\[u\]/(u^2 - 7),
//! and its quartic extension F_p\[i\]/(i^4 - 7) = F_{p^2}\[v\]/(v^2 - u) with v = i, u = i^2.

use core::ops::{Add, Mul, Neg, Sub};

pub const P: u64 = 0xFFFF_FFFF_0000_0001;
const EPS: u64 = 0xFFFF_FFFF; // 2^64 mod p = 2^32 - 1

/// Multiplicative generator of F_p^*.
pub const GENERATOR: u64 = 7;
/// Largest k with 2^k | p - 1.
pub const TWO_ADICITY: u32 = 32;

pub trait Field:
    Copy
    + Send
    + Sync
    + Clone
    + PartialEq
    + Eq
    + core::fmt::Debug
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Neg<Output = Self>
{
    const ZERO: Self;
    const ONE: Self;
    fn inv(self) -> Self;
    fn from_u64(x: u64) -> Self;
    fn to_bytes(&self, out: &mut Vec<u8>);
    fn square(self) -> Self {
        self * self
    }
    fn double(self) -> Self {
        self + self
    }
    fn pow(self, mut e: u64) -> Self {
        let mut base = self;
        let mut acc = Self::ONE;
        while e > 0 {
            if e & 1 == 1 {
                acc = acc * base;
            }
            base = base.square();
            e >>= 1;
        }
        acc
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default, Hash)]
pub struct Fp(pub u64); // canonical: always < P

#[inline(always)]
fn reduce128(x: u128) -> u64 {
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let hi_hi = hi >> 32;
    let hi_lo = hi & EPS;
    // x = lo + hi_lo * 2^64 + hi_hi * 2^96,  2^64 = EPS, 2^96 = -1 (mod p)
    let (mut t0, borrow) = lo.overflowing_sub(hi_hi);
    if borrow {
        t0 = t0.wrapping_sub(EPS);
    }
    let t1 = hi_lo * EPS;
    let (mut r, carry) = t0.overflowing_add(t1);
    if carry {
        r = r.wrapping_add(EPS);
    }
    if r >= P { r - P } else { r }
}

impl Fp {
    #[inline(always)]
    pub const fn new(x: u64) -> Self {
        Fp(if x >= P { x - P } else { x })
    }
    /// Element of multiplicative order exactly 2^k (k <= 32).
    pub fn two_adic_root(k: u32) -> Self {
        assert!(k <= TWO_ADICITY);
        Fp(GENERATOR).pow((P - 1) >> k)
    }
}

impl Add for Fp {
    type Output = Fp;
    #[inline(always)]
    fn add(self, o: Fp) -> Fp {
        let (s, c) = self.0.overflowing_add(o.0);
        if c {
            Fp(s.wrapping_add(EPS)) // s + 2^64 - p
        } else if s >= P {
            Fp(s - P)
        } else {
            Fp(s)
        }
    }
}
impl Sub for Fp {
    type Output = Fp;
    #[inline(always)]
    fn sub(self, o: Fp) -> Fp {
        let (d, b) = self.0.overflowing_sub(o.0);
        if b { Fp(d.wrapping_sub(EPS)) } else { Fp(d) }
    }
}
impl Mul for Fp {
    type Output = Fp;
    #[inline(always)]
    fn mul(self, o: Fp) -> Fp {
        Fp(reduce128(self.0 as u128 * o.0 as u128))
    }
}
impl Neg for Fp {
    type Output = Fp;
    #[inline(always)]
    fn neg(self) -> Fp {
        if self.0 == 0 { self } else { Fp(P - self.0) }
    }
}
impl Field for Fp {
    const ZERO: Fp = Fp(0);
    const ONE: Fp = Fp(1);
    fn inv(self) -> Fp {
        assert!(self.0 != 0, "inverse of zero");
        self.pow(P - 2)
    }
    fn from_u64(x: u64) -> Fp {
        Fp::new(x)
    }
    fn to_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.0.to_le_bytes());
    }
}

/// Quadratic extension a + b*u with u^2 = W = 7 (7 is a non-residue mod p).
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default, Hash)]
pub struct Fp2(pub Fp, pub Fp);
const W: Fp = Fp(7);

impl From<Fp> for Fp2 {
    #[inline(always)]
    fn from(x: Fp) -> Fp2 {
        Fp2(x, Fp::ZERO)
    }
}
impl Add for Fp2 {
    type Output = Fp2;
    #[inline(always)]
    fn add(self, o: Fp2) -> Fp2 {
        Fp2(self.0 + o.0, self.1 + o.1)
    }
}
impl Sub for Fp2 {
    type Output = Fp2;
    #[inline(always)]
    fn sub(self, o: Fp2) -> Fp2 {
        Fp2(self.0 - o.0, self.1 - o.1)
    }
}
impl Mul for Fp2 {
    type Output = Fp2;
    #[inline(always)]
    fn mul(self, o: Fp2) -> Fp2 {
        let a = self.0 * o.0;
        let b = self.1 * o.1;
        let c = (self.0 + self.1) * (o.0 + o.1);
        Fp2(a + W * b, c - a - b)
    }
}
impl Mul<Fp> for Fp2 {
    type Output = Fp2;
    #[inline(always)]
    fn mul(self, o: Fp) -> Fp2 {
        Fp2(self.0 * o, self.1 * o)
    }
}
impl Neg for Fp2 {
    type Output = Fp2;
    #[inline(always)]
    fn neg(self) -> Fp2 {
        Fp2(-self.0, -self.1)
    }
}
impl Field for Fp2 {
    const ZERO: Fp2 = Fp2(Fp(0), Fp(0));
    const ONE: Fp2 = Fp2(Fp(1), Fp(0));
    fn inv(self) -> Fp2 {
        let norm = self.0 * self.0 - W * self.1 * self.1;
        let ni = norm.inv();
        Fp2(self.0 * ni, -(self.1 * ni))
    }
    fn from_u64(x: u64) -> Fp2 {
        Fp2(Fp::new(x), Fp::ZERO)
    }
    fn to_bytes(&self, out: &mut Vec<u8>) {
        self.0.to_bytes(out);
        self.1.to_bytes(out);
    }
}

/// Extension fields used as challenge fields: F_{p^e} with a fixed basis 1, i, ..., i^{e-1}.
pub trait ExtField: Field + From<Fp> + Mul<Fp, Output = Self> + Send + Sync {
    /// Degree e over F_p.
    const DEGREE: usize;
    /// Element with coordinates d_0, ..., d_{e-1} in the basis 1, i, ..., i^{e-1} (Section 8, map num).
    fn from_digits(d: &[Fp]) -> Self;
    /// Coordinates in the basis 1, i, ..., i^{e-1}.
    fn digits(&self) -> Vec<Fp>;
}

impl ExtField for Fp2 {
    const DEGREE: usize = 2;
    fn from_digits(d: &[Fp]) -> Fp2 {
        Fp2(d[0], d[1])
    }
    fn digits(&self) -> Vec<Fp> {
        vec![self.0, self.1]
    }
}

/// Quartic extension a + b v with a, b in F_{p^2} and v^2 = u (so v = i, i^4 = 7).
/// In the basis 1, i, i^2, i^3 the element is a.0 + b.0 i + a.1 i^2 + b.1 i^3.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default, Hash)]
pub struct Fp4(pub Fp2, pub Fp2);

#[inline(always)]
fn mul_by_u(x: Fp2) -> Fp2 {
    // u (x0 + x1 u) = 7 x1 + x0 u
    Fp2(W * x.1, x.0)
}

impl From<Fp> for Fp4 {
    #[inline(always)]
    fn from(x: Fp) -> Fp4 {
        Fp4(Fp2(x, Fp::ZERO), Fp2::ZERO)
    }
}
impl Add for Fp4 {
    type Output = Fp4;
    #[inline(always)]
    fn add(self, o: Fp4) -> Fp4 {
        Fp4(self.0 + o.0, self.1 + o.1)
    }
}
impl Sub for Fp4 {
    type Output = Fp4;
    #[inline(always)]
    fn sub(self, o: Fp4) -> Fp4 {
        Fp4(self.0 - o.0, self.1 - o.1)
    }
}
impl Mul for Fp4 {
    type Output = Fp4;
    #[inline(always)]
    fn mul(self, o: Fp4) -> Fp4 {
        let ac = self.0 * o.0;
        let bd = self.1 * o.1;
        let s = (self.0 + self.1) * (o.0 + o.1);
        Fp4(ac + mul_by_u(bd), s - ac - bd)
    }
}
impl Mul<Fp> for Fp4 {
    type Output = Fp4;
    #[inline(always)]
    fn mul(self, o: Fp) -> Fp4 {
        Fp4(self.0 * o, self.1 * o)
    }
}
impl Neg for Fp4 {
    type Output = Fp4;
    #[inline(always)]
    fn neg(self) -> Fp4 {
        Fp4(-self.0, -self.1)
    }
}
impl Field for Fp4 {
    const ZERO: Fp4 = Fp4(Fp2::ZERO, Fp2::ZERO);
    const ONE: Fp4 = Fp4(Fp2::ONE, Fp2::ZERO);
    fn inv(self) -> Fp4 {
        // (a + b v)^{-1} = (a - b v) / (a^2 - u b^2)
        let norm = self.0 * self.0 - mul_by_u(self.1 * self.1);
        let ni = norm.inv();
        Fp4(self.0 * ni, -(self.1 * ni))
    }
    fn from_u64(x: u64) -> Fp4 {
        Fp4::from(Fp::new(x))
    }
    fn to_bytes(&self, out: &mut Vec<u8>) {
        for d in self.digits() {
            d.to_bytes(out);
        }
    }
}
impl ExtField for Fp4 {
    const DEGREE: usize = 4;
    fn from_digits(d: &[Fp]) -> Fp4 {
        Fp4(Fp2(d[0], d[2]), Fp2(d[1], d[3]))
    }
    fn digits(&self) -> Vec<Fp> {
        vec![self.0.0, self.1.0, self.0.1, self.1.1]
    }
}

/// Batch inversion (Montgomery's trick). All inputs must be nonzero.
pub fn batch_inv<F: Field>(xs: &[F]) -> Vec<F> {
    let mut prefix = Vec::with_capacity(xs.len());
    let mut acc = F::ONE;
    for &x in xs {
        prefix.push(acc);
        acc = acc * x;
    }
    let mut inv = acc.inv();
    let mut out = vec![F::ZERO; xs.len()];
    for i in (0..xs.len()).rev() {
        out[i] = inv * prefix[i];
        inv = inv * xs[i];
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn naive_mul(a: u64, b: u64) -> u64 {
        ((a as u128 * b as u128) % P as u128) as u64
    }

    #[test]
    fn arithmetic_matches_naive() {
        let mut x: u64 = 0x1234_5678_9abc_def0;
        for _ in 0..100_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let a = x % P;
            let b = x.rotate_left(29) % P;
            assert_eq!((Fp(a) * Fp(b)).0, naive_mul(a, b));
            assert_eq!(
                (Fp(a) + Fp(b)).0,
                ((a as u128 + b as u128) % P as u128) as u64
            );
            assert_eq!(
                (Fp(a) - Fp(b)).0,
                ((a as u128 + P as u128 - b as u128) % P as u128) as u64
            );
        }
        for a in [P - 1, P - 2, EPS, 1u64 << 63, 0, 1] {
            for b in [P - 1, P - 2, EPS, 1u64 << 63, 0, 1] {
                assert_eq!((Fp(a) * Fp(b)).0, naive_mul(a, b));
            }
        }
    }

    #[test]
    fn roots_and_nonresidue() {
        let w = Fp::two_adic_root(32);
        assert_eq!(w.pow(1 << 32), Fp::ONE);
        assert_eq!(w.pow(1 << 31), -Fp::ONE);
        // 7 is a quadratic non-residue: 7^((p-1)/2) = -1
        assert_eq!(Fp(7).pow((P - 1) / 2), -Fp::ONE);
        // 7 generates F_p^*: p - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537
        assert_eq!((1u64 << 32) * 3 * 5 * 17 * 257 * 65537, P - 1);
        for l in [2u64, 3, 5, 17, 257, 65537] {
            assert_ne!(Fp(7).pow((P - 1) / l), Fp::ONE);
        }
    }

    #[test]
    fn quartic_extension() {
        // i^4 = 7 in the digit basis
        let i = Fp4::from_digits(&[Fp(0), Fp(1), Fp(0), Fp(0)]);
        assert_eq!(i * i * i * i, Fp4::from(Fp(7)));
        let mut x = 5u64;
        let mut r = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            Fp::new(x)
        };
        for _ in 0..200 {
            let a = Fp4::from_digits(&[r(), r(), r(), r()]);
            let b = Fp4::from_digits(&[r(), r(), r(), r()]);
            let c = Fp4::from_digits(&[r(), r(), r(), r()]);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!(a * a.inv(), Fp4::ONE);
            assert_eq!(Fp4::from_digits(&a.digits()), a);
            // schoolbook product in the basis 1, i, i^2, i^3 with i^4 = 7
            let (da, db) = (a.digits(), b.digits());
            let mut prod = [Fp::ZERO; 7];
            for k in 0..4 {
                for l in 0..4 {
                    prod[k + l] = prod[k + l] + da[k] * db[l];
                }
            }
            let red: Vec<Fp> = (0..4)
                .map(|k| {
                    prod[k]
                        + if k + 4 < 7 {
                            Fp(7) * prod[k + 4]
                        } else {
                            Fp::ZERO
                        }
                })
                .collect();
            assert_eq!((a * b).digits(), red);
        }
    }

    #[test]
    fn ext_inverse() {
        let a = Fp2(Fp(123456789), Fp(987654321));
        assert_eq!(a * a.inv(), Fp2::ONE);
        let v = [Fp2(Fp(3), Fp(5)), Fp2(Fp(7), Fp(0)), a];
        let iv = batch_inv(&v);
        for (x, y) in v.iter().zip(iv) {
            assert_eq!(*x * y, Fp2::ONE);
        }
    }
}
