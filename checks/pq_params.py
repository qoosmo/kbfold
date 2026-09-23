# Concrete evaluation of the CDHZ bound (Thm 6.10 + Thm 8.3 + Thm 11.3) for Pi_eval, all masses <= t.
from fractions import Fraction as Fr
from math import log2, ceil
p = 2**64 - 2**32 + 1
F = p**4                  # quartic extension
t = 2**64                 # query bound
sigma = 256               # Merkle hash output length
rho, delta = Fr(1,4), Fr(3,8)
m_max = 32                # M = 2^m <= 2^32
M = 2**m_max
kappa = 248
b = 320                   # bits per field challenge
ell = 30                  # folding rounds (<= n <= 30)
k = ell + 1
lmax = M//2               # longest string (symbols over Sigma = F^2)
qV = 2**36; qC = 2**36; qs = 2**30
rmin = min(b, kappa*m_max)
M1 = M//2
eps_fold = Fr(M1+2)*(Fr(1,F)+Fr(1,2**b))
eps_q = (1-delta)**kappa
kR = max(eps_fold, eps_q)
A = 4*(80*(t+k+1)*(t+k)*kR + Fr((t+k+1)*k, 2**rmin))
B = 4*Fr(8*1*lmax, 2**sigma)
C = 8*(Fr(160*t*(2*t+1)**2, 2**sigma) + Fr(16*qs*ceil(log2(lmax)), 2**sigma))
T1 = t+1+qV+k+qC
D = 4*Fr(240*(t+1)*T1**2, 2**sigma)
E = 2*qV**2*Fr(240*(t+2+k+qV), 2**sigma)
tot = A+B+C+D+E
L = lambda x: log2(x.numerator)-log2(x.denominator)
for name,x in [("eps_fold",eps_fold),("(5/8)^kappa",eps_q),("A (sr term)",A),("B",B),("C (offline)",C),("D (online)",D),("E (com)",E),("total",tot)]:
    print(f"{name:14s} 2^{L(x):.2f}")
print("min kappa with (5/8)^kappa <= 2^-168:", ceil(168/log2(8/5)))
print("log2 |F| =", log2(F))
