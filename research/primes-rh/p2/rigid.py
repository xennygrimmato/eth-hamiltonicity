"""Escape (B) test: the binomial / Legendre rigid identity with chi = (./3).
Identity (unique factorisation + complete multiplicativity of chi):
   sum_{p != 3, chi(p) = -1} v_p(C(2N,N))  ==  [chi(C(2N,N)/3^{v_3}) = -1]   (mod 2)
v_p(C(2N,N)) = 1 on (N,2N], so the 'window' part W_N = #{p in (N,2N]: p = 2 mod 3} mod 2 is forced only if the
contamination K_N (primes p <= N with odd v_p, p = 2 mod 3) is provably even. Measure how often W_N = T_N."""
import numpy as np
from math import comb
X = 4000
isp = np.ones(2*X + 1, bool); isp[:2] = False
for i in range(2, int((2*X)**.5) + 1):
    if isp[i]: isp[i*i::i] = False
P = [p for p in range(2, 2*X + 1) if isp[p]]
def vp_binom(N, p):  # Kummer / Legendre
    s, q = 0, p
    while q <= 2*N: s += (2*N)//q - 2*(N//q); q *= p
    return s
agree = Wodd = Todd = Kodd = tot = 0
for N in range(10, X + 1):
    c = comb(2*N, N)
    while c % 3 == 0: c //= 3
    T = int(c % 3 == 2)
    win = sum(1 for p in P if N < p <= 2*N and p % 3 == 2) % 2
    K = sum(vp_binom(N, p) for p in P if p <= N and p % 3 == 2) % 2
    assert (win + K) % 2 == T, N    # the rigid identity
    tot += 1; agree += win == T; Wodd += win; Todd += T; Kodd += K
print(f"N in [10,{X}]: identity holds for all; P(window odd)={Wodd/tot:.3f}, P(T odd)={Todd/tot:.3f}, "
      f"P(contamination odd)={Kodd/tot:.3f}, P(window parity = rigid bit T)={agree/tot:.3f}")
# where does the contamination live? fraction of contaminating primes (odd v_p, p=2 mod 3, p<=N) by scale, N=4000
N = X
cont = [p for p in P if p <= N and p % 3 == 2 and vp_binom(N, p) % 2]
for lo, hi in [(N/2, N), (N/4, N/2), (N/16, N/4), (np.sqrt(2*N), N/16), (0, np.sqrt(2*N))]:
    print(f"   contaminating primes in ({lo:.0f},{hi:.0f}]: {sum(1 for p in cont if lo < p <= hi)}")
