"""node / cost_model.py -- the engine's certified exponent for a Heath-Brown network.

Cost theorem (GroupingExplicit + Theorem A(b), research/anthropic-api.md 2.1-2.2):
  T <= (K^g + 2^{e_K*(U + 2*zeta*g*P)} * poly * 2^{2gP/K} * tau) * poly,
  case (i):  g = 3K^8, zeta = 1/(2K)           -> extra exponent e*3K^7 P + 6K^7 P
  case (ii): K | g, g >= K ln(2gK)/(2 zeta^2), pairwise cut <= P/g, zeta <= 1
             -> extra exponent >= e*K ln(2gK) P/zeta + 2gP/K
HB with h pieces: mu-variables of n/h bits must sit inside one node -> P >= n/h;
product tree over 2h-1 factors with leaves absorbed into nodes: U >= n log2(n/P) (tree model, Lean cost_ge_entropy).
We minimise the exponent/n over K (engine level), t = P/n, with e_K = c/sqrt(log2 K) for c in {60 (theorem, x0=18), 1, 0.1}.
"""
import math
def best(c, Ks=range(1, 200)):
    out = None
    for lk in Ks:                     # K = 2^lk
        K = 2.0 ** lk
        e = c / math.sqrt(lk)
        for i in range(1, 400):
            t = 2.0 ** (-i / 4)       # P/n
            U = max(1.0, math.log2(1 / t))
            # case (ii) with zeta=1, g = K*ln(2gK)/2 ~ K*ln K (cheapest)
            g = max(K, K * math.log(2 * K * K) / 2)
            E2 = e * (U + 2 * g * t) + 2 * g * t / K
            E1 = e * (U + 3 * 2.0 ** min(7 * lk, 1000) * t) + 6 * 2.0 ** min(7 * lk, 1000) * t
            E = min(E1, E2)
            if out is None or E < out[0]:
                out = (E, lk, t, e)
    return out
for c in (60, 1, 0.1, 0.01):
    E, lk, t, e = best(c)
    print(f"[N] e_K = {c}/sqrt(log2 K): min exponent/n = {E:.3f} at log2 K = {lk}, P/n = {t:.2e}, e_K = {e:.3f}; "
          f"lower bound e_K*log2 K = {e*lk:.3f}; beats sqrt(N)? {E < 0.5}")
