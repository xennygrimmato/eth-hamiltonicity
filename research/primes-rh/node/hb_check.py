"""node / hb_check.py  -- adversarial numeric checks for the Heath-Brown route.

(1) HB identity for Lambda, K pieces, as an INTEGER signed count:
      Lambda(n) = sum_{j=1..K} (-1)^{j-1} C(K,j) (mu_z^{*j} * 1^{*(j-1)} * log)(n),  n <= z^K
    checked as arrays for all n <= X (exact, using integer-scaled log: we check the mu-identity
    mu(n) = sum_j (-1)^{j-1} C(K,j) (mu_z^{*j} * 1^{*(j-1)})(n), which is integral, then psi follows
    from Lambda = mu * log with the integer weight floor(B log m)).
(2) Mini-engine: enumerate witness tuples (d_1..d_j, e_1..e_j) with product in J, node weights
    W(d)=mu(d)[d<=z], W(e)=1, the log factor as floor(B*log(e_j)) (any slot carrying "log" = 1*log
    convolution), and verify sum of products == sum_{m in J} floor-weighted Lambda, round(/B) = psi(J).
    Also report the bit-size of each weighted (mu) variable vs n, the quantity the node-load rule bounds.
"""
import math, itertools, sys
import numpy as np
from math import comb

def mobius_upto(X):
    mu = np.ones(X + 1, dtype=np.int64); mu[0] = 0
    is_p = np.ones(X + 1, dtype=bool); is_p[:2] = False
    for p in range(2, X + 1):
        if is_p[p]:
            is_p[2*p::p] = False
            mu[p::p] *= -1
            if p * p <= X: mu[p*p::p*p] = 0
    return mu

def dconv(a, b, X):
    out = np.zeros(X + 1, dtype=np.int64)
    nz = np.nonzero(a[1:])[0] + 1
    for d in nz:
        L = X // d
        out[d::d][:L] += a[d] * b[1:L + 1]
    return out

def check_identity(X, K):
    mu = mobius_upto(X)
    z = math.ceil(X ** (1.0 / K)) + 1          # z^K > X
    muz = mu.copy(); muz[z + 1:] = 0
    one = np.zeros(X + 1, dtype=np.int64); one[1:] = 1
    delta = np.zeros(X + 1, dtype=np.int64); delta[1] = 1
    total = np.zeros(X + 1, dtype=np.int64)
    pw_mu = delta.copy(); pw_one = delta.copy()
    for j in range(1, K + 1):
        pw_mu = dconv(pw_mu, muz, X)
        if j >= 2: pw_one = dconv(pw_one, one, X)
        total += (-1) ** (j - 1) * comb(K, j) * dconv(pw_mu, pw_one, X)
    bad = np.nonzero(total[1:] != mu[1:])[0]
    return z, len(bad)

def lam(m):
    if m < 2: return 0.0
    for p in range(2, int(m ** 0.5) + 1):
        if m % p == 0:
            while m % p == 0: m //= p
            return math.log(p) if m == 1 else 0.0
    return math.log(m)

def mini_engine(J, K):
    """Enumerate HB witness tuples for Lambda = sum_j c_j mu_z^{*j} * 1^{*(j-1)} * L,
    L(e)=floor(B log e) on the last slot; returns engine value and psi."""
    a, b = J
    X = b
    mu = mobius_upto(X)
    z = math.ceil(X ** (1.0 / K)) + 1
    B = X * X                                    # rounding error <= sum_J tau-ish < B
    LOG = [0] + [math.floor(B * math.log(e)) for e in range(1, X + 1)]
    val = 0; ntuples = 0
    def rec(prod, slots, w):
        # slots: list of kinds remaining ('mu','one','log')
        nonlocal val, ntuples
        if not slots:
            if a <= prod <= b:
                val += w; ntuples += 1
            return
        kind = slots[0]
        lim = b // prod
        if kind == 'mu': lim = min(lim, z)
        for d in range(1, lim + 1):
            if kind == 'mu':
                if mu[d] == 0: continue
                rec(prod * d, slots[1:], w * int(mu[d]))
            elif kind == 'one':
                rec(prod * d, slots[1:], w)
            else:
                if len(slots) == 1:   # last slot: must land in J
                    lo = max(1, -(-a // prod)); hi = b // prod
                    for e in range(lo, hi + 1):
                        val += w * LOG[e]; ntuples += 1
                    return
    for j in range(1, K + 1):
        c = (-1) ** (j - 1) * comb(K, j)
        slots = ['mu'] * j + ['one'] * (j - 1) + ['log']
        before = val
        val = 0
        rec(1, slots, 1)
        val = before + c * val
    psi = sum(lam(m) for m in range(a, b + 1))
    return val, B, psi, ntuples, z

if __name__ == '__main__':
    for X, K in [(10**5, 2), (10**5, 3), (10**5, 4), (10**6, 2), (10**6, 3)]:
        z, nbad = check_identity(X, K)
        print(f"[N] mu-identity HB K={K} on n<={X}: z={z} (mu-variable bits {z.bit_length()} of n={X.bit_length()}), mismatches={nbad}")
    for J, K in [((1000, 1100), 2), ((1000, 1100), 3), ((5000, 5060), 3), ((20000, 20030), 4)]:
        v, B, psi, nt, z = mini_engine(J, K)
        print(f"[N] mini-engine J={J} K={K}: tuples={nt}, value/B={v/B:.9f}, round={round(v/B*1e6)/1e6}, psi={psi:.9f}, |diff|={abs(v/B-psi):.2e}, z={z}")
