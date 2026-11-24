#!/usr/bin/env python3
"""x1: faithful small-N simulation of Ni's Cauchy-kernel pipeline (no engine; sums brute-forced),
extended to twin primes, Goldbach counts, Sophie Germain pairs and the Mertens function.

All approximate factors are EXACT Gaussian rationals with denominator 2^(p+t), built exactly as in
Ni's (2): kernel parts are the integers floor(2^t 2^p q|X|/D), coefficients are p-bit roundings of
h(z_l)(z_l - c)/M. Every sum below is computed in exact integer arithmetic; the only place rounding
happens is the final  floor(Re S~ + 1/2).

Distributivity (an exact identity on the approximate values) is used to factor the tuple sum:
  sum_{n} sum_{dm=n} sum_{x,x'} Fe(x/d) Fe(x'/n) Flog(m) Finv(n)
    = sum_n A(n) Finv(n) sum_{dm=n} A(d) Flog(m),   A(d) = sum_{(x,d)=1} Fe(x/d).
`tuple_check` verifies bit-for-bit equality with the literal (n,d,m,x,x') loop at tiny N.
"""
import math, sys, time
import mpmath as mp
from math import gcd

C_NUM, C_DEN = 3, 2      # centre c = 3/2
R_NUM, R_DEN = 3, 4      # radius r = 3/4
LOG2_76 = math.log2(7 / 6)

# ---------- Gaussian integers as (re, im) python ints ----------
def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
def gadd(a, b):
    return (a[0] + b[0], a[1] + b[1])

# ---------- parameter choice from an error target 2^-D per factor ----------
def H_bounds(beta):
    """sup|h| on the disc |z-3/2| <= 7/8 for the three functions (beta bounds the dyadic scale j)."""
    He = math.exp(2 * math.pi * 7 / 8)                    # |e(z-1)| <= e^{2 pi Im z}
    Hlog = beta * math.log(2) + math.log(19 / 8) + math.pi  # |j log2 + log z|, crude
    Hinv = 1 / (math.log(2) + math.log(5 / 8))            # Re h_j >= log2 + log(5/8) = 0.223
    return max(He, Hlog, Hinv)

def params_for(D, beta):
    """M, p, t such that each factor has error <= 2^-D (see notebook section 2)."""
    H = H_bounds(beta)
    M = math.ceil((D + math.log2(3 * 49 * H)) / LOG2_76)
    p = math.ceil(D + math.log2(3 * (18 * H + 6 * M)))
    t = math.ceil(D + math.log2(3 * 1.2 * H))
    return M, p, t

# ---------- the kernel machine ----------
class Pipeline:
    def __init__(self, M, p, t, jmax):
        self.M, self.p, self.t = M, p, t
        mp.mp.prec = p + t + 80
        c = mp.mpf(C_NUM) / C_DEN
        r = mp.mpf(R_NUM) / R_DEN
        self.U, self.V = [], []
        ze = []
        for l in range(M):
            z = c + r * mp.expjpi(mp.mpf(2 * l) / M)
            ze.append(z)
            self.U.append(int(mp.nint(z.real * 2 ** p)))
            self.V.append(int(mp.nint(z.imag * 2 ** p)))
        def rnd(w):
            return (int(mp.nint(w.real * 2 ** p)), int(mp.nint(w.imag * 2 ** p)))
        self.ce = [rnd(mp.expjpi(2 * (z - 1)) * (z - c) / M) for z in ze]       # e(z-1)
        ln2 = mp.log(2)
        self.clog = {j: [rnd((j * ln2 + mp.log(z)) * (z - c) / M) for z in ze] for j in range(0, jmax + 1)}
        self.cinv = {j: [rnd((z - c) / (j * ln2 + mp.log(z)) / M) for z in ze] for j in range(1, jmax + 1)}
        self.S = 2 ** (p + t)                                                       # denominator

    def kparts(self, l, a, q):
        """Signed truncated kernel parts at node l, y = a/q:  value = (kr + i ki)/2^t (Ni eq. (2))."""
        X = self.U[l] * q - (a << self.p)
        Y = self.V[l] * q
        Dd = X * X + Y * Y
        num = q << (self.t + self.p)
        kr = (num * abs(X)) // Dd
        ki = (num * abs(Y)) // Dd
        return (kr if X >= 0 else -kr), (-ki if Y >= 0 else ki)

    def approx(self, coefs, a, q):
        """sum_l c_l K_l(a/q) as Gaussian integer over 2^(p+t)."""
        re = im = 0
        for l in range(self.M):
            kr, ki = self.kparts(l, a, q)
            cr, ci = coefs[l]
            re += cr * kr - ci * ki
            im += cr * ki + ci * kr
        return (re, im)

    def Fe(self, x, d):            # e(x/d), y = 1 + x/d in [1,2)
        return self.approx(self.ce, d + x, d)
    def Flog(self, m):             # log m, m >= 1
        j = m.bit_length() - 1
        return self.approx(self.clog[j], m, 1 << j)
    def Finv(self, n):             # 1/log n, n >= 2
        j = n.bit_length() - 1
        return self.approx(self.cinv[j], n, 1 << j)

    def A(self, d):
        """sum over 0<=x<d, (x,d)=1 of Fe(x/d)  (= approx of mu(d)); d=1 treated exactly (boundary case)."""
        if d == 1:
            return (self.S, 0)
        acc = [[0, 0] for _ in range(self.M)]
        p, t = self.p, self.t
        for x in range(1, d):
            if gcd(x, d) != 1:
                continue
            a = d + x
            for l in range(self.M):
                kr, ki = self.kparts(l, a, d)
                acc[l][0] += kr; acc[l][1] += ki
        re = im = 0
        for l in range(self.M):
            cr, ci = self.ce[l]; kr, ki = acc[l]
            re += cr * kr - ci * ki
            im += cr * ki + ci * kr
        return (re, im)

# ---------- exact reference values ----------
def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = 0
    if n >= 1: s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i::i] = bytearray(len(s[i * i::i]))
    return s
def mobius(n):
    mu = [1] * (n + 1); mu[0] = 0
    pr = sieve(n)
    for q in range(2, n + 1):
        if pr[q]:
            for k in range(q, n + 1, q): mu[k] = -mu[k]
            for k in range(q * q, n + 1, q * q): mu[k] = 0
    return mu

# ---------- literal tuple loop (tiny N only) ----------
def tuple_sum_pi(P, N):
    """S~ = sum over (n,d,m,x,x') of -Fe(x/d)Fe(x'/n)Flog(m)Finv(n), literally, no factoring."""
    tot = (0, 0)
    for n in range(2, N + 1):
        fi = P.Finv(n)
        for d in range(1, n + 1):
            if n % d: continue
            m = n // d
            if m == 1: continue                      # log 1 = 0 exactly (boundary case)
            fl = P.Flog(m)
            xs = [0] if d == 1 else [x for x in range(1, d) if gcd(x, d) == 1]
            for x in xs:
                fe1 = (P.S, 0) if d == 1 else P.Fe(x, d)
                for xp in range(1, n):
                    if gcd(xp, n) != 1: continue
                    v = gmul(gmul(gmul(fe1, P.Fe(xp, n)), fl), fi)
                    tot = (tot[0] - v[0], tot[1] - v[1])
    return tot  # denominator S^4
