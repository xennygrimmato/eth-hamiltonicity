# 2-adic Smith invariants of the cross-group block of OpenAI D.1's Cauchy kernel
# W_xy(T) = C(T) / (C'(0) (T - (y-x))),  C(T) = prod_{t in S}(T-t),  S = {-L..L-1}, L = 2^a.
# At a node t with v_2(t)=i, T = t + alpha*zeta, alpha = 2^(a+1): rows x, cols y in the SAME
# group-coordinate-i class are "crossing" (bit_i(x) == bit_i(y)); their entries should have
# valuation >= a+1-i and the invariant factors should come in ~2^i copies per weight level
# (D.1 eq. tensor-mode-multiplicity: 6M/D variables of each weight, D = L/2^i), weights linear.
from fractions import Fraction
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form
import sys

def v2(n):
    n = abs(int(n)); 
    if n == 0: return 10**9
    c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c

def kernel(L, T):
    S = list(range(-L, L))
    def C(x):
        p = Fraction(1)
        for s in S: p *= (x - s)
        return p
    # C'(0) = prod_{s != 0} (0 - s)
    Cp0 = Fraction(1)
    for s in S:
        if s != 0: Cp0 *= (0 - s)
    W = [[None]*L for _ in range(L)]
    for x in range(L):
        for y in range(L):
            d = y - x   # in S
            num = Fraction(1)
            for s in S:
                if s != d: num *= (T - s)
            W[x][y] = num / Cp0
    return W

def smith_vals(M):
    # M: list of lists of Fractions. Scale by 2^k * odd to make integral, Smith over Z, return valuations (minus scaling).
    from math import lcm
    den = 1
    for row in M:
        for e in row: den = lcm(den, e.denominator)
    k = v2(den)
    # multiply by den (odd part of den does not change 2-adic valuations)
    Mi = Matrix([[int(e * den) for e in row] for row in M])
    snf = smith_normal_form(Mi, domain=ZZ)
    vals = []
    for i in range(min(snf.shape)):
        d = snf[i, i]
        vals.append(v2(d) - k if d != 0 else None)
    return sorted([v for v in vals if v is not None]), sum(1 for v in vals if v is None)

a = int(sys.argv[1]) if len(sys.argv) > 1 else 3
L = 2**a; alpha = 2**(a+1)
print(f"L={L} a={a} alpha={alpha} S=[-{L},{L-1}]")
for i in range(a):
    t = 2**i   # node of valuation i
    for zeta in (1, 3):
        T = Fraction(t + alpha*zeta)
        W = kernel(L, T)
        # sanity: W(t) should be the shift permutation y - x = t (check at zeta=0)
        # crossing block: rows x with bit_i(x)=0, cols y with bit_i(y)=0
        rows = [x for x in range(L) if (x >> i) & 1 == 0]
        cols = [y for y in range(L) if (y >> i) & 1 == 0]
        B = [[W[x][y] for y in cols] for x in rows]
        vals, zeros = smith_vals(B)
        minv = min(v2(e.numerator) - v2(e.denominator) for row in B for e in row if e != 0)
        print(f" node t={t} (i={i}), zeta={zeta}: cross block {len(rows)}x{len(cols)}, min entry val {minv} (D.1 bound a+1-i={a+1-i}); Smith valuations {vals}; zero invariants {zeros}")
# check W(t) is the shift permutation
W0 = kernel(L, Fraction(1))
ok = all((W0[x][y] == (1 if y - x == 1 else 0)) for x in range(L) for y in range(L))
print("W(1) == shift-by-1 permutation on real ports:", ok)
