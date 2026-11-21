# chebq.py -- Chebyshev/Selberg certificate prime finder, written in QUERY form (notebook s7).
# Goal (weak, Polymath4 Problem 1): find a prime p > u.  Only primitives used:
#   (i)  Q_k(J; m, lo, hi) = #{(d,q): lo<=d<=hi, m|d, d^k*q in J}   (divisor-range count with congruence;
#        a unique-witness system n = (m t)^k q -> one engine count; here SIMULATED by a floor sum)
#   (ii) factoring one integer n <= 2x (engine / sympy here).
# Sieve work outside the oracle: mu up to R only (R = u^rho), primes up to R.
# F(J) = L1^2 * sum_{n in J} floor(log2 n) - sum_{n in J} w(n),  w(n) >= L1^2 * log2(u-smooth part of n),
# w(n) = sum_{p^k|n, p<=R} c(p) L1^2 + sum_{k>=1} sum_{R<d<=u, d^k|n} Lam_R(d)^2 c(d),  c(d)=ceil(log2 d),
# Lam_R(d) = sum_{e|d, e<=R} mu(e) L(e) (integer-scaled log(R/e)); Lam_R(p^j)=L1 for p>R.
# F(n)>0 => P+(n)>u.  F additive -> bisection from J=[x,2x).
import math, sys, sympy
from collections import defaultdict

def run(u, rho, A, C=64, verify=True):
    R = max(2, int(round(u**rho))); x = int(round(u**A)); J0 = (x, 2*x)        # J = [lo, hi)
    mu = [0]+[int(sympy.mobius(e)) for e in range(1, R+1)]
    L = [0]+[int(round(C*math.log(R/e))) for e in range(1, R+1)]; L1 = L[1]
    a = {e: mu[e]*L[e] for e in range(1, R+1) if mu[e] and L[e]}
    b = defaultdict(int)                                    # b(m) = sum_{lcm(e1,e2)=m} a(e1)a(e2)
    for e1, v1 in a.items():
        for e2, v2 in a.items():
            b[e1*e2//math.gcd(e1, e2)] += v1*v2
    b = {m: v for m, v in b.items() if v}
    blocks = []                                             # (lo,hi,c) with c=ceil(log2 d) on [lo,hi]
    j = 1
    while 2**(j-1)+1 <= u:
        lo = max(R+1, 2**(j-1)+1); hi = min(u, 2**j)
        if lo <= hi: blocks.append((lo, hi, j))
        j += 1
    kmax = max(1, int(math.log(2*x)/math.log(R+1))+1)
    smallp = list(sympy.primerange(2, R+1))
    stats = {'Q': 0, 'F': 0}
    def cnt(J, q):                                          # #{n in J: q|n}
        return (J[1]-1)//q - (J[0]-1)//q
    def Q(J, m, lo, hi, k):                                 # ORACLE (simulated)
        stats['Q'] += 1
        s = 0
        t0 = -(-lo//m)
        for t in range(t0, hi//m+1):
            dk = (m*t)**k
            if dk >= J[1]: break
            s += cnt(J, dk)
        return s
    def sumfloorlog(J):
        s = 0; lo, hi = J
        while lo < hi:
            e = lo.bit_length()-1; top = min(hi, 1 << (e+1)); s += e*(top-lo); lo = top
        return s
    def F(J):
        stats['F'] += 1
        tot = L1*L1*sumfloorlog(J)
        for p in smallp:
            q = p
            while q < J[1]:
                tot -= math.ceil(math.log2(p))*L1*L1*cnt(J, q); q *= p
        for k in range(1, kmax+1):
            for (lo, hi, c) in blocks:
                if lo**k >= J[1]: continue
                for m, v in b.items():
                    if m > hi: continue
                    tot -= c*v*Q(J, m, lo, hi, k)
        return tot
    Ftop = F(J0)
    res = dict(u=u, R=R, x=x, A=A, rho=rho, nb=len(b), Ftop_per_n=Ftop/(x*L1*L1),
               pred=(A - (1+rho*rho)/(2*rho))*math.log2(u))
    if Ftop <= 0:
        res['found'] = None; res.update(stats); return res
    lo, hi = J0; Flo = Ftop
    while hi-lo > 1:
        mid = (lo+hi)//2; f = F((lo, mid))
        if f > 0: hi = mid
        else: lo = mid                                      # then F([mid,hi)) = Flo - f > 0
    n = lo
    fac = sympy.factorint(n); p = max(fac)
    res.update(stats); res.update(n=n, p=p, ok=p > u and sympy.isprime(p))
    if verify:  # brute-force check of the pointwise certificate at n
        sm = 1
        for q, e in fac.items():
            if q <= u: sm *= q**e
        res['smooth_part<n'] = sm < n
    return res

if __name__ == '__main__':
    for arg in sys.argv[1:]:
        u, rho, A = arg.split(','); r = run(int(u), float(rho), float(A))
        print(r, flush=True)
