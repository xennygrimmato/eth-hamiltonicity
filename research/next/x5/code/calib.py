"""Calibration: the crossing exponent of Prop. B.2 from exact counts.
Symbols of energy 2n <-> partitions of n (Frobenius), so P(E) = sum_{n<=E/2} p(n),
and the class of size k, energy 2n has q^{k^2}/(q)_k^2 count (Durfee square k).
rho(E) = max_N [ln((N+1)P(N)) + ln((Th-N+1)P(Th-N))] / (2 ln(|S1||S2|)),  e1=e2=E, Th = 4E,
|S| = largest Durfee class of energy E.  Paper (asymptotic): rho -> 1/sqrt 2.
Also the 'flattening-forced' quantity ln P(Th)/ln(|S1||S2|) (>= 1 needed)."""
import math, sys

def partitions(nmax):
    p = [1] + [0] * nmax
    for n in range(1, nmax + 1):
        s, k = 0, 1
        while True:
            for g in (k * (3 * k - 1) // 2, k * (3 * k + 1) // 2):
                if g > n: break
                s += (-1) ** (k + 1) * p[n - g]
            if k * (3 * k - 1) // 2 > n: break
            k += 1
        p[n] = s
    return p

def durfee_max(n):
    """max_k #partitions of n with Durfee square k"""
    best = 0
    k = 1
    while k * k <= n:
        m = n - k * k
        # coefficients of 1/(q)_k up to m
        c = [1] + [0] * m
        for part in range(1, k + 1):
            for i in range(part, m + 1):
                c[i] += c[i - part]
        best = max(best, sum(c[i] * c[m - i] for i in range(m + 1)))
        k += 1
    return best

if __name__ == '__main__':
    Es = [int(x) for x in sys.argv[1:]] or [20, 50, 100, 200, 500, 1000, 2000]
    nmax = 2 * max(Es) + 2
    p = partitions(nmax)
    cum = [0] * (nmax + 1); s = 0
    for i in range(nmax + 1):
        s += p[i]; cum[i] = s
    P = lambda E: cum[E // 2]
    print(" E   |S|digits  rho_count  rho_noPoly   lnP(E)/sqrtE  kappa=pi/sqrt3=%.4f" % (math.pi / math.sqrt(3)))
    for E in Es:
        S = durfee_max(E // 2)
        L = 2 * math.log(S) * 2  # 2 ln(|S1||S2|)
        Th = 4 * E
        best = max(math.log((N + 1) * P(N)) + math.log((Th - N + 1) * P(Th - N)) for N in range(0, Th + 1, 2))
        best0 = max(math.log(P(N)) + math.log(P(Th - N)) for N in range(0, Th + 1, 2))
        # idealised: |S| ~ P(E)
        print(f"{E:5d} {len(str(S)):5d}  {best/L:.4f}   {best0/(4*math.log(P(E))):.4f}    {math.log(P(E))/math.sqrt(E):.4f}")
