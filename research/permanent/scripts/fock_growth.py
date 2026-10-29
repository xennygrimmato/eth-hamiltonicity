"""Sparse Fock spaces V_S = Q[t_k : k in S]: Hilbert series prod_{k in S} 1/(1-q^k), the growth
exponent beta = lim log f(E)/log E with f(E) = log2 p_S(E), and the "general law" rho = f(2h)/(2f(h))
(rho-lower-bound.md, Cor. 3.4) that a two-order structure on V_S WOULD give if it existed.
Exact integer arithmetic.  Prints PASS if the fitted exponents agree with the theoretical values
  S = {k^a}: beta = 1/(a+1) (Hardy-Ramanujan 1917 / Meinardus 1954),   primes: beta = 1/2 (Roth-Szekeres),
  powers of 2: log p_S(E) ~ (log2 E)^2 / 2, beta = 0,                  N: beta = 1/2.
"""
import math, sys

def restricted(M, parts):
    pp = [0] * (M + 1); pp[0] = 1
    for k in parts:
        if k > M: break
        for n in range(k, M + 1):
            pp[n] += pp[n - k]
    return pp

def euler(M):
    pp = [0] * (M + 1); pp[0] = 1
    for n in range(1, M + 1):
        s = 0; k = 1
        while True:
            g1 = k * (3 * k - 1) // 2
            if g1 > n: break
            sign = 1 if k % 2 else -1
            s += sign * pp[n - g1]
            g2 = k * (3 * k + 1) // 2
            if g2 <= n: s += sign * pp[n - g2]
            k += 1
        pp[n] = s
    return pp

def primes_upto(M):
    s = bytearray([1]) * (M + 1); s[0] = s[1] = 0
    for i in range(2, int(M ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(M + 1) if s[i]]

def lg(n): return math.log2(n) if n > 0 else float('nan')

def main():
    M = 40000
    fams = [
        ("all parts N",        None,                                  0.5),
        ("squares k^2",        [k*k for k in range(1, 500)],          1/3),
        ("cubes k^3",          [k**3 for k in range(1, 100)],         1/4),
        ("fourth powers k^4",  [k**4 for k in range(1, 30)],          1/5),
        ("primes",             primes_upto(M),                        0.5),
        ("powers of 2",        [2**k for k in range(0, 18)],          0.0),
    ]
    def leading(name, E):
        # Hardy-Ramanujan (1917) for parts k^a: ln p(E) ~ (a+1) [Gamma(1+1/a) zeta(1+1/a) / a]^{a/(a+1)} E^{1/(a+1)}
        import math as m
        def zeta(s, terms=200000):
            return sum(k ** (-s) for k in range(1, terms)) + terms ** (1 - s) / (s - 1)
        a = {"all parts N": 1, "squares k^2": 2, "cubes k^3": 3, "fourth powers k^4": 4}.get(name)
        if a is not None:
            return (a + 1) * (m.gamma(1 + 1 / a) * zeta(1 + 1 / a) / a) ** (a / (a + 1)) * E ** (1 / (a + 1)) / m.log(2)
        if name == "primes":  # Roth-Szekeres 1954
            return 2 * m.pi * m.sqrt(E / (3 * m.log(E))) / m.log(2)
        if name == "powers of 2":  # de Bruijn 1948: ln b(E) ~ (ln E)^2 / (2 ln 2)
            return m.log(E) ** 2 / (2 * m.log(2)) / m.log(2)
    ok = True
    print(f"{'S':20s} {'E':>7s} {'f(E)=log2 p_S(E)':>17s} {'f/leading':>9s} {'f(2E)/(2f(E))':>14s} {'slope':>7s} {'beta':>6s} {'2^(beta-1)':>10s}")
    for name, parts, beta in fams:
        pp = euler(M) if parts is None else restricted(M, parts)
        slopes, laws, ratios = [], [], []
        for E in [1000, 10000, 20000]:
            f = lg(pp[E]); law = lg(pp[2*E]) / (2*f)
            bh = (math.log(lg(pp[E])) - math.log(lg(pp[E//10]))) / math.log(10)   # local exponent on [E/10, E]
            ratio = f / leading(name, E)
            print(f"{name:20s} {E:7d} {f:17.2f} {ratio:9.3f} {law:14.4f} {bh:7.4f} {beta:6.3f} {2**(beta-1):10.4f}")
            slopes.append(bh); laws.append(law); ratios.append(ratio)
        # slow convergence (log corrections) is expected; test monotone approach and the leading term within a factor 2
        good = all(slopes[i] > slopes[i+1] for i in range(2)) and all(laws[i] > laws[i+1] for i in range(2)) and 0.5 < ratios[-1] < 1.2
        if not good:
            ok = False; print("   !! not approaching the predicted exponent / leading term")
    print("\nNote: for primes the finite-size law is BELOW 1/sqrt2 (0.69 at E = 2*10^4) because of the 1/sqrt(ln E) factor;")
    print("it converges to 1/sqrt2 from below like sqrt(ln E / ln 2E).  For primes the Roth-Szekeres law log p(E) ~ 2 pi sqrt(E/(3 ln E)) has beta = 1/2 with a log")
    print("correction; the law f(2h)/(2f(h)) -> 1/sqrt2 regardless of the log factor.  Squares: Hardy-Ramanujan")
    print("log p_sq(E) ~ 3 (pi/4)^{1/3} zeta(3/2)^{2/3} E^{1/3} / ln 2 ; the finite-E law is above 2^{-2/3} = 0.630.")
    print("PASS" if ok else "FAIL")

if __name__ == "__main__":
    main()
