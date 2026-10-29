"""modp_affine.py -- per mod p as a dense bilinear exponential sum with non-affine unary weights (perm-mod-p.md section 4)
(a) p = 2: per = X mod 2 with X = 2^{-n} sum_{s,t in F_2^n} (-1)^{n-|s|+|t|+t^T A s}: a quadratic Gauss sum (all weights affine)
(b) p odd: X = p^{-n} sum_{s in {0,1}^n, t,y in Z_p^n} (-1)^{n-|s|} prod_i y_i * zeta^{t^T A s - t.y},  X = per mod p
    rewritten as p^{-n} sum_c zeta^c * N_c with N_c = signed weighted count of (s,t,y) with t^T A s - t.y = c mod p:
    one dense bilinear congruence + unary weights.  Evaluated exactly in Z[zeta] via cyclotomic reduction.
(c) |hhat(t)| is constant on its support for p = 2 (affine type) and non-constant for odd p (not affine type)
"""
import itertools, math, random, cmath
random.seed(11)
def per(A):
    n = len(A); tot = 0
    for mask in range(1 << n):
        prod = 1
        for i in range(n):
            prod *= sum(A[i][j] for j in range(n) if mask >> j & 1)
        tot += (-1) ** (n - bin(mask).count('1')) * prod
    return tot
ok = True
def check(name, c):
    global ok
    ok &= c; print(("PASS " if c else "FAIL ") + name)

for n in range(2, 8):
    A = [[random.randint(0, 1) for _ in range(n)] for _ in range(n)]
    G = 0
    for s in itertools.product((0, 1), repeat=n):
        As = [sum(A[i][j] * s[j] for j in range(n)) % 2 for i in range(n)]
        for t in itertools.product((0, 1), repeat=n):
            G += (-1) ** ((n - sum(s) + sum(t) + sum(t[i] * As[i] for i in range(n))) % 2)
    X = G // 2 ** n
    check(f"(a) n={n}: 2^n | G ({G % 2**n == 0}), X = {X}, X = per mod 2 ({(X - per(A)) % 2 == 0})", G % 2**n == 0 and (X - per(A)) % 2 == 0)

for (n, p) in [(3, 3), (4, 3), (3, 5), (5, 3)]:
    A = [[random.randint(0, 1) for _ in range(n)] for _ in range(n)]
    Nc = [0] * p      # N_c = sum over (s,t,y) with Q = c of sign * prod y_i
    for s in itertools.product((0, 1), repeat=n):
        sg = (-1) ** (n - sum(s))
        As = [sum(A[i][j] * s[j] for j in range(n)) for i in range(n)]
        # factorises over i, but we enumerate (t_i, y_i) jointly to exhibit the single congruence
        for ty in itertools.product(range(p), repeat=2 * n):
            t, y = ty[:n], ty[n:]
            w = math.prod(y)
            if w == 0: continue
            c = sum(t[i] * (As[i] - y[i]) for i in range(n)) % p
            Nc[c] += sg * w
    # p^{-n} sum_c zeta^c N_c must be the rational integer X: sum_c zeta^c N_c = p^n X means N_c - N_0 ... use: in Z[zeta],
    # sum_c N_c zeta^c is rational iff N_1 = ... = N_{p-1}; its value is N_0 - N_1.
    rational = all(Nc[c] == Nc[1] for c in range(1, p))
    val = Nc[0] - Nc[1]
    X = val // p ** n
    Xd = sum((-1) ** (n - sum(s)) * math.prod(sum(A[i][j] * s[j] for j in range(n)) % p for i in range(n)) for s in itertools.product((0, 1), repeat=n))
    check(f"(b) n={n} p={p}: sum_c N_c zeta^c rational ({rational}), = p^n * X ({val == p**n * Xd}), X = per mod p ({(Xd - per(A)) % p == 0}); Boolean vars N' = n(1+2*ceil(lg p)) = {n*(1+2*math.ceil(math.log2(p)))}",
          rational and val == p ** n * Xd and (Xd - per(A)) % p == 0)

for p in (2, 3, 5, 7):
    z = cmath.exp(2j * math.pi / p)
    hh = [sum(y * z ** (-t * y) for y in range(p)) / p for t in range(p)]
    mods = sorted(set(round(abs(h), 6) for h in hh if abs(h) > 1e-9))
    print(f"(c) p={p}: |hhat(t)|, t=0..p-1 = {[round(abs(h),4) for h in hh]}  -> {'affine (constant modulus)' if len(mods)==1 else 'NOT affine'}")
print("\nALL PASS" if ok else "\nSOME FAIL")
