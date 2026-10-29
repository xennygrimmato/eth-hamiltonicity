"""modp_identities.py -- exact checks for perm-mod-p.md, sections 2-3.
(a) shifted Ryser (2.1) for arbitrary integer shifts w
(b) BHL truncation (2.2) mod p^k and the number of surviving terms
(c) repeated rows: m equal rows => m! | per
(d) low rank over F_p (2.3) and per = 0 mod p when rank*(p-1) < n
(e) Fourier / 2-local form of Ryser mod p (N = n + n*ceil(lg p) variables), computed in F_q, q = 1 mod p
"""
import random, itertools, math
from math import factorial
random.seed(20261029)

def per(A):
    n = len(A)
    if n == 0: return 1
    # Ryser, exact
    tot = 0
    for mask in range(1 << n):
        prod = 1
        for i in range(n):
            s = 0
            for j in range(n):
                if mask >> j & 1: s += A[i][j]
            prod *= s
            if prod == 0: break
        tot += (-1) ** (n - bin(mask).count('1')) * prod
    return tot

def rand01(n, d=0.5):
    return [[1 if random.random() < d else 0 for _ in range(n)] for _ in range(n)]

ok = True
def check(name, cond):
    global ok
    if not cond: ok = False
    print(("PASS " if cond else "FAIL ") + name)

# (a) shifted Ryser
for n in range(2, 8):
    A = rand01(n); P = per(A)
    for _ in range(3):
        w = [random.randint(-5, 5) for _ in range(n)]
        tot = 0
        for mask in range(1 << n):
            prod = 1
            for i in range(n):
                prod *= w[i] + sum(A[i][j] for j in range(n) if mask >> j & 1)
            tot += (-1) ** (n - bin(mask).count('1')) * prod
        if tot != P: break
    check(f"(a) shifted Ryser n={n}", tot == P)

# (b) truncation mod p^k
print("\n(b) per = sum over S with Z_w(S) < k  (mod p^k); surviving fraction vs 2^n")
for (n, p, k) in [(8, 3, 1), (8, 3, 2), (8, 5, 1), (8, 3, 3), (8, 2, 3), (8, 2, 5), (7, 7, 1), (8, 3, 4)]:
    A = rand01(n); P = per(A); M = p ** k
    good = True; fr = []
    for _ in range(4):
        w = [random.randrange(p) for _ in range(n)]
        tot = 0; surv = 0
        for mask in range(1 << n):
            f = [w[i] + sum(A[i][j] for j in range(n) if mask >> j & 1) for i in range(n)]
            Z = sum(1 for x in f if x % p == 0)
            if Z < k:
                surv += 1
                tot += (-1) ** (n - bin(mask).count('1')) * math.prod(f)
        good &= (tot - P) % M == 0
        fr.append(surv / 2 ** n)
    pred = sum(math.comb(n, z) * (1 / p) ** z * (1 - 1 / p) ** (n - z) for z in range(k))
    check(f"(b) n={n} p={p} k={k} kp/n={k*p/n:.2f}: surviving fraction {sum(fr)/len(fr):.3f} (binomial prediction {pred:.3f})", good)

# (c) repeated rows
for n in range(3, 8):
    for m in range(2, n + 1):
        A = rand01(n)
        for i in range(1, m): A[i] = list(A[0])
        A[0] = [random.randint(0, 3) for _ in range(n)]
        for i in range(1, m): A[i] = list(A[0])
        if per(A) % factorial(m): check(f"(c) n={n} m={m}", False)
check("(c) a row repeated m times => m! | per   (n<=7, all m)", True)

# (d) low rank over F_p
def perm_mod_lowrank(U, V, p):
    n, r = len(U), len(U[0])
    def coeffs(rows):
        # coefficients of prod_i (rows_i . x) truncated to exponents <= p-1, as dict alpha -> value mod p
        D = {tuple([0] * r): 1}
        for u in rows:
            E = {}
            for a, c in D.items():
                for l in range(r):
                    if u[l] % p and a[l] < p - 1:
                        b = list(a); b[l] += 1; b = tuple(b)
                        E[b] = (E.get(b, 0) + c * u[l]) % p
            D = E
        return D
    X, Y = coeffs(U), coeffs(V)
    tot = 0
    for a, c in X.items():
        if a in Y:
            tot += math.prod(factorial(x) for x in a) * c * Y[a]
    return tot % p

print()
for (n, p, r) in [(6, 3, 2), (6, 3, 3), (7, 3, 3), (7, 3, 4), (6, 5, 1), (6, 5, 2), (8, 3, 3), (8, 3, 4), (8, 5, 2), (8, 2, 7)]:
    good = True; zero_pred = r * (p - 1) < n; allzero = True
    for _ in range(4):
        U = [[random.randrange(p) for _ in range(r)] for _ in range(n)]
        V = [[random.randrange(p) for _ in range(r)] for _ in range(n)]
        A = [[sum(U[i][l] * V[j][l] for l in range(r)) % p for j in range(n)] for i in range(n)]
        pm = per(A) % p
        good &= pm == perm_mod_lowrank(U, V, p)
        allzero &= pm == 0
    check(f"(d) n={n} p={p} r={r}: formula (2.3); r(p-1)<n => per=0 mod p: pred {zero_pred}, all zero {allzero}", good and (allzero or not zero_pred))

# (e) Fourier 2-local form.  X := sum_S (-1)^{n-|S|} prod_i (r_i(S) mod p)  is = per mod p,
# and X = sum_{S, t in Z_p^n} (-1)^{n-|S|} prod_i hhat(t_i) prod_{i,j in S} zeta^{t_i A_ij}  (computed in F_q).
def is_prime(m):
    if m < 2: return False
    i = 2
    while i * i <= m:
        if m % i == 0: return False
        i += 1
    return True
print()
for (n, p) in [(5, 3), (6, 3), (5, 5), (4, 7)]:
    q = 1 + p * 10 ** 6
    while not is_prime(q): q += p
    g = 2
    while True:
        z = pow(g, (q - 1) // p, q)
        if z != 1: break
        g += 1
    pinv = pow(p, q - 2, q)
    hh = [pinv * sum(y * pow(z, (-t * y) % p, q) for y in range(p)) % q for t in range(p)]
    A = rand01(n)
    Xint = 0
    for mask in range(1 << n):
        Xint += (-1) ** (n - bin(mask).count('1')) * math.prod(sum(A[i][j] for j in range(n) if mask >> j & 1) % p for i in range(n))
    Xq = 0
    for mask in range(1 << n):
        sg = (-1) ** (n - bin(mask).count('1'))
        prod = 1
        for i in range(n):
            # sum over t_i: hhat(t) * zeta^{t * r_i}, i.e. the t-variables are summed row by row
            ri = sum(A[i][j] for j in range(n) if mask >> j & 1)
            prod = prod * sum(hh[t] * pow(z, t * ri % p, q) for t in range(p)) % q
        Xq = (Xq + sg * prod) % q
    check(f"(e) n={n} p={p}: X = per mod p ({Xint % p == per(A) % p}); 2-local F_q form = X ({Xq == Xint % q}); N = n + n*ceil(lg p) = {n + n*math.ceil(math.log2(p))}",
          Xint % p == per(A) % p and Xq == Xint % q)

print("\nALL PASS" if ok else "\nSOME FAIL")
