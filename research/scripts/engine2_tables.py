"""engine2 M1/M3: (a) low-CP-rank tables make Z cheap (exact identity);
(b) tables produced by grouping a random sparse 3-CNF have full flattening rank (no structure to exploit);
(c) CRT: Z mod p for small primes reconstructs Z exactly, and the rectangle F=[x=v][y=u] has full rank mod p."""
import itertools, random
from engine2_lib import *
random.seed(1)
allok = True

# (a) CP-rank identity: T_a(y) = sum_{i<r} prod_b f[a][b][i][y_b]  =>  Z = sum_{i in [r]^K} prod_{a<b} <f[a][b][i_a], f[b][a][i_b]>
for (K, D, r) in [(3, 3, 2), (4, 2, 2), (4, 3, 2), (5, 2, 2)]:
    f = {(a, b, i): [random.randint(-2, 2) for _ in range(D)] for a in range(K) for b in range(K) if a != b for i in range(r)}
    T = []
    for a in range(K):
        nb = [b for b in range(K) if b != a]
        T.append({y: sum(eval_prod for eval_prod in [1] if True) * 0 + sum(
            __import__('math').prod(f[(a, b, i)][yb] for b, yb in zip(nb, y)) for i in range(r))
            for y in itertools.product(range(D), repeat=K - 1)})
    Z = clique_Z(K, D, T)
    Z2 = 0
    for i in itertools.product(range(r), repeat=K):
        p = 1
        for (a, b) in edges(K):
            p *= sum(f[(a, b, i[a])][x] * f[(b, a, i[b])][x] for x in range(D))
        Z2 += p
    allok &= report(f"(a) CP-rank-{r} tables, K={K}, D={D}: Z = sum over r^K of edge inner products ({Z})", Z == Z2)

# (b) grouped-CNF tables, K=3 groups; pair blocks of lam boolean vars; private vars per group
def grouped_table(lam, npriv, nclauses):
    # variables of group a: legs b (lam bits), leg c (lam bits), private npriv bits
    nv = 2 * lam + npriv
    cls = []
    for _ in range(nclauses):
        vs = random.sample(range(nv), 3)
        cls.append([(v, random.random() < 0.5) for v in vs])
    D = 2 ** lam
    M = [[0] * D for _ in range(D)]
    for yb in range(D):
        for yc in range(D):
            cnt = 0
            for z in range(2 ** npriv):
                bits = [(yb >> k) & 1 for k in range(lam)] + [(yc >> k) & 1 for k in range(lam)] + [(z >> k) & 1 for k in range(npriv)]
                if all(any(bits[v] == (1 if s else 0) for v, s in c) for c in cls):
                    cnt += 1
            M[yb][yc] = cnt
    return M
for lam in [2, 3]:
    D = 2 ** lam
    for dens in [1.5, 3.0]:
        ranks = []
        for trial in range(20):
            npriv = 3 * lam; M = grouped_table(lam, npriv, int(dens * (2 * lam + npriv)))
            ranks.append(rank_exact(M))
        import math
        lr = sum(math.log2(max(x, 1)) for x in ranks) / (20 * lam)
        print(f"(b) lam={lam}, D={D}, clause density {dens}: ranks (leg b | leg c) of 20 grouped 3-CNF tables {sorted(ranks)}; mean log2(rank)/lam = {lr:.2f}")
# (b') rank deficiency is only a U-compression: replace edge label by a row basis (exact, Fractions)
from fractions import Fraction
def compress_edge_check(K, D, T, a, b):
    """T[a] restricted as matrix rows = label on edge ab, cols = other legs. Compress edge ab to rank r alphabet; recompute Z."""
    la = legs(K, a); ia = la.index(tuple(sorted((a, b))))
    others = [y for y in itertools.product(range(D), repeat=K - 2)]
    def ins(y, x, i): return y[:i] + (x,) + y[i:]
    rows = [[T[a][ins(y, x, ia)] for y in others] for x in range(D)]
    # greedy basis
    basis = []
    for x in range(D):
        if rank_exact([rows[i] for i in basis] + [rows[x]]) > len(basis): basis.append(x)
    r = len(basis)
    import sympy
    B = sympy.Matrix([rows[i] for i in basis]).T  # cols = basis rows
    coef = {}
    for x in range(D):
        sol = B.solve_least_squares(sympy.Matrix(rows[x])) if r < len(others) else B.solve(sympy.Matrix(rows[x]))
        coef[x] = [sympy.nsimplify(c) for c in sol]
        assert B * sympy.Matrix(coef[x]) == sympy.Matrix(rows[x])
    # new tables: alphabet on edge ab is r (pad to D with zeros so clique_Z still applies)
    Ta = {}; Tb = {}
    lb = legs(K, b); ib = lb.index(tuple(sorted((a, b))))
    for y in itertools.product(range(D), repeat=K - 1):
        k = y[ia]; Ta[y] = rows[basis[k]][others.index(y[:ia] + y[ia + 1:])] if k < r else 0
    for y in itertools.product(range(D), repeat=K - 1):
        k = y[ib]; rest = y[:ib] + y[ib + 1:]
        Tb[y] = sum(coef[x][k] * T[b][ins(rest, x, ib)] for x in range(D)) if k < r else 0
    T2 = list(T); T2[a] = Ta; T2[b] = Tb
    return r, clique_Z(K, D, T2)
done = 0
while done < 3:
    K, D = 3, 4
    T = [{y: 0 for y in itertools.product(range(D), repeat=2)} for _ in range(K)]
    for a in range(K):
        M = grouped_table(2, 6, 24)
        for yb in range(D):
            for yc in range(D): T[a][(yb, yc)] = M[yb][yc]
    Z = clique_Z(K, D, T)
    r, Z2 = compress_edge_check(K, D, T, 0, 1)
    if Z == 0 or r == D: continue
    done += 1
    allok &= report(f"(b') edge (0,1) compressed from D={D} to rank alphabet r={r}: Z unchanged ({Z})", Z == Z2)

# (c) CRT and ranks mod p
K, D = 4, 2
T = random_tables(K, D, -50, 50)
Z = clique_Z(K, D, T)
primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
P = 1; R = 0
for p in primes:
    Tp = [{y: v % p for y, v in t.items()} for t in T]
    zp = clique_Z(K, D, Tp) % p
    # CRT combine
    R = R + P * ((zp - R) * pow(P, -1, p) % p); P *= p
R = R if R <= P // 2 else R - P
allok &= report(f"(c) CRT over 12 primes reconstructs Z={Z} from Z mod p computed with tables mod p", R == Z)
for lam in [1, 2]:
    D = 2 ** lam
    F = [[1 if (x == v and y == u) else 0 for u in range(D) for v in range(D)] for x in range(D) for y in range(D)]
    Fc = [[1 if (x == v and y == u) else 0 for y in range(D) for v in range(D)] for x in range(D) for u in range(D)]
    ok = all(rank_mod(F, p) == D * D and rank_mod(Fc, p) == D * D for p in [2, 3, 5])
    allok &= report(f"(c) rectangle F (D={D}) has rank D^2 across both cuts over F_2, F_3, F_5", ok)
print("ALL PASS" if allok else "SOME FAIL")
