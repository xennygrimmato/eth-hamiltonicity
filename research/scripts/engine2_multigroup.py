"""engine2 M7: multi-grouping gadget recursions.  Nodes = tuples u in [K]^d (coordinate j = group of u in grouping P_j).
A 2-group-good gadget for the edge (u,v) with cut family S needs the 'mix' nodes (u_S, v_{S^c}) in X.
(a) exact closure lemma: X = X_S x X_{S^c} for two cuts S,T  =>  X is a product over the atoms (brute force on [3]^3);
(b) robust entropy chain (Theorem 7.3):  log|X| >= sum_j H(A_j) - sum_{j<d} I_j  and
    I_S <= h(delta_S) + delta_S (d log K - log|X|),  on random near-product designs;
(c) linear designs X = C in F_q^m: the cut families available to an edge w are unions of matroid components except
    on a set of edges of density <= 2^m/q."""
import itertools, random, math
from collections import Counter
random.seed(3)
allok = True
def rep(name, ok):
    global allok; allok &= ok; print(f"[{'PASS' if ok else 'FAIL'}] {name}")

# (a) exact: sets X in [3]^3 that are products across S={0} and T={1} must be products over atoms {0},{1},{2}
pts = list(itertools.product(range(3), repeat=3))
def is_prod(X, S):
    Sc = [j for j in range(3) if j not in S]
    P1 = {tuple(x[j] for j in S) for x in X}; P2 = {tuple(x[j] for j in Sc) for x in X}
    return len(X) == len(P1) * len(P2)
cnt = 0; bad = 0
for trial in range(20000):
    # random X built as product across {0} then forced into product across {1} by closure
    X = set(random.sample(pts, random.randint(2, 10)))
    for _ in range(5):
        P0 = {x[0] for x in X}; R0 = {x[1:] for x in X}; X = {(a,) + r for a in P0 for r in R0}
        P1 = {x[1] for x in X}; R1 = {(x[0], x[2]) for x in X}; X = {(r[0], b, r[1]) for b in P1 for r in R1}
    if is_prod(X, [0]) and is_prod(X, [1]):
        cnt += 1
        full = {x for x in itertools.product(*[sorted({y[j] for y in X}) for j in range(3)])}
        if X != full: bad += 1
rep(f"(a) {cnt} sets that are products across {{0}} and across {{1}}: all are full products over atoms (counterexamples: {bad})", bad == 0 and cnt > 0)

# (b) robust entropy chain on random designs X subset [K]^d: product minus a delta-fraction, or union of two products
def H(c):
    n = sum(c.values()); return -sum(v / n * math.log2(v / n) for v in c.values())
def h2(p): return 0 if p in (0, 1) else -p * math.log2(p) - (1 - p) * math.log2(1 - p)
def analyse(X, K, d):
    X = list(X); Xs = set(X); n = len(X)
    HA = [H(Counter(x[j] for x in X)) for j in range(d)]
    I = []; dl = []
    for j in range(d):
        HS = H(Counter(x[j] for x in X)); HSc = H(Counter(x[:j] + x[j + 1:] for x in X))
        I.append(HS + HSc - math.log2(n))
        miss = sum(1 for u in X for v in X if (u[:j] + (v[j],) + u[j + 1:]) not in Xs) / n ** 2   # mix (v_j, u_{-j})
        dl.append(miss)
    chain = math.log2(n) >= sum(HA) - sum(I[:d - 1]) - 1e-9
    bnd = all(I[j] <= h2(dl[j]) + dl[j] * (d * math.log2(K) - math.log2(n)) + 1e-9 for j in range(d))
    return chain, bnd, math.log2(n) / math.log2(K), max(dl), I
okc = okb = True; rows = []
for (K, d) in [(6, 2), (5, 3), (4, 4)]:
    full = list(itertools.product(range(K), repeat=d))
    for delta in [0.0, 0.05, 0.2, 0.5]:
        X = [x for x in full if random.random() >= delta]
        c, b, beta, dmax, I = analyse(X, K, d); okc &= c; okb &= b; rows.append((K, d, 'minus', delta, round(beta, 3), round(dmax, 3)))
    # union of two random 'sub-products' (each coordinate a random half) -- far from a product
    A = [random.sample(range(K), K // 2 + 1) for _ in range(d)]; B = [random.sample(range(K), K // 2 + 1) for _ in range(d)]
    X = set(itertools.product(*A)) | set(itertools.product(*B))
    c, b, beta, dmax, I = analyse(X, K, d); okc &= c; okb &= b; rows.append((K, d, 'union', None, round(beta, 3), round(dmax, 3)))
for r in rows: print("   K=%d d=%d %-5s delta=%s : log|X|/log K = %s, max_S delta_S = %s" % r)
rep("(b) chain log|X| >= sum_j H(A_j) - sum_{j<d} I_j holds on all designs", okc)
rep("(b) I_S <= h(delta_S) + delta_S (d log K - log|X|) holds on all designs", okb)

# (c) linear designs
def codewords(G, q):
    b = len(G); m = len(G[0])
    return {tuple(sum(c * G[i][j] for i, c in enumerate(co)) % q for j in range(m)) for co in itertools.product(range(q), repeat=b)}
def components(C, m):
    # coordinates j,k in same component iff not separable: C = C_S + C_{S^c} for S containing j not k
    comps = []
    rest = set(range(m))
    def splits(S):
        CS = {w for w in C if all(w[j] == 0 for j in range(m) if j not in S)}
        CSc = {w for w in C if all(w[j] == 0 for j in S)}
        return len(CS) * len(CSc) == len(C)
    # finest S with splits: brute force over subsets
    atoms = [set(range(m))]
    for r in range(1, m):
        for S in itertools.combinations(range(m), r):
            if splits(set(S)):
                new = []
                for a in atoms:
                    for part in (a & set(S), a - set(S)):
                        if part: new.append(part)
                atoms = new
    return len(atoms)
res = []; okl = True
for (q, m, b) in [(5, 3, 2), (7, 4, 2), (7, 4, 3), (5, 4, 3), (17, 4, 3), (31, 4, 3), (101, 3, 2)]:
    for trial in range(3):
        if trial == 0 and b >= 2:
            # decomposable code: direct sum of a [1,1] and an [m-1,b-1] code
            G = [[1] + [0] * (m - 1)] + [[0] + [random.randrange(q) for _ in range(m - 1)] for _ in range(b - 1)]
        else:
            G = [[random.randrange(q) for _ in range(m)] for _ in range(b)]
        C = codewords(G, q)
        if len(C) != q ** b: continue
        ncomp = components(C, m)
        over = 0; maxd = 0
        for w in C:
            if not any(w): continue
            Ss = [set(S) for r in range(1, m) for S in itertools.combinations(range(m), r)
                  if tuple(w[j] if j in S else 0 for j in range(m)) in C and any(w[j] for j in S) and any(w[j] for j in range(m) if j not in S)]
            atoms = [set(j for j in range(m) if w[j])]
            for S in Ss:
                atoms = [p for a in atoms for p in (a & S, a - S) if p]
            dw = len(atoms); maxd = max(maxd, dw)
            if dw > ncomp: over += 1
        frac = over / (q ** b - 1)
        res.append((q, m, b, ncomp, maxd, round(frac, 4), round(2 ** m / q, 3)))
        okl &= frac <= 2 ** m / q
for r in res: print("   q=%d m=%d dim=%d: matroid components=%d, max distinct cuts over edges=%d, frac edges with more cuts than components=%s (bound 2^m/q=%s)" % r)
rep("(c) linear designs: edges with more distinct cuts than components have density <= 2^m/q", okl)
print("ALL PASS" if allok else "SOME FAIL")
