"""d8_exact.py -- EXACT flattening certificate D for the incidence 8-cycle under merges G, H (engine3-open-door §3.4, §5.5(a)).
Model (engine2-decorrelated §8.2 reduction, generalised to 4 groups): a contraction M is an orientation o in {-1,0,1}^E of
(a subset of) the crossing edges (longer paths only change the node net flows by flow decomposition, and only the group
excesses n^G_i = sum_{v in G_i} (out_v - in_v) enter).  d_G(M) = LP of lp4.py at n^G (closed form below), same for H;
D = max_M min(d_G(M), d_H(M)).
Exact method: dynamic programming over the edges on the state (n^G, n^H) in Z^4 x Z^4 (every orientation's state is
reachable, every reachable state is realised), then evaluate min(d_G,d_H) on every reachable state.  Cross-checked by
(i) the scaled version o in {-k..k}^E (multiplicity k, i.e. k bits per edge used) to get the fractional (per-bit) value,
(ii) an exact LP over o in [-1,1]^E for every pair of dual-vertex linear pieces (the true asymptotic, scale-free value).
Closed form of the 4-group LP: d(n) = max( max_i|n_i|, max_{i<j}|n_i+n_j|, (1/2)sum_i|n_i|, (1/2)(|n_1+n_2|+|n_1+n_3|+|n_1+n_4|) ).
Usage: python3 d8_exact.py [kmax]  (k > 1 only for the 12- and 8-edge sub-configurations: memory)"""
import itertools, sys, numpy as np
from fractions import Fraction
from scipy.optimize import linprog
sys.path.insert(0, __import__('os').path.dirname(__file__))
import lp4

def dclosed(n):
    a = [abs(x) for x in n]
    pr = [abs(n[i] + n[j]) for i, j in itertools.combinations(range(4), 2)]
    return max(max(a), max(pr), Fraction(sum(a), 2), Fraction(abs(n[0]+n[1]) + abs(n[0]+n[2]) + abs(n[0]+n[3]), 2))

nodes = list(range(1, 9))
G = [[1, 2], [3, 4], [5, 6], [7, 8]]; H = [[2, 3], [4, 5], [6, 7], [8, 1]]
gG = {v: i for i, g in enumerate(G) for v in g}; gH = {v: i for i, g in enumerate(H) for v in g}
dist = lambda i, j: min((j - i) % 8, (i - j) % 8)
E_all = [(i, j) for i, j in itertools.combinations(nodes, 2) if dist(i, j) >= 2]
E_two = [e for e in E_all if dist(*e) >= 3]; E_three = [e for e in E_all if dist(*e) == 2]

def vec(e):
    u, v = e; x = [0] * 8
    x[gG[u]] += 1; x[gG[v]] -= 1; x[4 + gH[u]] += 1; x[4 + gH[v]] -= 1
    return tuple(x)

def dp(edges, k=1):
    states = {(0,) * 8: None}
    for e in edges:
        w = vec(e); new = {}
        for s in states:
            for c in range(-k, k + 1):
                t = tuple(a + c * b for a, b in zip(s, w))
                if t not in new: new[t] = (s, c)
        # keep a back-pointer chain per layer for witness reconstruction
        states = {t: (s, c) for t, (s, c) in new.items()}
        dp.layers.append(states)
    return states
dp.layers = []

def best(edges, k=1):
    dp.layers = []
    st = dp(edges, k)
    bestv, bests = -1, None
    hist = {}
    for s in st:
        v = min(dclosed(s[:4]), dclosed(s[4:]))
        hist[v] = hist.get(v, 0) + 1
        if v > bestv: bestv, bests = v, s
    # witness orientation
    o = []; s = bests
    for L in reversed(dp.layers):
        p, c = L[s]; o.append(c); s = p
    o = o[::-1]
    return bestv, bests, o, len(st)

def frac_lp(edges):
    """max over o in [-1,1]^E of min(d_G, d_H): d = max of linear functionals L(n) = sum_S y_S s_S n_S (y dual vertex,
    s signs).  For each pair of functionals, max_o min(L_G, L_H) is an LP; take the max.  Reduced by: max over o of a
    single functional is sum_e |L(w_e)| (upper bound), used to prune."""
    W = np.array([vec(e) for e in edges], float)  # E x 8
    cutsG = np.array([[1 if i in S else 0 for i in range(4)] for S in lp4.CUTS], float)  # 7 x 4
    funcs = set()
    for y in lp4.dual_vertices():
        yv = np.array([float(x) for x in y])
        supp = [i for i in range(7) if yv[i] > 0]
        for signs in itertools.product((-1, 1), repeat=len(supp)):
            s = np.zeros(7); s[supp] = signs
            funcs.add(tuple(np.round((yv * s) @ cutsG, 9)))   # functional on n (4-vector)
    funcs = [np.array(f) for f in funcs if any(abs(x) > 0 for x in f)]
    LG = [W[:, :4] @ f for f in funcs]; LH = [W[:, 4:] @ f for f in funcs]   # per-edge coefficients
    ubG = [np.abs(a).sum() for a in LG]; ubH = [np.abs(a).sum() for a in LH]
    order = sorted(((min(ubG[i], ubH[j]), i, j) for i in range(len(funcs)) for j in range(len(funcs))), reverse=True)
    best = -1; arg = None; nlp = 0
    Ecount = len(edges)
    for ub, i, j in order:
        if ub <= best + 1e-9: break
        # variables o (E), t ; max t s.t. t <= LG.o, t <= LH.o
        c = np.zeros(Ecount + 1); c[-1] = -1
        A = np.zeros((2, Ecount + 1)); A[0, :Ecount] = -LG[i]; A[0, -1] = 1; A[1, :Ecount] = -LH[j]; A[1, -1] = 1
        r = linprog(c, A_ub=A, b_ub=[0, 0], bounds=[(-1, 1)] * Ecount + [(None, None)], method='highs'); nlp += 1
        if -r.fun > best + 1e-9: best = -r.fun; arg = (r.x[:Ecount].round(6), funcs[i], funcs[j])
    return best, arg, nlp, len(funcs)

if __name__ == '__main__':
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    # sanity: closed form vs lp4
    rng = np.random.default_rng(1)
    for _ in range(2000):
        n = list(rng.integers(-9, 10, 3)); n.append(-sum(n))
        assert abs(float(dclosed(n)) - lp4.lp_value(n)) < 1e-7
    print("closed form of the 4-group LP agrees with linprog on 2000 random n", flush=True)
    # sanity on the prism with 3 groups would need the 3-group LP; instead check the rectangle-like reduction trivially.
    for name, edges in (("all 20 edges", E_all), ("12 two-cell edges", E_two), ("8 three-cell edges", E_three)):
        print(f"== 8-cycle, {name} (E = {len(edges)}) ==", flush=True)
        for k in range(1, (kmax if len(edges) <= 12 else 1) + 1):
            v, s, o, ns = best(edges, k)
            print(f"  multiplicity k={k}: reachable states {ns}; max_M min(d_G,d_H) = {v} -> per unit {Fraction(v)/k} = {float(Fraction(v)/k):.4f} of {len(edges)}"
                  f"; n^G={s[:4]} n^H={s[4:]}; witness o={o}", flush=True)
        fb, arg, nlp, nf = frac_lp(edges)
        print(f"  fractional (o in [-1,1]^E, exact asymptotic flattening value): {fb:.6f} of {len(edges)}  [{nf} linear pieces, {nlp} LPs]")
        print(f"     maximiser o = {list(arg[0])}", flush=True)
