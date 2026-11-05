# Step (1): D.1's mode-monomial decomposition, literally, for ONE packet of ONE K_4 edge, at a node t.
# Verifies  G_e(t+alpha*zeta) == sum_{beta: sum w_Z beta_Z < p} f_beta (x) g_beta  (mod 2^p)
# where f_beta depends only on the ports of endpoint u and g_beta only on those of v (rank one across the
# edge, i.e. across the merge cut of matching i = v2(t)), with D.1's weights w_Z = b+1 (eq. tensor-mode-budget).
# Prints: #beta tuples (D.1 bookkeeping), #nonzero pieces, true 2-adic rank (#Smith invariants < p), 2^lam.
import sys, itertools
from fractions import Fraction
from k4lib import *

def poly_mul(Pa, Pb, MOD):
    out = {}
    for ea, ca in Pa.items():
        for eb, cb in Pb.items():
            e = tuple(x + y for x, y in zip(ea, eb)); out[e] = (out.get(e, 0) + ca * cb) % MOD
    return {e: c for e, c in out.items() if c}

def mode_pieces(e, A, lam, t, zeta, p, PBIG=200):
    K = Kernel(A); L = K.L; T = Fraction(t + K.alpha * zeta); i = v2(t); MOD = 1 << PBIG
    u, v = e; rs = real_slots(e, A, lam)
    sym = {w: lab(w, A)[i] for w in (u, v)}
    assert sym[u] != sym[v], "edge must cross the cut of coordinate i"
    W = lambda x, y: to_mod(K.W(x, y, T), PBIG)
    # modes: (side whose rows are targeted, tile y0, b);  crossing tile for rows at w: bit_i(y0) == sym[w]
    bmax = p - 1  # need b+1 < p
    modes = {w: [(y0, b) for y0 in range(2 ** (i + 1)) if bit(y0, i) == sym[w] for b in range(bmax)] for w in (u, v)}
    def coeff(x, y0, b):  # C(T)/(C'(0)(T-y0+x)) * (2^{i+1}/(T-y0+x))^b, exact
        num = Fraction(1)
        for s in K.S:
            num *= (T - s)
        q = num / (K.Cp0 * (T - y0 + x)) * (Fraction(2 ** (i + 1)) / (T - y0 + x)) ** b
        assert v2q(q) >= b + 1, (v2q(q), b)
        return to_mod(q, PBIG)
    # sanity: geometric expansion reproduces crossing entries mod 2^p
    for (x, r, c) in rs:
        for (y, r2, c2) in rs:
            if c2 != r:  # column vertex other endpoint -> crossing
                y0 = y % (2 ** (i + 1)); j = y >> (i + 1)
                s_ = sum(coeff(x, y0, b) * j ** b for b in range(bmax)) % (1 << p)
                assert s_ == W(x, y) % (1 << p)
    n = 2 ** lam
    # for each endpoint w: P_w[(local assignment of w's ports)] = polynomial in modes targeted at w
    def side_poly(w, zw):
        # zw: w's port bits (bit s = w's port on real slot s)
        P = {tuple([0] * len(modes[w])): 1}
        for s, (x, r, c) in enumerate(rs):
            if r != w: continue
            Y = (zw >> s) & 1
            loc = 0; lin = {}
            for k, (y, r2, c2) in enumerate(rs):
                if c2 == w:   # local column (column port held by w)
                    loc += W(x, y) * ((zw >> k) & 1)
            for m, (y0, b) in enumerate(modes[w]):
                lin[m] = coeff(x, y0, b)
            # factor l_Y(loc + sum lin_m Z_m)
            F = {}
            z0 = tuple([0] * len(modes[w]))
            F[z0] = (loc if Y == 1 else 1 - loc) % MOD
            for m, cm in lin.items():
                ex = [0] * len(modes[w]); ex[m] = 1
                F[tuple(ex)] = (cm if Y == 1 else -cm) % MOD
            P = poly_mul(P, F, MOD)
            P = {ex: cc for ex, cc in P.items() if sum((b + 1) * ex[m] for m, (y0, b) in enumerate(modes[w])) < p}
        return P
    def source_vals(w, zw):  # L_Z(X) for modes SOURCED at w (targeting the other endpoint): columns held by w
        o = v if w == u else u; vals = []
        for (y0, b) in modes[o]:
            sval = 0
            for k, (y, r2, c2) in enumerate(rs):
                if c2 == w and y % (2 ** (i + 1)) == y0:
                    j = y >> (i + 1); sval += (j ** b) * ((zw >> k) & 1)
            vals.append(sval)
        return vals
    wts = {w: [b + 1 for (y0, b) in modes[w]] for w in (u, v)}
    betas_u = set(); betas_v = set()
    SP = {w: [side_poly(w, z) for z in range(n)] for w in (u, v)}
    SV = {w: [source_vals(w, z) for z in range(n)] for w in (u, v)}
    # D.1 tuple count: all (beta_u, beta_v) with total weight < p (bounded per variable by #rows on target side)
    nrows = {w: sum(1 for (x, r, c) in rs if r == w) for w in (u, v)}
    def tuples(ws, budget, maxdeg):
        res = []
        def rec(k, bud, deg, cur):
            if k == len(ws): res.append(tuple(cur)); return
            bb = 0
            while bb * ws[k] < bud and bb <= deg:
                rec(k + 1, bud - bb * ws[k], deg - bb, cur + [bb]); bb += 1
        rec(0, budget, maxdeg, []); return res
    Tu = tuples(wts[u], p, nrows[u]); Tv = tuples(wts[v], p, nrows[v])
    pm = 1 << p
    G = [[0] * n for _ in range(n)]; npieces = 0; ntuples = 0
    for bu in Tu:
        wu = sum(a * b for a, b in zip(bu, wts[u]))
        for bv in Tv:
            wv = sum(a * b for a, b in zip(bv, wts[v]))
            if wu + wv >= p: continue
            ntuples += 1
            # f(zu) = [Z^bu] P_u(zu) * prod_{Z sourced at u (= targeted at v)} L_Z(zu)^{bv_Z}
            f = [SP[u][z].get(bu, 0) * prod_pow(SV[u][z], bv) % pm for z in range(n)]
            g = [SP[v][z].get(bv, 0) * prod_pow(SV[v][z], bu) % pm for z in range(n)]
            if any(f) and any(g):
                npieces += 1
                for zu in range(n):
                    if f[zu]:
                        for zv in range(n):
                            G[zu][zv] = (G[zu][zv] + f[zu] * g[zv]) % pm
    Gtrue = edge_matrix(e, A, lam, T, K, P=p)
    ok = all(G[a_][b_] == Gtrue[a_][b_] for a_ in range(n) for b_ in range(n))
    return ok, ntuples, npieces

def prod_pow(vals, beta):
    r = 1
    for x, b in zip(vals, beta): r *= x ** b
    return r

if __name__ == "__main__":
    A = 3; lam = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    K = Kernel(A)
    # W(0) = I and locality of W(t)
    for e in EDGES:
        G0 = edge_matrix(e, A, lam, Fraction(0), K)
        assert all(G0[x][y] == (1 if x == y else 0) for x in range(2 ** lam) for y in range(2 ** lam))
    print(f"A={A} L={K.L} lam={lam}: G_e(0) = identity (equality of lam-bit strings) for all 6 edges: OK")
    from sympy import Matrix
    for t in (1, 3, 2, 6, 4, -4):
        i = v2(t)
        cr = [e for e in EDGES if lab(e[0], A)[i] != lab(e[1], A)[i]]
        ranks = [Matrix(edge_matrix(e, A, lam, Fraction(t), K)).rank() for e in EDGES]
        print(f" node t={t} (merge along matching {i} = {sorted(CUTS[i][0])}|{sorted(CUTS[i][1])}): crossing edges {[''.join(e) for e in cr]}; rank over Q of G_e(t) per edge {dict(zip([''.join(e) for e in EDGES], ranks))}")
    print(" p : edge t : D.1 tuples | nonzero pieces | 2-adic rank (#Smith inv < p) | 2^lam   [identity verified mod 2^p]")
    for t in (1, 2, 4):
        i = v2(t)
        for e in [e for e in EDGES if lab(e[0], A)[i] != lab(e[1], A)[i]][:2]:
            Gm = edge_matrix(e, A, lam, Fraction(t + K.alpha), K, P=300)
            sv = smith_vals_mod(Gm, 300)
            for p in (4, 8, 12, 16):
                ok, nt, npc = mode_pieces(e, A, lam, t, 1, p)
                print(f"{p:3d} : {''.join(e)} t={t} : {nt:6d} | {npc:6d} | {sum(1 for x in sv if x < p):4d} | {2**lam}  {'OK' if ok else 'FAIL'}")
            print(f"     Smith valuations of G_{''.join(e)}(t+alpha) : {sv}")
