"""Normalisation-robust cut ranks: CONNECTED bounded-degree test graphs (research/tutte-plane.md §5.3).

Every test graph G(sigma, R) is connected, so k(G) = 1 and any normalisation c(n,m,k(G)) T_G
(T itself, the FK form Z = u^k v^n T, the forest form, ...) differs from T only by row/column
scalings when n and m split as n_L + n_R, m_L + m_R (they do).  Hence the rank of the cut matrix
is the same for every such normalisation.

L side : linear forest F_sigma on the boundary vertices u_1..u_b (sigma ranges over all of Pi(b)).
Cross  : matching u_i - w_i   (x != 0),   or triangle u_i, w_i, w'_i (x = 0).
R side : linear forest F_tau on w_1..w_b, plus a connector between consecutive tau-blocks;
         connector types  E: edge w-w'          P: path w-h-w'            (x != 0)
                          T: triangle(w,h,h') + edge h-w'   T2: triangle(w,w',h')   (x = 0)
         all 2^{|tau|-1} choices, so the R side is always connected.
Lemma (proved in the note): (q+v) z_{R} = z_{R+P} - v z_{R+E} and (Z(K3)/q) z_R = z_{R+T} - v z_{R+T2};
so the span of the connected R-vectors contains every forest vector z_{R_tau}, which span R^{Bell(b)}.
Hence rank = rank M_q (x != 1), = Bell(b) (x = 1, y != 1).

Computation: boundary vectors by subset enumeration on each side and the gluing formula
Z = sum_{P,Q} a(P) q^{|PvQ|} z(Q) (x != 1),  T(1,y) v^{n-1} = sum a(P) z0(Q) [PvQ = 1] (x = 1);
a few entries are cross-checked against brute-force Tutte of the glued graph.
Prints PASS/FAIL.
"""
import sys, itertools, random
from fractions import Fraction
from tutte_lib import *
from tutte_ranks import expected_rank_Mq, eval_T

def lin_forest(P, verts):
    E = []
    for B in blocks(P):
        for s, t in zip(B, B[1:]):
            E.append((verts[s], verts[t]))
    return E

def r_graphs(b, tau, xzero):
    """yield (nR_total, edges) of R' = crossing gadget + F_tau + connectors; vertex ids:
    u_i = i, w_i = b+i, w'_i = 2b+i (triangle gadget), extra vertices after."""
    W = [b + i for i in range(b)]
    base = lin_forest(tau, W)
    if xzero:
        cross = [(i, b + i) for i in range(b)] + [(i, 2 * b + i) for i in range(b)] + [(b + i, 2 * b + i) for i in range(b)]
        nxt0 = 3 * b
        types = ("T", "T2")
    else:
        cross = [(i, b + i) for i in range(b)]
        nxt0 = 2 * b
        types = ("E", "P")
    bl = sorted(blocks(tau), key=min)
    pairs = [(W[bl[j][-1]], W[bl[j + 1][0]]) for j in range(len(bl) - 1)]
    for choice in itertools.product(types, repeat=len(pairs)):
        E = cross + base; nxt = nxt0
        for (w, w2), t in zip(pairs, choice):
            if t == "E":
                E.append((w, w2))
            elif t == "P":
                E += [(w, nxt), (nxt, w2)]; nxt += 1
            elif t == "T":
                h, h2 = nxt, nxt + 1; nxt += 2
                E += [(w, h), (h, h2), (w, h2), (h, w2)]
            else:   # T2: triangle w, w2, h'
                h2 = nxt; nxt += 1
                E += [(w, w2), (w2, h2), (w, h2)]
        yield nxt, E, choice

def boundary_vectors(nv, E, b, q, v):
    """z[(Q, internal, |A|)] = number of A <= E(R') inducing Q on u_1..u_b, with `internal`
    components avoiding U.  (Exponents are kept so that every point, y = 1 included, is exact.)"""
    z = {}
    present = sorted(set([x for e in E for x in e]) | set(range(b)))
    for _, A in subsets(E):
        lab = comp_labels(nv, A)
        ucomps = set(lab[i] for i in range(b))
        internal = len(set(lab[x] for x in present) - ucomps)
        key = (canon([lab[i] for i in range(b)]), internal, len(A))
        z[key] = z.get(key, 0) + 1
    return z, None, len(present)

def pw(a, e):
    return Fraction(1) if e == 0 else Fraction(a) ** e

def run_point(b, x, y, C, check_brute=True):
    x, y = Fraction(x), Fraction(y); u, v = x - 1, y - 1; q = u * v
    Ps = set_partitions(b); top = tuple([0] * b)
    xzero = (x == 0)
    Lvec = []
    for sig in Ps:
        a = {}
        F = lin_forest(sig, list(range(b)))
        for _, A in subsets(F):
            key = (canon(comp_labels(b, A)), len(A))
            a[key] = a.get(key, 0) + 1
        Lvec.append((sig, F, a))
    cols = []
    for tau in Ps:
        for nv, E, ch in r_graphs(b, tau, xzero):
            z, z0, nR = boundary_vectors(nv, E, b, q, v)
            cols.append((tau, ch, nv, E, z, z0, nR))
    Tm = []
    for (sig, F, a) in Lvec:
        row = []
        for (tau, ch, nv, E, z, z0, nR) in cols:
            n_tot = nR          # the u's lie in the crossing edges, so they are counted in nR
            T = Fraction(0)
            for (P, la), ca in a.items():
                for (Q, it, lr), cz in z.items():
                    k = nblocks(join(P, Q)) + it
                    T += ca * cz * pw(u, k - 1) * pw(v, la + lr - n_tot + k)
            row.append(T)
        Tm.append(row)
    if check_brute:
        rng = random.Random(b)
        for _ in range(3):
            i = rng.randrange(len(Lvec)); j = rng.randrange(len(cols))
            sig, F, a = Lvec[i]; tau, ch, nv, E, z, z0, nR = cols[j]
            used = sorted(set([t for e in E + F for t in e]) | set(range(b)))
            relabel = {t: k for k, t in enumerate(used)}
            GE = [(relabel[s], relabel[t]) for s, t in E + F]
            C.check(ncomp(len(used), GE) == 1, "connected test graph")
            if len(GE) <= 18:
                C.check(eval_T(len(used), GE, x, y) == Tm[i][j], f"gluing formula vs brute force b={b} ({x},{y})")
    r = rank_Q(Tm)
    if u == 0:
        exp = bell(b) if v != 0 else None
    elif v == 0:
        exp = None
    else:
        exp = expected_rank_Mq(b, q)
    if exp is not None:
        C.check(r == exp, f"rank b={b} ({x},{y}) got {r} expected {exp}")
    return r, exp, len(cols)

def main(maxb=4):
    C = Checker("tutte_ranks_connected")
    pts = [(3, Fraction(1, 2)), (-2, 3), (Fraction(1, 2), 3), (2, 0), (-1, 0), (Fraction(-1, 2), Fraction(-1, 2)),
           (1, 2), (1, -1), (1, 0), (3, 3), (-1, -1), (2, 1), (Fraction(5, 2), 1), (1, 1),
           (0, Fraction(1, 2)), (0, 3), (0, -2)]
    for b in range(1, maxb + 1):
        line = []
        for (x, y) in pts:
            if x == 0 and b > 3:
                continue
            r, exp, nc = run_point(b, x, y, C, check_brute=(b <= 3))
            line.append(f"({x},{y}):{r}" + ("" if exp is None else f"/{exp}"))
        print(f"b={b} Bell={bell(b)} #R-graphs={nc}: " + " ".join(line), flush=True)
    return C.done()

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 4)
