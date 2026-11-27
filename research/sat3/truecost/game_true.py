#!/usr/bin/env python3
"""Level-1 crossing game on 3-nets (attain/game1.py) with flattening LOWER BOUNDS on the true cost of a
piece in place of the certified costs.

A piece Psi_theta of a factor (wire a-c with p bits, wire b-d with q bits, p + q = 1) is, under merge k,
a tensor on the blocks of the partition of {a,b,c,d} induced by the groups of k.  Its true D1 cost is the
cheapest network on these blocks; a lower bound is the cut LP

    min sum_{B<B'} x_{BB'}   s.t.   sum_{B in S, B' not in S} x_{BB'} >= rho(S)   for every union S of blocks,

rho(S) = log-rank of Psi_theta across (legs in S | other legs):
    rho(a) = rho(c) = p, rho(b) = rho(d) = q      (single-party ranks: full in every table, true-costs.md)
    rho(ab) = r = R cos(theta), rho(ad) = r' = R sin(theta), R = sqrt(2(p^2+q^2))   (theta on the arc
                 |p-q| <= r, r' <= p+q: the certified values; they are the true ones if the arc lemma applies)
    rho(ac) = r3 :  model O1: 2 min(p,q) (the value found in the tables for n1 = n2);  model O2: 0.
The LP value is the maximum over the vertices of the dual polytope, computed once per block pattern.

Modes:  cert  = certified costs (must reproduce attain/game1.py);
        O1    = lower bounds, r3 = 2 min(p,q);      O2 = lower bounds, r3 = 0;
        H     = certified costs except: four-block patterns cost the O1 lower bound (isolates the third merge).
Usage: game_true.py NET [nt] [short]      NET in 2, 3, 2x2, 4, 5, ...  ('short': five weight vectors)
"""
import sys, os, math, itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'attain'))
import game1

LEGS = 'abcd'
# rank type of a subset of legs: index into (p, q, r, r', r3)
def rho_type(S):
    S = frozenset(S)
    if len(S) > 2:
        S = frozenset(LEGS) - S
    if len(S) == 1:
        return 0 if next(iter(S)) in 'ac' else 1
    if S in (frozenset('ab'), frozenset('cd')): return 2
    if S in (frozenset('ad'), frozenset('bc')): return 3
    return 4


def dual_vertices(pat):
    """pat: canonical labels of (a,b,c,d).  Returns array V (nv, 5): cost >= max_v V[v] . (p,q,r,r',r3)."""
    blocks = sorted(set(pat))
    nb = len(blocks)
    if nb == 1:
        return np.zeros((1, 5))
    legs_of = {B: [LEGS[i] for i in range(4) if pat[i] == B] for B in blocks}
    cuts = []
    for k in range(1, nb):
        for S in itertools.combinations(blocks, k):
            if blocks[0] in S:      # one representative of S / complement
                cuts.append(S)
    cuts = [S for S in cuts if len(S) < nb]
    edges = list(itertools.combinations(blocks, 2))
    nS, nE = len(cuts), len(edges)
    A = np.zeros((nE, nS))
    for ie, (B, C) in enumerate(edges):
        for iS, S in enumerate(cuts):
            if (B in S) != (C in S):
                A[ie, iS] = 1
    types = [rho_type([l for B in S for l in legs_of[B]]) for S in cuts]
    # vertices of {y >= 0, A y <= 1}
    Aall = np.vstack([A, -np.eye(nS)]); ball = np.concatenate([np.ones(nE), np.zeros(nS)])
    verts = set()
    for rows in itertools.combinations(range(nE + nS), nS):
        M = Aall[list(rows)]
        if abs(np.linalg.det(M)) < 1e-9: continue
        yv = np.linalg.solve(M, ball[list(rows)])
        if (Aall @ yv <= ball + 1e-9).all():
            v = np.zeros(5)
            for iS in range(nS): v[types[iS]] += yv[iS]
            verts.add(tuple(np.round(v, 9)))
    return np.array(sorted(verts))


_DV = {}
def dv(pat):
    if pat not in _DV: _DV[pat] = dual_vertices(pat)
    return _DV[pat]


NTH = 2001
_cache = {}

def mval(pats, p, q, w, mode, detail=False):
    """max over theta on the arc of sum_k w_k c_k(theta)."""
    key = (pats, round(p, 9), tuple(np.round(w, 9)), mode)
    if not detail and key in _cache: return _cache[key]
    R = math.sqrt(2 * (p * p + q * q))
    th0 = math.acos(min(1.0, (p + q) / R)); th1 = math.asin(min(1.0, (p + q) / R))
    th = np.linspace(th0, th1, NTH)
    th = np.unique(np.concatenate([th, [math.pi / 4]]))
    r = np.minimum(R * np.cos(th), p + q); rp = np.minimum(R * np.sin(th), p + q)
    tot = np.zeros(len(th)); per = []
    for k, pat in enumerate(pats):
        S, Ac, Ab, A3 = game1.consts(*pat, p, q)
        cert = np.minimum(np.minimum(S, A3 + 2 * min(p, q)), np.minimum(Ac + r, Ab + rp))
        if mode == 'cert':
            ck = cert
        else:
            r3 = 2 * min(p, q) if mode in ('O1', 'H') else 0.0
            V = dv(pat)
            rho = np.stack([np.full(len(th), p), np.full(len(th), q), r, rp, np.full(len(th), r3)], axis=1)
            lb = (rho @ V.T).max(axis=1)
            assert (lb <= cert + 1e-9).all(), (pat, p, q, mode)
            ck = lb if (mode in ('O1', 'O2') or len(set(pat)) == 4) else cert
        per.append(ck); tot += w[k] * ck
    i = int(np.argmax(tot))
    if detail: return tot[i], th[i], [c[i] for c in per]
    _cache[key] = tot[i]
    return tot[i]


def solve(lab, edges, w, tgrid, mode):
    E = len(edges); w = np.asarray(w, float); npm = lab.shape[1]
    raw = np.array([sum(w[k] for k in range(npm) if lab[a, k] != lab[c, k]) for (a, c) in edges])
    rows, cols, vals, rhs, info = [], [], [], [], []
    nr = 0
    for i in range(E):
        a, c = edges[i]
        for j in range(i + 1, E):
            b, d = edges[j]
            for (bb, dd) in ((b, d), (d, b)):     # both orientations (the lower bounds are not symmetric a priori)
                pats = tuple(game1.canon((lab[a, k], lab[bb, k], lab[c, k], lab[dd, k])) for k in range(npm))
                for t in tgrid:
                    m = mval(pats, t, 1 - t, w, mode)
                    if m >= t * raw[i] + (1 - t) * raw[j] - 1e-12: continue
                    rows += [nr, nr]; cols += [i, j]; vals += [t, 1 - t]; rhs.append(m); info.append((i, j, t, pats))
                    nr += 1
    if nr == 0: return raw.sum(), raw, []
    A = coo_matrix((vals, (rows, cols)), shape=(nr, E)).tocsr()
    res = linprog(-np.ones(E), A_ub=A, b_ub=np.array(rhs), bounds=[(0, raw[i]) for i in range(E)], method='highs')
    assert res.status == 0, res.message
    mu = -res.ineqlin.marginals
    act = [(mu[idx],) + info[idx] for idx in np.nonzero(mu > 1e-9)[0]]
    return -res.fun, res.x, act


def two_merge_formula(g):
    E = g * g * (g * g - 1) // 2
    return (g * g * (g - 1) ** 2 / 2 / math.sqrt(2) + g * g * (g - 1) * 0.5) / E


if __name__ == '__main__':
    name = sys.argv[1]
    nt = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    g, nodes, lab = game1.net(name)
    edges = game1.all_edges(nodes)
    tgrid = [i / (nt + 1) for i in range(1, nt + 1)]
    E = len(edges)
    print(f"net {name}: g={g}, E={E}, t-grid {nt}; two-merge formula {two_merge_formula(g):.6f}; 1/sqrt2 = {1/math.sqrt(2):.6f}")
    print("four-block lower bound at p=q=1/2, theta=pi/4 (per unit of raw): O1",
          float((np.array([.5, .5, 1 / math.sqrt(2), 1 / math.sqrt(2), 1.0]) @ dv((0, 1, 2, 3)).T).max()),
          " O2", float((np.array([.5, .5, 1 / math.sqrt(2), 1 / math.sqrt(2), 0.0]) @ dv((0, 1, 2, 3)).T).max()))
    ws = [(0.5, 0.5, 0.0), (0.5, 0.0, 0.5), (0.0, 0.5, 0.5), (1 / 3, 1 / 3, 1 / 3), (0.45, 0.45, 0.1), (0.4, 0.4, 0.2),
          (0.6, 0.2, 0.2), (0.5, 0.3, 0.2), (0.6, 0.4, 0.0), (0.7, 0.3, 0.0), (1, 0, 0)]
    if len(sys.argv) > 3 and sys.argv[3] == 'short':
        ws = [(0.5, 0.5, 0.0), (1 / 3, 1 / 3, 1 / 3), (0.45, 0.45, 0.1), (0.4, 0.4, 0.2), (0.6, 0.2, 0.2)]
    print("   w                       cert       H         O1        O2      raw")
    for w in ws:
        out = []
        for mode in ('cert', 'H', 'O1', 'O2'):
            v, y, act = solve(lab, edges, w, tgrid, mode)
            out.append(v / E)
        rawv = sum(sum(w[k] for k in range(3) if lab[a, k] != lab[c, k]) for (a, c) in edges) / E
        print(f"  {str(tuple(round(x,3) for x in w)):22s} " + " ".join(f"{v:.6f}" for v in out) + f"  {rawv:.4f}", flush=True)
