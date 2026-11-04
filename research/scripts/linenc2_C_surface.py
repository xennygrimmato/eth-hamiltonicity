"""Loophole 1(c): graphs cellularly embedded in an orientable surface (no crossings).

Theorem J (Johnson's quadratic form, local version).  Let G be cellularly embedded in the closed
orientable surface S_g by a rotation system.  Choose local edge directions at every vertex and a
vector field xi with even-index zeros inside faces (realised combinatorially by edge twists k_e,
solved over GF(2) so that every face boundary has odd winding).  Let W(C) = winding of the
directed cycle C relative to xi, computed LOCALLY as a sum of per-edge and per-corner
'north-passing' bits.  Then for every disjoint system x of directed cycles
        c(x) == W(x) + q(H x)   (mod 2),
where H x in H_1(S_g; Z/2) = (Z/2)^{2g} is the homology class (linear in x) and q is a quadratic
form on (Z/2)^{2g} refining the intersection form (nondegenerate polarisation).
Checks:
  (a) W(C) (sum of local north bits) == exact winding number mod 2;
  (b) for single cycles, 1+W(C) depends only on [C]  (q is well defined);
  (c) q is quadratic on H_1: a quadratic fit exists, and when every class of H_1 is realised by a
      simple cycle the fitted polarisation is alternating of full rank 2g (= intersection form);
  (d) c(x) == W(x) + q(Hx) on every vertex-disjoint union of directed cycles (all of them);
  (e) planar case g=0: c(x) == W(x) (no global term) -- included in (d);
  (f) ablation: c(x) == W(x) alone fails whenever g > 0 (some x).
"""
import sys, os
from fractions import Fraction as Fr
from math import floor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from linenc2_lib import *  # noqa

HALF = Fr(1, 2); NORTH = Fr(1, 4)


def wrap(a):  # into (-1/2, 1/2]
    a = a - floor(a)
    return a - 1 if a > HALF else a


def passes(a, R):
    """number of t in (a, a+R) (or (a+R, a)) with t == 1/4 mod 1."""
    lo, hi = (a, a + R) if R >= 0 else (a + R, a)
    # count integers j with lo < 1/4 + j < hi
    return max(0, (floor(hi - NORTH - Fr(1, 10**9)) - floor(lo - NORTH)))


def setup(n, edges, rng):
    inc = [[] for _ in range(n)]
    for k, (i, j) in enumerate(edges):
        inc[i].append(k); inc[j].append(k)
    rot = {}
    ang = {}
    for v in range(n):
        L = inc[v][:]; rng.shuffle(L); rot[v] = L
        d = len(L); ph = Fr(rng.randrange(1, 997), 997 * 7)
        for t, k in enumerate(L):
            ang[(v, k)] = Fr(t, d) + ph
            assert (ang[(v, k)] - NORTH) % 1 != 0 and (ang[(v, k)] + HALF - NORTH) % 1 != 0
    other = lambda k, v: edges[k][0] + edges[k][1] - v
    # faces: dart (u,k) = leave u along edge k. next dart: at v=other, take rotation predecessor of k
    darts = [(v, k) for v in range(n) for k in inc[v]]
    nxt = {}
    for (u, k) in darts:
        v = other(k, u); L = rot[v]; i = L.index(k)
        nxt[(u, k)] = (v, L[i - 1])
    faces, seen = [], set()
    for d in darts:
        if d in seen: continue
        f = []; x = d
        while x not in seen:
            seen.add(x); f.append(x); x = nxt[x]
        faces.append(f)
    return inc, rot, ang, faces, other


def edge_rot(ang, other, u, k, kk):
    v = other(k, u)
    a = ang[(u, k)]
    R = wrap(ang[(v, k)] + HALF - a)  # base rotation, then add twist
    tw = kk[k] if u < v else -kk[k]
    return a, R + tw


def corner_turn(ang, v, kin, kout):
    a = ang[(v, kin)] + HALF
    return a, wrap(ang[(v, kout)] - a)


def walk_data(ang, other, kk, dart_list):
    """dart_list: cyclic list of darts (u,k). returns (exact winding, north-bit sum)."""
    tot = Fr(0); nb = 0
    L = len(dart_list)
    for t in range(L):
        u, k = dart_list[t]
        a, R = edge_rot(ang, other, u, k, kk)
        tot += R; nb += passes(a, R)
        v, k2 = dart_list[(t + 1) % L]
        a, T = corner_turn(ang, v, k, k2)
        tot += T; nb += passes(a, T)
    assert tot.denominator == 1
    return int(tot), nb


rng = random.Random(4242)
fails = dict(a=0, b=0, c=0, d=0, twist_solvable=0)
abl = 0; st = dict(graphs=0, genus_hist={}, systems=0, cycles=0)
for trial in range(70):
    n = rng.randint(4, 8)
    m = rng.randint(n + 1, min(n * (n - 1) // 2, 2 * n + 2))
    edges = random_graph(n, m, rng, min_deg2=True)
    # connected?
    comp = {0}; ch = True
    while ch:
        ch = False
        for i, j in edges:
            if (i in comp) != (j in comp): comp |= {i, j}; ch = True
    if len(comp) < n: continue
    inc, rot, ang, faces, other = setup(n, edges, rng)
    g2 = 2 - (n - m + len(faces))
    g = g2 // 2
    st['graphs'] += 1; st['genus_hist'][g] = st['genus_hist'].get(g, 0) + 1
    # twists: face winding must be odd
    kk0 = [0] * m
    rows, rhs = [], []
    for f in faces:
        w, _ = walk_data(ang, other, kk0, f)
        mask = 0
        for (u, k) in f: mask ^= 1 << k
        rows.append(mask); rhs.append((w + 1) % 2)
    sol = gf2_solve(rows, rhs)
    if sol is None:
        fails['twist_solvable'] += 1; continue
    kk = [(sol >> k) & 1 for k in range(m)]
    for f in faces:
        assert walk_data(ang, other, kk, f)[0] % 2 == 1
    # homology: cycle space mod face boundaries (edge masks); reduce to coordinates
    Bmasks = [sum(1 << k for (u, k) in f if sum(1 for (_, kx) in f if kx == k) == 1) for f in faces]
    # basis of boundary space
    def reduce_vec(v, basis):
        for h in sorted(basis, reverse=True):
            if (v >> h) & 1: v ^= basis[h]
        return v
    Bb = {}
    for b in Bmasks:
        b = reduce_vec(b, Bb)
        if b: Bb[b.bit_length() - 1] = b
        # re-reduce
    # homology coordinates: reduce cycle mask mod boundaries, then express in a basis of the quotient
    E = eid_map(edges)
    cyc = directed_simple_cycles(n, edges)
    def darts_of(c):
        return [(c[t], E[frozenset((c[t], c[(t + 1) % len(c)]))]) for t in range(len(c))]
    Q = {}  # quotient basis among reduced cycle vectors
    def hcoord(mask):
        r = reduce_vec(mask, Bb)
        return r
    reds = []
    for c in cyc:
        mask = sum(1 << k for (_, k) in darts_of(c))
        reds.append(hcoord(mask))
    # basis of span of reduced vectors (dimension should be 2g)
    HB = {}
    for r in reds:
        r2 = reduce_vec(r, HB)
        if r2: HB[r2.bit_length() - 1] = r2
    if len(HB) != 2 * g:
        # all of H_1 is generated by simple cycles for connected graphs
        fails['c'] += 1; continue
    piv = sorted(HB)
    # coordinates of r in basis HB (Gaussian with tracking)
    basis_list = []; track = {}
    for idx, h in enumerate(piv):
        pass
    def coords(r):
        # express r (already mod B) as combination of HB vectors; use elimination with tracking
        vec = r; co = 0
        changed = True
        for h in sorted(HB, reverse=True):
            if (vec >> h) & 1:
                vec ^= HB[h]; co ^= 1 << piv.index(h)
        assert vec == 0
        return co
    Wc, Hc = [], []
    for c, r in zip(cyc, reds):
        w, nb = walk_data(ang, other, kk, darts_of(c))
        st['cycles'] += 1
        if (w - nb) % 2: fails['a'] += 1
        Wc.append(nb % 2); Hc.append(coords(r))
    # (b) well defined
    qtab = {}
    for w, h in zip(Wc, Hc):
        val = (1 + w) % 2
        if qtab.setdefault(h, val) != val: fails['b'] += 1
    # (c) fit quadratic: q(h) = sum_i a_i h_i + sum_{i<j} b_ij h_i h_j
    D = 2 * g
    mons = [(i,) for i in range(D)] + [(i, j) for i in range(D) for j in range(i + 1, D)]
    rws, rh = [], []
    for h, val in qtab.items():
        mask = 0
        for t, mo in enumerate(mons):
            if all((h >> i) & 1 for i in mo): mask |= 1 << t
        rws.append(mask); rh.append(val)
    sq = gf2_solve(rws, rh) if mons else 0
    if sq is None:
        fails['c'] += 1; continue
    Bm = [[0] * D for _ in range(D)]
    for t, mo in enumerate(mons):
        if len(mo) == 2 and (sq >> t) & 1:
            Bm[mo[0]][mo[1]] = Bm[mo[1]][mo[0]] = 1
    if len(qtab) == 2 ** D:
        st['full_fit'] = st.get('full_fit', 0) + 1
        if gf2_rank(mat_to_rows(Bm)) != D: fails['c'] += 1
    else:
        st['underdetermined_fit'] = st.get('underdetermined_fit', 0) + 1
    def q(h):
        s = 0
        for t, mo in enumerate(mons):
            if (sq >> t) & 1 and all((h >> i) & 1 for i in mo): s ^= 1
        return s
    # (d) all vertex-disjoint unions of directed cycles
    vs = [sum(1 << v for v in c) for c in cyc]
    order = list(range(len(cyc)))
    def rec(start, used, W, H, cnt):
        global abl
        if cnt > 0:
            st['systems'] += 1
            if (cnt - W - q(H)) % 2: fails['d'] += 1
            if (cnt - W) % 2: abl += 1
        for i in range(start, len(cyc)):
            if not (vs[i] & used):
                rec(i + 1, used | vs[i], W + Wc[i], H ^ Hc[i], cnt + 1)
    rec(0, 0, 0, 0, 0)
print('stats:', st)
print('ablation W alone wrong on', abl, 'systems (must be > 0)')
for k, v in fails.items():
    print(f'check {k:15s}: {"PASS" if v == 0 else "FAIL"} ({v} failures)')
print('ALL PASS' if not any(fails.values()) and abl > 0 else 'SOME FAIL')
