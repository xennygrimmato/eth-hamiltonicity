# Steps (2)-(3): cost of the D.1-style evaluation of the K_4 clique sum in Majdoddin's Signed-Network-Sum model.
# At a node t (level i = v2(t) < 3) the term F(t+alpha*zeta) is a network whose deformed constraint tensor
# Gamma = prod_e G_e(t+alpha*zeta) is, across the cut of matching i, the Kronecker product of the 4 crossing
# edges' matrices (internal edges sit on one side).  Hence its exact 2-adic rank modulo 2^{p_t} across the cut
# (= minimal number of names of the merged tables, i.e. 2^{naming bits}) is
#     R_t = #{(k_1..k_4) : sum_e v_e(k_e) < p_t},   v_e = Smith valuations of G_e(t+alpha*zeta)  [exact],
# and the precision p_t is the exact one of Lemma tapered-hermite for the multiplicity profile used.
# Output: log_N R_t (exponent of N of the dominant node), against 4 (flattening floor) and 23/6, 3.
import sys, math, itertools, json
from fractions import Fraction
from k4lib import *

import os
A = int(os.environ.get("K4A", "3")); K = Kernel(A); L = K.L
PBIG = 400
NODES = [t for t in range(-L, L) if t != 0 and v2(t) < 3]

def crossing(i): return [e for e in EDGES if lab(e[0], A)[i] != lab(e[1], A)[i]]

def profiles(lam, zeta=1):
    """per node t: list of 4 valuation-count vectors (one per crossing edge) for one packet with lam wires"""
    out = {}
    for t in NODES:
        i = v2(t); T = Fraction(t + K.alpha * zeta); vecs = []
        for e in crossing(i):
            sv = smith_vals_mod(edge_matrix(e, A, lam, T, K, P=PBIG), PBIG)
            assert max(sv) < PBIG
            c = [0] * (max(sv) + 1)
            for x in sv: c[x] += 1
            vecs.append(c)
        out[t] = vecs
    return out

def conv(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y: r[i + j] += x * y
    return r

def powconv(a, k):
    r = [1]
    for _ in range(k): r = conv(r, a)
    return r

def cumul(vecs, kpk):
    tot = [1]
    for c in vecs: tot = conv(tot, powconv(c, kpk))
    cs = [0]; s = 0
    for x in tot: s += x; cs.append(s)
    return cs   # cs[P] = #tuples with total valuation < P

def R_at(cs, P):
    if P <= 0: return 0
    return cs[min(P, len(cs) - 1)]

def evaluate(prof, kpk, lam_tot, qlev, p):
    """returns max over nodes of log2 R_t / lam_tot, and per-level details"""
    cum = {t: cumul(prof[t], kpk) for t in NODES}
    hp, Q = hermite_precisions(A, qlev, p)
    det = {}
    worst = 0.0
    for t, (i, qt, vE, pt) in hp.items():
        R = R_at(cum[t], pt)
        lg = math.log2(R) / lam_tot if R > 0 else 0
        worst = max(worst, lg)
        det.setdefault(i, []).append((t, qt, vE, pt, round(lg, 4), len(cum[t]) - 2))
    return worst, det, Q

if __name__ == "__main__":
    res = {}
    print(f"A={A} L={L} alpha={K.alpha}; nodes used: levels 0,1,2 = matchings rows/cols/diagonals; deg F <= M(2L-1), M = 6*lam")
    # per-packet profiles for lam = 1..4
    PROF = {lam: profiles(lam) for lam in (1, 2, 3, 4)}
    # zeta independence check
    pz = profiles(4, zeta=3)
    print("Smith profiles identical for zeta=1 and zeta=3:", all(pz[t] == PROF[4][t] for t in NODES))
    for t in (1, 3, 2, 6, 4):
        print(f"  t={t:3d} level {v2(t)}: per-edge Smith valuations (lam=4, one packet):",
              [[v for v, c in enumerate(vec) for _ in range(c)] for vec in PROF[4][t]])
    cases = [(1, 1), (2, 1), (3, 1), (4, 1), (4, 2), (4, 4), (4, 8), (4, 16), (4, 32)]
    print("\n=== (A) D.1's own taper: u=3, h=ceil(3M/u)=M, q(i)=h(u-i) ===")
    print(" lam  N        Sum q  deg-bound | worst log_N R_t (p=1) | (p=6lam+1) | max total valuation per level")
    for (lp, k) in cases:
        lam = lp * k; M = 6 * lam; h = math.ceil(3 * M / 3)
        q = {0: 3 * h, 1: 2 * h, 2: h}
        w1, d1, Q = evaluate(PROF[lp], k, lam, q, 1)
        w2, d2, _ = evaluate(PROF[lp], k, lam, q, 6 * lam + 1)
        mx = {i: max(x[5] for x in d1[i]) for i in d1}
        minpt = {i: min(x[3] for x in d1[i]) for i in d1}
        print(f" {lam:4d} 2^{lam:<4d} {Q:6d} {M*(2*L-1):6d} | {w1:.4f} | {w2:.4f} | maxval {mx}  min p_t {minpt}")
        res[f"taper_lam{lam}"] = (w1, w2)
    print("\n=== (B) best uniform-per-level multiplicities (q0,q1,q2), subject to Sum q_t > deg F = M(2L-1) ===")
    print(" lam  N    best worst log_N R_t (p=1)  at (q0,q1,q2)  [exhaustive grid]")
    for (lp, k) in cases[:7]:
        lam = lp * k; M = 6 * lam; deg = M * (2 * L - 1)
        cum = {t: cumul(PROF[lp][t], k) for t in NODES}
        best = (9e9, None)
        step = max(1, lam // 4)
        rng = range(0, 2 * deg // 8 + 2, step)
        for q0 in rng:
            for q1 in rng:
                rem = deg + 1 - 8 * q0 - 4 * q1
                q2 = max(0, -(-rem // 2))
                if 8 * q0 + 4 * q1 + 2 * q2 <= deg: continue
                qlev = {0: q0, 1: q1, 2: q2}
                hp, Q = hermite_precisions(A, qlev, 1)
                w = 0
                for t, (i, qt, vE, pt) in hp.items():
                    R = R_at(cum[t], pt); w = max(w, math.log2(R) / lam if R else 0)
                    if w >= best[0]: break
                if w < best[0]: best = (w, (q0, q1, q2))
        print(f" {lam:4d} 2^{lam:<4d} {best[0]:.4f}  at {best[1]}")
        res[f"opt_lam{lam}"] = best
    print("\n=== (C) hypothetical: same nodes/precisions but a deformation of total degree D = c*lam (not realisable by")
    print("    D.1's kernel, whose degree is 90*lam); smallest worst exponent over (q0,q1,q2) with Sum q_t > D, lam = 64 ===")
    lp, k = 4, 16; lam = 64
    cum = {t: cumul(PROF[lp][t], k) for t in NODES}
    for c in (90, 56, 40, 30, 24, 20, 16, 12, 8):
        deg = c * lam; best = (9e9, None)
        rng = range(0, deg // 4 + 2, 4)
        for q0 in rng:
            for q1 in rng:
                rem = deg + 1 - 8 * q0 - 4 * q1
                q2 = max(0, -(-rem // 2))
                qlev = {0: q0, 1: q1, 2: q2}
                hp, Q = hermite_precisions(A, qlev, 1)
                w = 0
                for t, (i, qt, vE, pt) in hp.items():
                    R = R_at(cum[t], pt); w = max(w, math.log2(R) / lam if R else 0)
                    if w >= best[0]: break
                if w < best[0]: best = (w, (q0, q1, q2))
        print(f"  D = {c:3d}*lam : worst log_N R_t = {best[0]:.4f} at {best[1]}")
        res[f"hyp_c{c}"] = best
    json.dump(res, open("k4_cost.json", "w"), indent=1, default=str)
