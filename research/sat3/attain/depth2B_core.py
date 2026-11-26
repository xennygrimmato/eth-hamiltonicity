#!/usr/bin/env python3
"""Depth-2 certified game, type B (attain-notes.md, section 11): two level-1 pieces whose hub-hub bonds are crossed.

Strategy F = (P1, P2; t1, t2, u).
  P1: wires e1 = (a1, c1) [p1 = t1 bits] and e1' = (b1, d1) [q1 = 1 - t1], adversary angle th1:
      R1 = sqrt(2(p1^2 + q1^2)), certified ranks r_c = min(R1 cos th1, p1+q1) (cut c = a1 b1 | c1 d1),
      r_b = min(R1 sin th1, p1+q1) (cut b = a1 d1 | b1 c1).
  P2: wires e2 = (a2, c2) [p2 = u t2] and e2' = (b2, d2) [q2 = u (1 - t2)], angle th2, same conventions.
  After seeing (th1, th2) the cover either STOPS (each piece realised at level 1 per merge, cost table of section 1.2,
  game1.consts), or commits to a cut of each piece (four choices: hubs O1 | O1' with bond r1, O2 | O2' with bond r2)
  and crosses the two hub-hub bonds B1 = O1-O1' and B2 = O2-O2': adversary angle th3,
      R3 = sqrt(2(r1^2 + r2^2)), rho = min(R3 cos th3, r1 + r2) across O1 O2 | O1' O2'   (cut c'),
                                 rho' = min(R3 sin th3, r1 + r2) across O1 O2' | O1' O2  (cut b').
  Leaf (one merge): the tree  legs -> O1 -(r1)- U -(rho)- U' -(r1)- O1' <- legs,  O2 -(r2)- U, O2' -(r2)- U'
  (cut c'), or O2 at U', O2' at U (cut b'); cost = exact minimum 0-extension of the six hubs to the groups
  (tree DP), second cut chosen per merge:  cost_k = min(M_k, Sc_k + rho, Sb_k + rho').
  val_w(F) = max_{th1,th2} min( stop1(th1) + stop2(th2),  min_{cuts} max_{th3} sum_k w_k cost_k ).
Everything here is numba; the drivers are depth2B_run.py (LP / constraint generation) and depth2B_tests.py.
"""
import math, heapq
import numpy as np
from numba import njit, prange

SQ2 = math.sqrt(2.0)
HALFPI = math.pi / 2


# ---------------------------------------------------------------- level-1 piece (cost table of section 1.2)
@njit(cache=True)
def piece_consts(la, lb, lc, ld, p, q, g):
    """(K, Ac, Ab) with K = min(S, A3 + 2 min(p,q)); identical to game1.consts (hubs range over all g groups)."""
    S = 1e18
    for o in range(g):
        v = (p if la != o else 0.0) + (q if lb != o else 0.0) + (p if lc != o else 0.0) + (q if ld != o else 0.0)
        if v < S:
            S = v
    Ac = 1e18; Ab = 1e18; A3 = 1e18
    for o in range(g):
        for o2 in range(g):
            if o == o2:
                continue
            vc = (p if la != o else 0.0) + (q if lb != o else 0.0) + (p if lc != o2 else 0.0) + (q if ld != o2 else 0.0)
            vb = (p if la != o else 0.0) + (q if ld != o else 0.0) + (q if lb != o2 else 0.0) + (p if lc != o2 else 0.0)
            v3 = (p if la != o else 0.0) + (p if lc != o else 0.0) + (q if lb != o2 else 0.0) + (q if ld != o2 else 0.0)
            if vc < Ac: Ac = vc
            if vb < Ab: Ab = vb
            if v3 < A3: A3 = v3
    K = min(S, A3 + 2.0 * min(p, q))
    return K, Ac, Ab


@njit(cache=True)
def stop_eval(C, w, p, q, th):
    """sum_k w_k min(K, Ac + r, Ab + r'), C[k] = (K, Ac, Ab)."""
    R = math.sqrt(2.0 * (p * p + q * q)); cap = p + q
    r = min(R * math.cos(th), cap); rp = min(R * math.sin(th), cap)
    tot = 0.0
    for k in range(3):
        tot += w[k] * min(C[k, 0], min(C[k, 1] + r, C[k, 2] + rp))
    return tot


@njit(cache=True)
def _three_branch_max(C, w, R, cap, out_th):
    """exact max over th in [0, pi/2] of sum_k w_k min(C[k,0], C[k,1] + min(R cos, cap), C[k,2] + min(R sin, cap)).
    Candidates: endpoints, all breakpoints, stationary points of a cos + b sin. Returns (max, argmax)."""
    cand = np.empty(80); n = 0
    cand[0] = 0.0; cand[1] = HALFPI; cand[2] = math.pi / 4; n = 3
    if R <= 0.0:
        tot = 0.0
        for k in range(3):
            tot += w[k] * min(C[k, 0], min(C[k, 1], C[k, 2]))
        out_th[0] = 0.0
        return tot
    xs = np.empty(2 + 7 * 3); nx = 0
    # acos / asin candidates
    x = cap / R
    if 0.0 <= x <= 1.0:
        cand[n] = math.acos(x); n += 1; cand[n] = math.asin(x); n += 1
    for k in range(3):
        K, A, B = C[k, 0], C[k, 1], C[k, 2]
        x = (K - A) / R
        if 0.0 <= x <= 1.0:
            cand[n] = math.acos(x); n += 1
        x = (K - B) / R
        if 0.0 <= x <= 1.0:
            cand[n] = math.asin(x); n += 1
        x = (B - A) / (R * SQ2)
        if -1.0 <= x <= 1.0:
            th = math.acos(x) - math.pi / 4
            if 0.0 <= th <= HALFPI:
                cand[n] = th; n += 1
        x = (A + cap - B) / R
        if 0.0 <= x <= 1.0:
            cand[n] = math.asin(x); n += 1
        x = (B + cap - A) / R
        if 0.0 <= x <= 1.0:
            cand[n] = math.acos(x); n += 1
    for b0 in range(3):
        for b1 in range(3):
            for b2 in range(3):
                a = 0.0; b = 0.0
                if b0 == 1: a += w[0]
                if b0 == 2: b += w[0]
                if b1 == 1: a += w[1]
                if b1 == 2: b += w[1]
                if b2 == 1: a += w[2]
                if b2 == 2: b += w[2]
                if a > 0.0 and b > 0.0:
                    cand[n] = math.atan2(b, a); n += 1
    best = -1e18; bth = 0.0
    for i in range(n):
        th = cand[i]
        r = min(R * math.cos(th), cap); rp = min(R * math.sin(th), cap)
        tot = 0.0
        for k in range(3):
            tot += w[k] * min(C[k, 0], min(C[k, 1] + r, C[k, 2] + rp))
        if tot > best:
            best = tot; bth = th
    out_th[0] = bth
    return best


@njit(cache=True)
def stop_max(C, w, p, q, out_th):
    return _three_branch_max(C, w, math.sqrt(2.0 * (p * p + q * q)), p + q, out_th)


# ---------------------------------------------------------------- the type-B leaf
@njit(cache=True)
def hub_f(l1, b1, l2, b2, r, g, out):
    """cost of the subtree {hub O with legs (l1,b1),(l2,b2)} as a function of its parent's group h:
    min(move both legs to h, best place for O + bond r)."""
    mvmin = 0.0 if l1 == l2 else min(b1, b2)
    for h in range(g):
        mv = (b1 if l1 != h else 0.0) + (b2 if l2 != h else 0.0)
        out[h] = min(mv, mvmin + r)


@njit(cache=True)
def leaf_consts(L, p1, q1, p2, q2, cut1, cut2, r1, r2, g, f1, f1p, f2, f2p):
    """L = labels (a1,b1,c1,d1,a2,b2,c2,d2) under one merge. cut = 0 (c) or 1 (b). Returns (M, Sc, Sb)."""
    if cut1 == 0:
        hub_f(L[0], p1, L[1], q1, r1, g, f1); hub_f(L[2], p1, L[3], q1, r1, g, f1p)
    else:
        hub_f(L[0], p1, L[3], q1, r1, g, f1); hub_f(L[1], q1, L[2], p1, r1, g, f1p)
    if cut2 == 0:
        hub_f(L[4], p2, L[5], q2, r2, g, f2); hub_f(L[6], p2, L[7], q2, r2, g, f2p)
    else:
        hub_f(L[4], p2, L[7], q2, r2, g, f2); hub_f(L[5], q2, L[6], p2, r2, g, f2p)
    M = 1e18; A = 1e18; B = 1e18; A2 = 1e18; B2 = 1e18
    for h in range(g):
        x = f1[h] + f1p[h] + f2[h] + f2p[h]
        if x < M: M = x
        x = f1[h] + f2[h]
        if x < A: A = x
        x = f1p[h] + f2p[h]
        if x < B: B = x
        x = f1[h] + f2p[h]
        if x < A2: A2 = x
        x = f1p[h] + f2[h]
        if x < B2: B2 = x
    return M, A + B, A2 + B2


@njit(cache=True)
def nest_val(LL, p1, q1, p2, q2, cut1, cut2, r1, r2, g, w, C, f1, f1p, f2, f2p, exact, out_th):
    """max over th3 (exact if exact else lower bound at th3 = pi/4) of sum_k w_k min(M, Sc + rho, Sb + rho')."""
    for k in range(3):
        M, Sc, Sb = leaf_consts(LL[k], p1, q1, p2, q2, cut1, cut2, r1, r2, g, f1, f1p, f2, f2p)
        C[k, 0] = M; C[k, 1] = Sc; C[k, 2] = Sb
    R3 = math.sqrt(2.0 * (r1 * r1 + r2 * r2)); cap = r1 + r2
    if exact:
        return _three_branch_max(C, w, R3, cap, out_th)
    rr = R3 / SQ2  # <= cap always
    tot = 0.0
    for k in range(3):
        tot += w[k] * min(C[k, 0], min(C[k, 1], C[k, 2]) + rr)
    return tot


@njit(cache=True)
def F_point(LL, p1, q1, p2, q2, C1, C2, w, g, th1, th2, exact, work):
    """min over the cover's options at adversary angles (th1, th2): stop, or one of the four cut pairs (each max over th3).
    work: tuple of scratch arrays."""
    C, f1, f1p, f2, f2p, oth = work
    R1 = math.sqrt(2.0 * (p1 * p1 + q1 * q1)); R2 = math.sqrt(2.0 * (p2 * p2 + q2 * q2))
    best = stop_eval(C1, w, p1, q1, th1) + stop_eval(C2, w, p2, q2, th2)
    rc1 = min(R1 * math.cos(th1), p1 + q1); rb1 = min(R1 * math.sin(th1), p1 + q1)
    rc2 = min(R2 * math.cos(th2), p2 + q2); rb2 = min(R2 * math.sin(th2), p2 + q2)
    for cut1 in range(2):
        r1 = rc1 if cut1 == 0 else rb1
        for cut2 in range(2):
            r2 = rc2 if cut2 == 0 else rb2
            v = nest_val(LL, p1, q1, p2, q2, cut1, cut2, r1, r2, g, w, C, f1, f1p, f2, f2p, exact, oth)
            if v < best:
                best = v
    return best


@njit(cache=True)
def make_work(g):
    return (np.empty((3, 3)), np.empty(g), np.empty(g), np.empty(g), np.empty(g), np.empty(1))


@njit(cache=True)
def labels8(LAB, a1, b1, c1, d1, a2, b2, c2, d2):
    LL = np.empty((3, 8), dtype=np.int64)
    for k in range(3):
        LL[k, 0] = LAB[a1, k]; LL[k, 1] = LAB[b1, k]; LL[k, 2] = LAB[c1, k]; LL[k, 3] = LAB[d1, k]
        LL[k, 4] = LAB[a2, k]; LL[k, 5] = LAB[b2, k]; LL[k, 6] = LAB[c2, k]; LL[k, 7] = LAB[d2, k]
    return LL


# ---------------------------------------------------------------- per-pair level-1 tables
@njit(cache=True, parallel=True)
def pair_tables(LAB, EA, EB, PE, TG, w, g):
    """for every pair (e, e') = PE[i] and ratio t = TG[j] (p = t on e, q = 1 - t on e'; unit total):
    consts PC[i, j, k, :], level-1 max PM[i, j] and a maximiser PT[i, j]."""
    nP = PE.shape[0]; nT = TG.shape[0]
    PC = np.empty((nP, nT, 3, 3)); PM = np.empty((nP, nT)); PT = np.empty((nP, nT))
    for i in prange(nP):
        e, f = PE[i, 0], PE[i, 1]
        a, c, b, d = EA[e], EB[e], EA[f], EB[f]
        oth = np.empty(1)
        for j in range(nT):
            p = TG[j]; q = 1.0 - p
            for k in range(3):
                K, Ac, Ab = piece_consts(LAB[a, k], LAB[b, k], LAB[c, k], LAB[d, k], p, q, g)
                PC[i, j, k, 0] = K; PC[i, j, k, 1] = Ac; PC[i, j, k, 2] = Ab
            PM[i, j] = stop_max(PC[i, j], w, p, q, oth)
            PT[i, j] = oth[0]
    return PC, PM, PT


# ---------------------------------------------------------------- stage-1 filter over all quadruples
@njit(cache=True)
def split_filter(LL, p1, q1, p2, q2, stop, th1, th2, priced_tol, g, w, work):
    """lower bound on val_w(F): min(stop at the level-1 maximisers (th1, th2), every nest option at (th1, th2)).
    Exact th3 maximisation, computed lazily: a nest option is evaluated exactly only if its cheap lower bound
    (th3 = pi/4) is below priced_tol; returns as soon as the bound is known to be < priced_tol."""
    C, f1, f1p, f2, f2p, oth = work
    if stop < priced_tol:
        return stop
    R1 = math.sqrt(2.0 * (p1 * p1 + q1 * q1)); R2 = math.sqrt(2.0 * (p2 * p2 + q2 * q2))
    rc1 = min(R1 * math.cos(th1), p1 + q1); rb1 = min(R1 * math.sin(th1), p1 + q1)
    rc2 = min(R2 * math.cos(th2), p2 + q2); rb2 = min(R2 * math.sin(th2), p2 + q2)
    L = stop
    for cut1 in range(2):
        r1 = rc1 if cut1 == 0 else rb1
        for cut2 in range(2):
            r2 = rc2 if cut2 == 0 else rb2
            v = nest_val(LL, p1, q1, p2, q2, cut1, cut2, r1, r2, g, w, C, f1, f1p, f2, f2p, False, oth)
            if v < priced_tol:
                v = nest_val(LL, p1, q1, p2, q2, cut1, cut2, r1, r2, g, w, C, f1, f1p, f2, f2p, True, oth)
                if v < L:
                    L = v
                if L < priced_tol:
                    return L
    return L


@njit(cache=True, parallel=True)
def filter_sweep(LAB, EA, EB, PE, P1idx, PC, PM, PT, TG, UG, w, yE, g, tol):
    """For every P1 in P1idx (indices into PE), every P2 in PE, every (t1, t2, u): the lower bound of split_filter;
    violation (priced - L) / (1 + u). Returns the best violation per (P1, P2) (values below tol are not exact)."""
    n1 = P1idx.shape[0]; nP = PE.shape[0]; nT = TG.shape[0]; nU = UG.shape[0]
    best = np.full((n1, nP), -1e9, dtype=np.float32)
    for ii in prange(n1):
        i = P1idx[ii]
        e1, e1p = PE[i, 0], PE[i, 1]
        work = make_work(g)
        for j in range(nP):
            e2, e2p = PE[j, 0], PE[j, 1]
            LL = labels8(LAB, EA[e1], EA[e1p], EB[e1], EB[e1p], EA[e2], EA[e2p], EB[e2], EB[e2p])
            bv = -1e9
            for t1i in range(nT):
                p1 = TG[t1i]; q1 = 1.0 - p1
                pr1 = p1 * yE[e1] + q1 * yE[e1p]
                for t2i in range(nT):
                    pr2u = TG[t2i] * yE[e2] + (1.0 - TG[t2i]) * yE[e2p]
                    for ui in range(nU):
                        u = UG[ui]
                        priced = pr1 + u * pr2u
                        ptol = priced - (1.0 + u) * tol
                        L = split_filter(LL, p1, q1, u * TG[t2i], u * (1.0 - TG[t2i]), PM[i, t1i] + u * PM[j, t2i],
                                         PT[i, t1i], PT[j, t2i], ptol, g, w, work)
                        viol = (priced - L) / (1.0 + u)
                        if viol > bv:
                            bv = viol
            best[ii, j] = bv
    return best


@njit(cache=True, parallel=True)
def stage2(LAB, EA, EB, PE, QI, QJ, PC, PM, PT, TG, UG, w, yE, g, tol, TH):
    """for candidate quadruples (QI[n], QJ[n]) and all splits: filter, then max of F over the grid TH x TH plus the
    level-1 maximisers (exact th3). Returns violation array [n, split] ((priced - gridmax)/(1+u), -1e9 if filtered)."""
    nq = QI.shape[0]; nT = TG.shape[0]; nU = UG.shape[0]; nS = nT * nT * nU
    out = np.full((nq, nS), -1e9)
    for n in prange(nq):
        i = QI[n]; j = QJ[n]
        e1, e1p = PE[i, 0], PE[i, 1]; e2, e2p = PE[j, 0], PE[j, 1]
        work = make_work(g)
        LL = labels8(LAB, EA[e1], EA[e1p], EB[e1], EB[e1p], EA[e2], EA[e2p], EB[e2], EB[e2p])
        C2 = np.empty((3, 3))
        for t1i in range(nT):
            p1 = TG[t1i]; q1 = 1.0 - p1
            for t2i in range(nT):
                for ui in range(nU):
                    u = UG[ui]
                    p2 = u * TG[t2i]; q2 = u * (1.0 - TG[t2i])
                    priced = p1 * yE[e1] + q1 * yE[e1p] + p2 * yE[e2] + q2 * yE[e2p]
                    ptol = priced - (1.0 + u) * tol
                    L = split_filter(LL, p1, q1, p2, q2, PM[i, t1i] + u * PM[j, t2i], PT[i, t1i], PT[j, t2i], ptol, g, w, work)
                    if L >= ptol:
                        continue
                    for k in range(3):
                        for m in range(3):
                            C2[k, m] = u * PC[j, t2i, k, m]
                    mx = L
                    for a in range(TH.shape[0] + 1):
                        th1 = TH[a] if a < TH.shape[0] else PT[i, t1i]
                        for b in range(TH.shape[0] + 1):
                            th2 = TH[b] if b < TH.shape[0] else PT[j, t2i]
                            v = F_point(LL, p1, q1, p2, q2, PC[i, t1i], C2, w, g, th1, th2, True, work)
                            if v > mx:
                                mx = v
                                if mx >= ptol:
                                    break
                        if mx >= ptol:
                            break
                    out[n, (t1i * nT + t2i) * nU + ui] = (priced - mx) / (1.0 + u)
    return out


# ---------------------------------------------------------------- strategy value on a grid, and certified bracket
@njit(cache=True)
def F_grid(LL, p1, q1, p2, q2, C1, C2, w, g, th1s, th2s):
    work = make_work(g)
    out = np.empty((th1s.shape[0], th2s.shape[0]))
    for a in range(th1s.shape[0]):
        for b in range(th2s.shape[0]):
            out[a, b] = F_point(LL, p1, q1, p2, q2, C1, C2, w, g, th1s[a], th2s[b], True, work)
    return out


@njit(cache=True)
def F_ub_box(LL, p1, q1, p2, q2, C1, C2, w, g, lo1, hi1, lo2, hi2, work):
    """certified upper bound of F on the box [lo1,hi1] x [lo2,hi2] by monotonicity:
    stop_i is a sum of min(K, Ac + r(th), Ab + r'(th)) with r decreasing and r' increasing in th, so on an interval it is
    <= min(K, Ac + r(lo), Ab + r'(hi)); every nest option is nondecreasing in (r1, r2) (each leaf cost is a minimum of
    sums with nonnegative coefficients of r1, r2 and rho, rho' = min(R3 cos/sin th3, r1 + r2), R3 increasing), so on the
    box it is <= its value at the largest r1 (lo1 for cut c, hi1 for cut b) and largest r2."""
    C, f1, f1p, f2, f2p, oth = work
    R1 = math.sqrt(2.0 * (p1 * p1 + q1 * q1)); R2 = math.sqrt(2.0 * (p2 * p2 + q2 * q2))
    rc1 = min(R1 * math.cos(lo1), p1 + q1); rb1 = min(R1 * math.sin(hi1), p1 + q1)
    rc2 = min(R2 * math.cos(lo2), p2 + q2); rb2 = min(R2 * math.sin(hi2), p2 + q2)
    best = 0.0
    for k in range(3):
        best += w[k] * min(C1[k, 0], min(C1[k, 1] + rc1, C1[k, 2] + rb1))
        best += w[k] * min(C2[k, 0], min(C2[k, 1] + rc2, C2[k, 2] + rb2))
    for cut1 in range(2):
        r1 = rc1 if cut1 == 0 else rb1
        for cut2 in range(2):
            r2 = rc2 if cut2 == 0 else rb2
            v = nest_val(LL, p1, q1, p2, q2, cut1, cut2, r1, r2, g, w, C, f1, f1p, f2, f2p, True, oth)
            if v < best:
                best = v
    return best


@njit(cache=True)
def F_bnb(LL, p1, q1, p2, q2, C1, C2, w, g, n0, tol, maxeval, th1star, th2star):
    """Branch and bound over (th1, th2) in [0, pi/2]^2, th3 maximised exactly in every evaluation.
    Lower bound: values at box centres (attained). Upper bound per box: F_ub_box (monotonicity in the bonds).
    Returns (lo, hi, th1, th2, nevals): lo = best value found, hi = certified upper bound on max F (hi - lo <= tol unless
    the evaluation cap was hit, in which case hi is the largest remaining box bound)."""
    work = make_work(g)
    lo = F_point(LL, p1, q1, p2, q2, C1, C2, w, g, th1star, th2star, True, work)
    a1 = th1star; a2 = th2star
    nev = 1
    h = HALFPI / n0
    heap = [(0.0, 0.0, 0.0, 0.0, 0.0)]
    heap.pop()
    for i in range(n0):
        for j in range(n0):
            l1 = i * h; l2 = j * h
            v = F_point(LL, p1, q1, p2, q2, C1, C2, w, g, l1 + 0.5 * h, l2 + 0.5 * h, True, work)
            ub = F_ub_box(LL, p1, q1, p2, q2, C1, C2, w, g, l1, l1 + h, l2, l2 + h, work)
            nev += 2
            if v > lo:
                lo = v; a1 = l1 + 0.5 * h; a2 = l2 + 0.5 * h
            heap.append((-ub, l1, l1 + h, l2, l2 + h))
    heapq.heapify(heap)
    hi = lo + tol
    while len(heap) > 0:
        nub, l1, u1, l2, u2 = heapq.heappop(heap)
        if -nub <= lo + tol:
            break
        if nev + 8 > maxeval:
            hi = -nub
            break
        m1 = 0.5 * (l1 + u1); m2 = 0.5 * (l2 + u2)
        for (b1, c1) in ((l1, m1), (m1, u1)):
            for (b2, c2) in ((l2, m2), (m2, u2)):
                v = F_point(LL, p1, q1, p2, q2, C1, C2, w, g, 0.5 * (b1 + c1), 0.5 * (b2 + c2), True, work)
                ub = F_ub_box(LL, p1, q1, p2, q2, C1, C2, w, g, b1, c1, b2, c2, work)
                nev += 2
                if v > lo:
                    lo = v; a1 = 0.5 * (b1 + c1); a2 = 0.5 * (b2 + c2)
                if ub > lo + tol:
                    heapq.heappush(heap, (-ub, b1, c1, b2, c2))
    if hi < lo + tol:
        hi = lo + tol
    return lo, hi, a1, a2, nev
