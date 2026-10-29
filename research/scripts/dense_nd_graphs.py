#!/usr/bin/env python3
"""dense_nd_graphs.py -- Corollaries for 0/1 graphs: G = blow-up of an r-vertex type graph H (loops = clique classes)
with a sparse set S of edited vertex pairs (added or removed edges).  This is "neighbourhood diversity <= r up to
|S| edge edits".  Checks, exactly, against brute force (n <= 9):

 (HC-rank)    #HC(G) = HC(A_G)/2 computed by Theorem 1 (I3) with U = M B, V = M (M = class indicator, rank <= r);
 (HC-profile) the class-profile form:  #HC(G) = sum_{F lin. forest of S} D^F Phi_H(prof F) + sum_{F = HC of S} D^F,
              D_e = +1 (added) / -1 (removed); prof F = (#F-isolated vertices per class, #paths per unordered
              endpoint-class pair); Phi_H(prof) = undirected completions, by a DP over unit counts (n^{O(r^2)} profiles);
 (PM-profile) #PM(G) = sum_{M matching of S} D^M PM_H(class counts of V - V(M)),
              PM_H(c) = sum_t prod_a multinom(c_a; 2t_aa, (t_ab)_b) prod_{a<b} t_ab! prod_a (2t_aa-1)!!   (closed form).
"""
import itertools, random, sys
from functools import lru_cache
from math import factorial
sys.path.insert(0, __import__('os').path.dirname(__file__))
from dense_lib import *
from dense_lowrank_hc import I3


def brute_pm(A):
    n = len(A)
    def rec(free):
        if not free: return 1
        i = free[0]; s = 0
        for k in range(1, len(free)):
            j = free[k]
            if A[i][j]:
                s += A[i][j] * rec(free[1:k] + free[k + 1:])
        return s
    return rec(list(range(n))) if n % 2 == 0 else 0


def und_lin_forests(edges, n):
    """undirected edge subsets with max degree <= 2; returns (F, kind) kind in {'forest','ham','cyclic'}"""
    res = []
    def rec(k, F, deg):
        if k == len(edges):
            res.append(list(F)); return
        rec(k + 1, F, deg)
        i, j = edges[k]
        if deg[i] < 2 and deg[j] < 2:
            deg[i] += 1; deg[j] += 1; F.append((i, j))
            rec(k + 1, F, deg)
            F.pop(); deg[i] -= 1; deg[j] -= 1
    rec(0, [], [0] * n)
    return res


def classify(F, n):
    adj = {v: [] for v in range(n)}
    for i, j in F:
        adj[i].append(j); adj[j].append(i)
    seen, comps = set(), []
    for v in range(n):
        if v in seen: continue
        stack, comp = [v], []
        seen.add(v)
        while stack:
            x = stack.pop(); comp.append(x)
            for y in adj[x]:
                if y not in seen: seen.add(y); stack.append(y)
        comps.append(comp)
    paths = []
    for comp in comps:
        ecount = sum(len(adj[x]) for x in comp) // 2
        if ecount >= len(comp):          # cycle
            if len(comp) == n: return 'ham', None
            return 'cyclic', None
        ends = [x for x in comp if len(adj[x]) <= 1]
        paths.append((ends[0], ends[-1]) if len(comp) > 1 else (comp[0], comp[0]))
    return 'forest', paths


def Phi_H(B, r, prof_trivial, prof_paths):
    """undirected Hamiltonian completions; prof_trivial[i], prof_paths[(a,b)] a<=b."""
    types = [('t', i) for i in range(r)] + [('p', a, b) for a in range(r) for b in range(a, r)]
    def orients(tp):
        if tp[0] == 't': return [(tp[1], tp[1])]
        a, b = tp[1], tp[2]
        return [(a, b), (b, a)]            # for a == b: two distinct orientations
    c0 = tuple([prof_trivial[i] for i in range(r)] + [prof_paths.get((a, b), 0) for a in range(r) for b in range(a, r)])
    N = sum(c0)
    @lru_cache(maxsize=None)
    def f(c, j, s):
        if sum(c) == 0: return B[j][s]
        tot = 0
        for k, tp in enumerate(types):
            if c[k] == 0: continue
            c2 = c[:k] + (c[k] - 1,) + c[k + 1:]
            for (s2, e2) in orients(tp):
                if B[j][s2]: tot += c[k] * f(c2, e2, s)
        return tot
    closed = 0
    for k, tp in enumerate(types):
        if c0[k] == 0: continue
        c2 = c0[:k] + (c0[k] - 1,) + c0[k + 1:]
        for (s, e) in orients(tp):
            closed += c0[k] * f(c2, e, s)
    assert closed % (2 * N) == 0
    return closed // (2 * N)


def PM_H(B, r, c):
    pairs = [(a, b) for a in range(r) for b in range(a, r) if B[a][b]]
    tot = 0
    def rec(k, t, rem):
        nonlocal tot
        if k == len(pairs):
            if any(rem): return
            pr = 1
            for a in range(r):
                parts = [2 * t.get((a, a), 0)] + [t.get((min(a, b), max(a, b)), 0) for b in range(r) if b != a]
                m = factorial(c[a])
                for p in parts: m //= factorial(p)
                pr *= m
                taa = t.get((a, a), 0)
                df = 1
                for q in range(1, 2 * taa, 2): df *= q
                pr *= df
            for (a, b), v in t.items():
                if a < b: pr *= factorial(v)
            tot += pr
            return
        a, b = pairs[k]
        mx = rem[a] // 2 if a == b else min(rem[a], rem[b])
        for v in range(mx + 1):
            rem2 = list(rem)
            if a == b: rem2[a] -= 2 * v
            else: rem2[a] -= v; rem2[b] -= v
            t[(a, b)] = v
            rec(k + 1, t, rem2)
        del t[(a, b)]
    rec(0, {}, list(c))
    return tot


def instance(rng, n, r, m):
    while True:
        B = [[0] * r for _ in range(r)]
        for a in range(r):
            for b in range(a, r):
                B[a][b] = B[b][a] = int(rng.random() < 0.7)
        if sum(map(sum, B)) >= 2: break
    cls = [rng.randrange(r) for _ in range(n)]
    L = [[0 if i == j else B[cls[i]][cls[j]] for j in range(n)] for i in range(n)]
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    S = rng.sample(pairs, m)
    G = [row[:] for row in L]
    for i, j in S:
        G[i][j] = G[j][i] = 1 - G[i][j]
    return B, cls, L, S, G


def main():
    rng = random.Random(7)
    allok = True
    cases = [(6, 2, 4), (7, 2, 5), (8, 2, 6), (7, 3, 5), (8, 3, 6), (9, 3, 6), (8, 3, 8), (9, 2, 7), (6, 3, 6), (8, 2, 9), (8, 4, 6), (9, 4, 7), (7, 4, 6), (8, 3, 10), (9, 3, 9)]
    for (n, r, m) in cases:
        B, cls, L, S, G = instance(rng, n, r, m)
        hc = hc_dir_brute(G) // 2
        pm = brute_pm(G)
        M = [[1 if cls[i] == a else 0 for a in range(r)] for i in range(n)]
        Uf = [[B[cls[i]][a] for a in range(r)] for i in range(n)]
        D = [[0 if i == j else G[i][j] - L[i][j] for j in range(n)] for i in range(n)]
        hr = I3(n, r, Uf, M, D) if n <= 8 else None
        # profile form
        edges = [(i, j) for (i, j) in S]
        tot_hc, tot_pm = 0, 0
        for F in und_lin_forests(edges, n):
            sgn = 1
            for i, j in F: sgn *= D[i][j]
            kind, paths = classify(F, n)
            if kind == 'ham': tot_hc += sgn; continue
            if kind == 'cyclic': continue
            triv = [0] * r; pp = {}
            for (u, w) in paths:
                if u == w: triv[cls[u]] += 1
                else:
                    key = tuple(sorted((cls[u], cls[w]))); pp[key] = pp.get(key, 0) + 1
            tot_hc += sgn * Phi_H(B, r, triv, pp)
            if len({v for e in F for v in e}) == 2 * len(F):   # F is a matching
                c = [0] * r
                used = {v for e in F for v in e}
                for v in range(n):
                    if v not in used: c[cls[v]] += 1
                tot_pm += sgn * PM_H(B, r, c)
        ok = (tot_hc == hc) and (tot_pm == pm) and (hr is None or hr == 2 * hc)
        allok &= ok
        print(f"n={n} r={r} |S|={m}: #HC={hc} profile={tot_hc} rank-form/2={None if hr is None else hr//2}  "
              f"#PM={pm} profile={tot_pm}  {'PASS' if ok else 'FAIL'}")
    print("ALL PASS" if allok else "SOME FAIL")


if __name__ == "__main__":
    main()
