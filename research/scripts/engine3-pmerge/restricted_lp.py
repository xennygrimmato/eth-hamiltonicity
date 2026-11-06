"""restricted_lp.py -- cap of the 'select-then-bound' method with SCSH added, over every restriction H of Delta_3.
For H subset of the 9 nodes (edges outside H fixed, so f|_H = graph tensor of Delta_3[H]), the selected piece is the one
with large uniform quantum functional on parties X_j = restricted groups of a chosen merge (or the party lemma: parties from
several merges), giving h(X_j) >= e(X_j, H \\ X_j) for all j (no over-full pieces).  Then subadditivity + complement
symmetry + leg bounds + SCSH on all 4-party coarsenings of H bound the other cuts, and c_k(A) >= c_k(A|_H) >= cut bounds.
Reported: min over feasible h of (c_r + c_c + c_d)/3 (the uniform-q value of that piece) and of min_k c_k, for
(a) selection by rows, (b) by columns, (c) by diagonals, (d) party lemma with one party per merge where possible.
H ranges over all subsets up to the symmetry group of Delta_3 fixing the triangle class (|H| >= 4)."""
import itertools, numpy as np, sys
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix
nodes = [(r, c) for r in range(3) for c in range(3)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
MER = {'r': lambda v: v[0], 'c': lambda v: v[1], 'd': lambda v: (v[0] - v[1]) % 3}
# symmetry group: maps of Z_3^2 preserving the three merge classes (as a set) and the anti-diagonal class
def affine_maps():
    maps = []
    for a, b, c, d in itertools.product(range(3), repeat=4):
        if (a * d - b * c) % 3 == 0: continue
        for e, f in itertools.product(range(3), repeat=2):
            maps.append(lambda v, a=a, b=b, c=c, d=d, e=e, f=f: ((a * v[0] + b * v[1] + e) % 3, (c * v[0] + d * v[1] + f) % 3))
    good = []
    for m in maps:
        img = {frozenset(m(v) for v in nodes if (v[0] + v[1]) % 3 == s) for s in range(3)}
        if img != {frozenset(v for v in nodes if (v[0] + v[1]) % 3 == s) for s in range(3)}: continue
        cls = lambda g: {frozenset(v for v in nodes if g(v) == x) for x in range(3)}
        imgs = [{frozenset(m(v) for v in C) for C in cls(g)} for g in MER.values()]
        if all(any(im == cls(g) for g in MER.values()) for im in imgs): good.append(m)
    return good
SYM = affine_maps()
def canon(H):
    return min(tuple(sorted(m(v) for v in H)) for m in SYM)

def solve(H, select):
    H = list(H); k = len(H); loc = {v: i for i, v in enumerate(H)}; FULL = (1 << k) - 1
    E_H = [(u, v) for (u, v) in edges if u in loc and v in loc]
    deg = {v: sum(1 for e in E_H if v in e) for v in H}
    def m(vs): return sum(1 << loc[v] for v in vs if v in loc)
    groups = {g: [m([v for v in H if MER[g](v) == x]) for x in range(3)] for g in MER}
    groups = {g: [G for G in Gs if G] for g, Gs in groups.items()}
    def ecross(S): return sum(1 for (u, v) in E_H if ((S >> loc[u]) & 1) != ((S >> loc[v]) & 1))
    pop = [bin(S).count('1') for S in range(1 << k)]
    NV = (1 << k) + 3; IR, IC, ID = (1 << k), (1 << k) + 1, (1 << k) + 2
    rows_A = []
    def add(co, rhs=0.0): rows_A.append((co, rhs))
    for S in range(1, 1 << k):
        rest = FULL & ~S; T = rest
        while T:
            if T > S: add({S | T: 1, S: -1, T: -1})
            T = (T - 1) & rest
    seen = set()
    for assign in itertools.product(range(4), repeat=k):
        A = B = C = Dd = 0
        for i, a in enumerate(assign):
            if a == 0: A |= 1 << i
            elif a == 1: B |= 1 << i
            elif a == 2: C |= 1 << i
            else: Dd |= 1 << i
        if not B or not C or not A: continue
        key = (A, min(B, C), max(B, C))
        if key in seen: continue
        seen.add(key)
        co = {}
        for S, v in ((B | C, 1), (A | B, -1), (A | C, -1)): co[S] = co.get(S, 0) + v
        add(co)
    for g, I in (('r', IR), ('c', IC), ('d', ID)):
        for G in groups[g]: add({G: 1, I: -1})
        add({**{G: 0.5 for G in groups[g]}, I: -1})
    M = lil_matrix((len(rows_A), NV)); b = np.zeros(len(rows_A))
    for i, (co, rhs) in enumerate(rows_A):
        for kk, v in co.items(): M[i, kk] += v
        b[i] = rhs
    E = lil_matrix((1 << (k - 1), NV)); j = 0
    for S in range(1 << k):
        if S < (FULL & ~S): E[j, S] = 1; E[j, FULL & ~S] = -1; j += 1
    # bounds: 0 <= h(S) <= legs(S) = sum of deg_H(v) (edges to fixed nodes are gone), h(empty)=0; selection lower bounds
    lower = {}
    for X in select:
        if X: lower[X] = max(lower.get(X, 0), ecross(X))
    bounds = [(lower.get(S, 0.0), float(sum(deg[v] for v in H if (S >> loc[v]) & 1))) for S in range(1 << k)] + [(0, None)] * 3
    bounds[0] = (0, 0)
    out = {}
    for lab, obj in (('unif', [IR, IC, ID]), ):
        c = np.zeros(NV)
        for I in obj: c[I] = 1 / 3
        r = linprog(c, A_ub=csr_matrix(M), b_ub=b, A_eq=csr_matrix(E[:j]), b_eq=np.zeros(j), bounds=bounds, method='highs')
        out[lab] = r.fun if r.status == 0 else None
        out['vec'] = tuple(round(r.x[I], 3) for I in (IR, IC, ID)) if r.status == 0 else None
    return out, groups

if __name__ == '__main__':
    best = {}
    seen = set()
    for size in range(9, 3, -1):
        for H in itertools.combinations(nodes, size):
            cH = canon(H)
            if cH in seen: continue
            seen.add(cH)
            Hl = list(H); loc = {v: i for i, v in enumerate(Hl)}
            def mm(vs): return sum(1 << loc[v] for v in vs if v in loc)
            sels = {}
            for g in MER:
                sels[g] = [mm([v for v in Hl if MER[g](v) == x]) for x in range(3)]
            # party lemma: one restricted group per merge, pairwise disjoint, covering as much as possible (try all triples)
            party = []
            for Gr, Gc, Gd in itertools.product(sels['r'], sels['c'], sels['d']):
                if Gr & Gc or Gr & Gd or Gc & Gd: continue
                party.append([Gr, Gc, Gd])
            results = []
            for lab, sel in [('rows', sels['r']), ('cols', sels['c']), ('diags', sels['d'])] + [(f'party{i}', p) for i, p in enumerate(party[:6])]:
                out, _ = solve(H, sel)
                if out['unif'] is not None: results.append((lab, round(out['unif'], 4), out['vec']))
            top = max(results, key=lambda t: t[1]) if results else None
            print(f'|H|={size} H={H}: best uniform-q bound {top}', flush=True)
            if top and (size not in best or top[1] > best[size][0]): best[size] = (top[1], H, top)
    print('\nbest per |H|:')
    for s in sorted(best): print(s, best[s])
