"""dense_lib.py -- shared exact routines for the dense_* scripts (dense-structured.md).

Conventions: A is an n x n integer matrix, directed weighted Hamiltonian-cycle sum
    HC(A) = sum over directed Hamiltonian cycles C of prod_{(i,j) in C} A[i][j]   (diagonal never used).
L = U V^T (n x r factors), D = A - L off the diagonal (sparse).  A 'unit' of a directed linear
forest F is a maximal directed path (tail u, head w); an F-isolated vertex is the unit (v, v).
"""
import itertools
from fractions import Fraction
from math import factorial


def det(M):
    n = len(M)
    if n == 0:
        return Fraction(1)
    A = [[Fraction(x) for x in row] for row in M]
    d = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return Fraction(0)
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            if f:
                for k in range(c, n):
                    A[r][k] -= f * A[c][k]
    return d


def hc_dir_brute(A):
    """Directed weighted HC sum, brute force over (n-1)! cyclic orders."""
    n = len(A)
    if n < 2:
        return 0
    tot = 0
    for p in itertools.permutations(range(1, n)):
        seq = (0,) + p
        pr = 1
        for i in range(n):
            pr *= A[seq[i]][seq[(i + 1) % n]]
            if pr == 0:
                break
        tot += pr
    return tot


def arcs_of(D):
    n = len(D)
    return [(i, j) for i in range(n) for j in range(n) if i != j and D[i][j] != 0]


def dir_subsets(arcs, n):
    """All arc subsets with indeg, outdeg <= 1 (paths and directed cycles)."""
    out = []
    def rec(k, F, ind, outd):
        if k == len(arcs):
            out.append(list(F))
            return
        rec(k + 1, F, ind, outd)
        i, j = arcs[k]
        if not (outd >> i & 1) and not (ind >> j & 1):
            F.append((i, j))
            rec(k + 1, F, ind | (1 << j), outd | (1 << i))
            F.pop()
    rec(0, [], 0, 0)
    return out


def units(F, n, verts=None):
    """Return list of units (tail, head) if F (indeg,outdeg<=1) is acyclic, else None.
    verts: vertex set to cover (default all)."""
    verts = range(n) if verts is None else verts
    succ = {i: j for i, j in F}
    has_in = {j for _, j in F}
    res, seen = [], set()
    for v in verts:
        if v in has_in:
            continue
        u, w = v, v
        seen.add(w)
        while w in succ:
            w = succ[w]
            seen.add(w)
        res.append((u, w))
    covered = {v for v in verts}
    if seen != covered:   # some vertices only on cycles
        return None
    return res


def is_ham_dicycle(F, n):
    if len(F) != n or n < 2:
        return False
    succ = {i: j for i, j in F}
    v, steps = 0, 0
    while True:
        v = succ.get(v)
        steps += 1
        if v is None:
            return False
        if v == 0:
            return steps == n


def wprod(D, F):
    p = 1
    for i, j in F:
        p *= D[i][j]
    return p


# ---------- polynomials as dicts: exponent tuple -> coefficient ----------
def pmul(P, Q, trunc=None):
    R = {}
    for e1, c1 in P.items():
        for e2, c2 in Q.items():
            e = tuple(a + b for a, b in zip(e1, e2))
            if trunc is not None and not trunc(e):
                continue
            R[e] = R.get(e, 0) + c1 * c2
    return {e: c for e, c in R.items() if c != 0}


def padd(P, Q, s=1):
    R = dict(P)
    for e, c in Q.items():
        R[e] = R.get(e, 0) + s * c
    return {e: c for e, c in R.items() if c != 0}


def best_ec(N, r):
    """Eulerian circuits (cyclic sequences of distinguishable arcs) of the multigraph on [r] with arc
    multiplicities N[a][b]; BEST theorem.  0 if unbalanced, disconnected or empty."""
    out = [sum(N[a]) for a in range(r)]
    inn = [sum(N[b][a] for b in range(r)) for a in range(r)]
    if out != inn:
        return 0
    R = [a for a in range(r) if out[a] > 0]
    if not R:
        return 0
    w = R[0]
    rest = [a for a in R if a != w]
    Lap = [[(out[a] - N[a][a] if a == b else 0) - (N[a][b] if a != b else 0) for b in rest] for a in rest]
    t = det(Lap)
    pr = 1
    for a in R:
        pr *= factorial(out[a] - 1)
    return int(t) * pr


def in_arborescences(R):
    """All in-arborescences of the complete digraph on R rooted at min(R): dict child -> parent."""
    w = min(R)
    others = [a for a in R if a != w]
    res = []
    for pars in itertools.product(R, repeat=len(others)):
        par = dict(zip(others, pars))
        ok = True
        for a in others:
            seen, x = set(), a
            while x != w:
                if x in seen or par[x] == x:
                    ok = False
                    break
                seen.add(x)
                x = par[x]
            if not ok:
                break
        if ok:
            res.append(par)
    return res
