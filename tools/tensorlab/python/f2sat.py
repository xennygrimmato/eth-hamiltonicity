"""Exact restriction search over F_2 by SAT (python-sat), for tiny wire networks.

Question: do there exist F_2-linear maps A_p : F_2^{in_p} -> F_2^{out_p} with (x_p A_p) S = T, where S, T
are EPR-wire networks (graph tensors) on the same parties?  Entry of (x A) S at output o is
    XOR over bond assignments b of  AND_p A_p[o_p, in_p(b)],
which is encoded with Tseitin AND gates and XOR chains.

Usage:  python f2sat.py            (runs the self-tests and the K_{2,3} bond-dimension-2 question)
API:    solve_f2(nparties, supply, demand, solver="cadical153", time_limit=None) -> (status, maps|None)
"""
import itertools as it
import sys
import time

from pysat.formula import IDPool
from pysat.solvers import Solver


def legs(nparties, wires, p):
    return [(k, w[2]) for k, w in enumerate(wires) if p in (w[0], w[1])]


def local_dim(nparties, wires, p):
    d = 1
    for _, x in legs(nparties, wires, p):
        d *= x
    return d


def dense_support(nparties, wires):
    """Set of nonzero entries (tuples of local indices) of the graph tensor (0/1 entries)."""
    L = [legs(nparties, wires, p) for p in range(nparties)]
    out = set()
    for b in it.product(*[range(w[2]) for w in wires]):
        idx = []
        for p in range(nparties):
            loc = 0
            for (k, d) in L[p]:
                loc = loc * d + b[k]
            idx.append(loc)
        out.add(tuple(idx))
    return out


def solve_f2(nparties, supply, demand, solver="cadical153", time_limit=None, verbose=False):
    pool = IDPool()
    ind = [local_dim(nparties, supply, p) for p in range(nparties)]
    outd = [local_dim(nparties, demand, p) for p in range(nparties)]
    A = [[[pool.id(("A", p, o, i)) for i in range(ind[p])] for o in range(outd[p])] for p in range(nparties)]
    T = dense_support(nparties, demand)
    Ls = [legs(nparties, supply, p) for p in range(nparties)]
    bonds = list(it.product(*[range(w[2]) for w in supply]))
    bond_in = [[0] * nparties for _ in bonds]
    for bi, b in enumerate(bonds):
        for p in range(nparties):
            loc = 0
            for (k, d) in Ls[p]:
                loc = loc * d + b[k]
            bond_in[bi][p] = loc
    clauses = []
    for o in it.product(*[range(x) for x in outd]):
        terms = []
        for bi in range(len(bonds)):
            lits = [A[p][o[p]][bond_in[bi][p]] for p in range(nparties)]
            g = pool.id(("and", o, bi))
            for l in lits:
                clauses.append([-g, l])
            clauses.append([g] + [-l for l in lits])
            terms.append(g)
        # XOR chain: x_k = x_{k-1} xor t_k
        acc = terms[0]
        for t in terms[1:]:
            y = pool.id(("xor", o, t))
            clauses += [[-y, acc, t], [-y, -acc, -t], [y, -acc, t], [y, acc, -t]]
            acc = y
        want = 1 if tuple(o) in T else 0
        clauses.append([acc] if want else [-acc])
    t0 = time.time()
    with Solver(name=solver, bootstrap_with=clauses) as s:
        ok = s.solve()
        model = s.get_model() if ok else None
    el = time.time() - t0
    if verbose:
        print(f"  vars={pool.top} clauses={len(clauses)} solve {el:.1f}s -> {'SAT' if ok else 'UNSAT'}")
    if not ok:
        return "UNSAT", None
    pos = set(l for l in model if l > 0)
    maps = [[[1 if A[p][o][i] in pos else 0 for i in range(ind[p])] for o in range(outd[p])] for p in range(nparties)]
    assert verify_f2(nparties, supply, demand, maps)
    return "SAT", maps


def verify_f2(nparties, supply, demand, maps):
    """Independent check of a candidate solution by direct evaluation over F_2."""
    T = dense_support(nparties, demand)
    S = dense_support(nparties, supply)
    outd = [len(m) for m in maps]
    for o in it.product(*[range(x) for x in outd]):
        v = 0
        for s in S:
            prod = 1
            for p in range(nparties):
                prod &= maps[p][o[p]][s[p]]
            v ^= prod
        if v != (1 if tuple(o) in T else 0):
            return False
    return True


if __name__ == "__main__":
    # self-tests: entanglement swapping (SAT); wire from nothing (UNSAT)
    print("swap:", solve_f2(3, [(0, 1, 2), (1, 2, 2)], [(0, 2, 2)], verbose=True)[0])
    print("no-wire:", solve_f2(3, [(0, 1, 2), (1, 2, 1)], [(0, 2, 2)], verbose=True)[0])
    # K_{2,3}: parties u1=0,u2=1,v1=2,v2=3,v3=4
    S = [(0, 2, 2), (0, 3, 2), (0, 4, 2), (1, 2, 2), (1, 3, 2), (1, 4, 2)]
    for dem in [(2, 2, 1, 1), (2, 2, 2, 1), (2, 1, 2, 2), (2, 2, 2, 2)]:
        D = [(2, 3, dem[0]), (3, 4, dem[1]), (2, 4, dem[2]), (0, 1, dem[3])]
        D = [w for w in D if w[2] > 1] or [(2, 3, 1)]
        t0 = time.time()
        st, _ = solve_f2(5, S, D, verbose=True)
        print(f"K23 bond 2, demand (v1v2,v2v3,v1v3,u1u2)={dem}: {st}  ({time.time()-t0:.1f}s)")
        sys.stdout.flush()
