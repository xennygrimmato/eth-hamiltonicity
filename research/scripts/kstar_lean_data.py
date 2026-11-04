"""Emit the Lean data (labelling tables, odd certificates) for lean/EthFollowup/Scratch/Kstar/Instances.lean."""
import sys, os
sys.path.insert(0, '/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/pylib')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Cadical153
from linenc2_lib import directed_simple_cycles
def turns_of(c):
    L = len(c); return [(c[i], c[i-1], c[(i+1) % L]) for i in range(L)]
def solve(n, E, k):
    cyc = directed_simple_cycles(n, E); T = sorted({t for c in cyc for t in turns_of(c)}); ti = {t: i for i, t in enumerate(T)}
    cnt = [0]
    def new(): cnt[0] += 1; return cnt[0]
    X = [[new() for _ in T] for _ in range(k)]; s = Cadical153()
    for c in cyc:
        outs = []
        for i in range(k):
            ts = [X[i][ti[t]] for t in turns_of(c)]; acc = ts[0]
            for b in ts[1:]:
                y = new(); a = acc
                s.add_clause([-y, a, b]); s.add_clause([-y, -a, -b]); s.add_clause([y, -a, b]); s.add_clause([y, a, -b]); acc = y
            outs.append(acc)
        s.add_clause(outs)
    assert s.solve(); M = set(l for l in s.get_model() if l > 0)
    tbl = [0] * (n**3)
    for t, j in ti.items():
        tbl[t[0]*n*n + t[1]*n + t[2]] = sum((X[i][j] in M) << i for i in range(k))
    return tbl
def odd_cert(n, E):
    """odd set of cycles whose turn multisets sum to 0 mod 2 (exists iff no k=1 labelling)."""
    cyc = directed_simple_cycles(n, E); T = sorted({t for c in cyc for t in turns_of(c)}); ti = {t: i for i, t in enumerate(T)}
    rows = []  # (vector incl. rhs bit at position len(T), combination mask)
    basis = {}
    for ci, c in enumerate(cyc):
        v = sum(1 << ti[t] for t in turns_of(c)) | (1 << len(T)); comb = 1 << ci
        while True:
            low = v & ((1 << len(T)) - 1)
            if low == 0: break
            p = low.bit_length() - 1
            if p in basis: bv, bc = basis[p]; v ^= bv; comb ^= bc
            else: basis[p] = (v, comb); break
        if v & ((1 << len(T)) - 1) == 0 and v:
            return [cyc[i] for i in range(len(cyc)) if comb >> i & 1]
    return None
if __name__ == '__main__':
    K = lambda k: [(i, j) for i in range(k) for j in range(i+1, k)]
    Kab = lambda a, b: [(i, j) for i in range(a) for j in range(a, a+b)]
    prism = [(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)]
    for name, n, E, k in [('K4', 4, K(4), 1), ('Prism', 6, prism, 1), ('K5', 5, K(5), 2), ('K33', 6, Kab(3, 3), 2)]:
        print(f'-- {name}: k={k} table'); print(name, n, E, solve(n, E, k))
    for name, n, E in [('K5', 5, K(5)), ('K33', 6, Kab(3, 3))]:
        c = odd_cert(n, E); print(f'-- {name} odd certificate: {len(c)} cycles'); print(name, c)
