"""Quadratic-Boolean multiplicative complexity of <p,q,r> over F2 via the alternating-form
equations (exact, no row sampling).

Fact: Boolean quadratic functions modulo affine functions <-> alternating bilinear forms over F2
(x_i^2 = x_i makes the diagonal linear). A gate L1*L2 (L affine) maps to l1 ^ l2 := l1 l2^T + l2 l1^T.
A quadratic XOR-AND circuit (AND inputs affine in the INPUTS only) with k ANDs computes the targets
iff each target form T_o is an F2-sum of some of the k forms l_j1 ^ l_j2.
Equations: for all o, u<v: XOR_j g_oj (l_j1[u] l_j2[v] + l_j1[v] l_j2[u]) = T_o[u,v].

Compare: the formal (polynomial-identity) commutative quadratic model additionally requires the
diagonal (x_u^2 coefficient) sum_j g_oj l_j1[u] l_j2[u] = 0. Flag 'formal' adds that.
usage: quad_alt.py p q r k [formal] [threads]
"""
import sys, time, itertools
import pycryptosat

def targets(p, q, r):
    n = p*q + q*r
    A = lambda i, j: i*q + j
    B = lambda j, k: p*q + j*r + k
    T = []
    for i in range(p):
        for k in range(r):
            S = set()
            for j in range(q):
                a, b = A(i, j), B(j, k)
                S.add((min(a, b), max(a, b)))
            T.append(S)
    return n, T

def solve(p, q, r, k, formal=False, threads=4):
    n, T = targets(p, q, r)
    m = len(T)
    s = pycryptosat.Solver(threads=threads)
    nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    def AND(*xs):
        y = new()
        for x in xs: s.add_clause([-y, x])
        s.add_clause([y] + [-x for x in xs])
        return y
    l1 = [[new() for _ in range(n)] for j in range(k)]
    l2 = [[new() for _ in range(n)] for j in range(k)]
    g = [[new() for _ in range(k)] for o in range(m)]
    for j in range(k):
        s.add_clause(l1[j]); s.add_clause(l2[j])
    # symmetry breaking: gate j used by some output
    for j in range(k):
        s.add_clause([g[o][j] for o in range(m)])
    # pairwise products P_j[u][v] = l1[u] l2[v]
    P = [[[AND(l1[j][u], l2[j][v]) for v in range(n)] for u in range(n)] for j in range(k)]
    for o in range(m):
        for u in range(n):
            for v in range(u + 1, n):
                terms = []
                for j in range(k):
                    terms.append(AND(g[o][j], P[j][u][v]))
                    terms.append(AND(g[o][j], P[j][v][u]))
                s.add_xor_clause(terms, (u, v) in T[o])
            if formal:
                s.add_xor_clause([AND(g[o][j], P[j][u][u]) for j in range(k)], False)
    t = time.time()
    sat, sol = s.solve()
    dt = time.time() - t
    if sat:
        gates = [(''.join(str(int(sol[x])) for x in l1[j]), ''.join(str(int(sol[x])) for x in l2[j])) for j in range(k)]
        use = [[int(sol[g[o][j]]) for j in range(k)] for o in range(m)]
        return True, dt, gates, use
    return False, dt, None, None

if __name__ == '__main__':
    p, q, r, k = map(int, sys.argv[1:5])
    formal = len(sys.argv) > 5 and sys.argv[5] == 'formal'
    th = int(sys.argv[6]) if len(sys.argv) > 6 else 4
    ok, dt, gates, use = solve(p, q, r, k, formal, th)
    print(f"<{p},{q},{r}> k={k} {'formal' if formal else 'boolean'}: {'SAT' if ok else 'UNSAT'} {dt:.1f}s")
    if ok:
        print(gates); print(use)
