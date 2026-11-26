"""E1: multiplicative complexity (XOR-AND circuits, XOR/constants free) of small
matrix products over F2, as Boolean functions. Exact via CryptoMiniSat (native XOR)
with counterexample-guided row refinement (UNSAT on a subset of rows => UNSAT).

Circuit normal form: AND gate j has inputs L_{j,0}, L_{j,1}, each an affine form over
the n input bits and outputs of gates < j. Each output is an affine form over inputs
and all gates. This normal form is complete for XOR-AND circuits.

usage: python3 mc_sat.py p q r k [seed]   (product of p x q by q x r matrices)
"""
import sys, itertools, random, time
import pycryptosat

def matmul_targets(p, q, r):
    # inputs: A (p*q) then B (q*r); outputs C (p*r)
    n = p*q + q*r
    A = lambda i, j: i*q + j
    B = lambda j, k: p*q + j*r + k
    outs = []
    for i in range(p):
        for k in range(r):
            outs.append([(A(i, j), B(j, k)) for j in range(q)])
    def f(bits):
        return [sum(bits[a] & bits[b] for a, b in o) & 1 for o in outs]
    return n, len(outs), f

class Enc:
    def __init__(self, n, m, k, f, threads=4, quad=False, time_limit=None):
        self.n, self.m, self.k, self.f = n, m, k, f
        self.s = pycryptosat.Solver(threads=threads) if time_limit is None else pycryptosat.Solver(threads=threads, time_limit=time_limit)
        self.nv = 0
        new = self.new
        # gate input coefficients
        self.c = [[[new() for _ in range(n + 1)] for s in range(2)] for j in range(k)]
        self.d = [[[new() for _ in range(j)] for s in range(2)] for j in range(k)]
        self.e = [[new() for _ in range(n + 1)] for o in range(m)]
        self.g = [[new() for _ in range(k)] for o in range(m)]
        # symmetry breaking: for each gate, side 0 is not the zero/constant form? keep simple:
        # forbid constant-only forms (gate trivially constant or equal to a linear form)
        for j in range(k):
            for s_ in range(2):
                self.s.add_clause(self.c[j][s_][1:] + self.d[j][s_])
                # WLOG gate-input constants are 0: (l1+c1)(l2+c2) = l1 l2 + affine(l1,l2), and every
                # consumer of a gate takes affine combinations, so the affine part is absorbed.
                self.s.add_clause([-self.c[j][s_][0]])
            # WLOG the two inputs differ (else the gate is linear) -- implied by optimality; and every
            # gate is used somewhere (by an output or a later gate) -- also WLOG at the minimum k.
        if quad:  # no gate reuse: quadratic circuits (still Boolean, x^2=x)
            for j in range(k):
                for s_ in range(2):
                    for x in self.d[j][s_]:
                        self.s.add_clause([-x])
        self.rows = set()

    def new(self):
        self.nv += 1
        return self.nv

    # ---- symmetry breaking (all WLOG; see notebook E1c) ----
    def vec(self, j, s_, upto=None):
        """linear form of gate j side s_ as literal list, most significant first:
        gate coefficients (highest gate first, only gates < upto), then inputs (highest first)."""
        upto = j if upto is None else upto
        return [self.d[j][s_][i] for i in reversed(range(upto))] + [self.c[j][s_][1 + i] for i in reversed(range(self.n))]

    def lex(self, X, Y, strict, cond=()):
        """X <=lex Y (or <) unless one of the literals in cond is true."""
        cond = list(cond)
        e = self.new(); self.s.add_clause([e])
        for x, y in zip(X, Y):
            self.s.add_clause(cond + [-e, -x, y])
            e2 = self.new()
            self.s.add_clause([-e, x, y, e2]); self.s.add_clause([-e, -x, -y, e2])
            e = e2
        if strict:
            self.s.add_clause(cond + [-e])

    def add_symmetry(self, first_fixed=True):
        k = self.k
        for j in range(k):
            if first_fixed and j == 0:
                continue
            X, Y = self.vec(j, 0), self.vec(j, 1)
            Wv = []
            for x, y in zip(X, Y):
                w = self.new(); self.s.add_xor_clause([w, x, y], False); Wv.append(w)
            self.lex(X, Y, True)      # plane basis = its two smallest elements
            self.lex(Y, Wv, True)
        for j in range(1 if first_fixed else 0, k - 1):
            # gates j, j+1 independent => order by first basis vector (greedy topological canonical order)
            X = self.vec(j, 0)
            Y = self.vec(j + 1, 0, upto=j)
            self.lex(X, Y, False, cond=[self.d[j + 1][0][j], self.d[j + 1][1][j]])

    def AND(self, a, b):
        x = self.new()
        self.s.add_clause([-x, a]); self.s.add_clause([-x, b]); self.s.add_clause([x, -a, -b])
        return x

    def add_row(self, bits):
        if bits in self.rows:
            return
        self.rows.add(bits)
        v = []
        for j in range(self.k):
            ls = []
            for s_ in range(2):
                l = self.new()
                terms = [l, self.c[j][s_][0]] + [self.c[j][s_][1 + i] for i in range(self.n) if bits[i]]
                terms += [self.AND(self.d[j][s_][i], v[i]) for i in range(j)]
                self.s.add_xor_clause(terms, False)
                ls.append(l)
            v.append(self.AND(ls[0], ls[1]))
        tgt = self.f(bits)
        for o in range(self.m):
            terms = [self.e[o][0]] + [self.e[o][1 + i] for i in range(self.n) if bits[i]]
            terms += [self.AND(self.g[o][j], v[j]) for j in range(self.k)]
            self.s.add_xor_clause(terms, bool(tgt[o]))

    def model_circuit(self, sol):
        val = lambda x: bool(sol[x])
        C = {'c': [[[val(x) for x in side] for side in g] for g in self.c],
             'd': [[[val(x) for x in side] for side in g] for g in self.d],
             'e': [[val(x) for x in o] for o in self.e],
             'g': [[val(x) for x in o] for o in self.g]}
        return C

def eval_circuit(C, bits, n, k, m):
    v = []
    for j in range(k):
        ls = []
        for s_ in range(2):
            c = C['c'][j][s_]; d = C['d'][j][s_]
            l = c[0] ^ (sum(c[1 + i] & bits[i] for i in range(n)) & 1) ^ (sum(d[i] & v[i] for i in range(j)) & 1)
            ls.append(l)
        v.append(ls[0] & ls[1])
    out = []
    for o in range(m):
        e = C['e'][o]
        out.append(e[0] ^ (sum(e[1 + i] & bits[i] for i in range(n)) & 1) ^ (sum(C['g'][o][j] & v[j] for j in range(k)) & 1))
    return out

def solve(p, q, r, k, seed=0, init=64, verbose=True, timelimit=None, quad=False, threads=4):
    n, m, f = matmul_targets(p, q, r)
    rnd = random.Random(seed)
    E = Enc(n, m, k, f, threads=threads, quad=quad)
    allrows = None if n > 20 else list(itertools.product([0, 1], repeat=n))
    for _ in range(init):
        E.add_row(tuple(rnd.randint(0, 1) for _ in range(n)))
    t0 = time.time(); it = 0
    while True:
        it += 1
        sat, sol = E.s.solve()
        if not sat:
            if verbose: print(f"UNSAT with {len(E.rows)} rows, k={k}, {time.time()-t0:.1f}s")
            return None
        C = E.model_circuit(sol)
        # find counterexample
        bad = None
        pool = allrows if allrows is not None else (tuple(rnd.randint(0, 1) for _ in range(n)) for _ in range(200000))
        for bits in pool:
            if eval_circuit(C, bits, n, k, m) != f(bits):
                bad = bits; break
        if bad is None:
            if verbose: print(f"SAT k={k}, rows={len(E.rows)}, {time.time()-t0:.1f}s")
            return C
        E.add_row(bad)
        if verbose and it % 20 == 0:
            print(f"  it {it} rows {len(E.rows)} {time.time()-t0:.1f}s", flush=True)

if __name__ == '__main__':
    p, q, r, k = map(int, sys.argv[1:5])
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    quad = len(sys.argv) > 6 and sys.argv[6] == 'quad'
    th = int(sys.argv[7]) if len(sys.argv) > 7 else 4
    C = solve(p, q, r, k, seed, quad=quad, threads=th)
    if C:
        import json; json.dump(C, open(f'circ_{p}{q}{r}_k{k}{"_quad" if quad else ""}.json','w'))
