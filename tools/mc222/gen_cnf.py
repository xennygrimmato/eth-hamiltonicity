#!/usr/bin/env python3
"""CNF encoding of "there is an XOR-AND circuit with exactly k AND gates computing the targets".

Independent of the Rust search (shares no code).  Truth-table encoding over all 2^n inputs.

Circuit model (see README for the normalisations and their proofs):
  gate i:   g_i = L_i * R_i,  L_i, R_i = F2-linear combinations (no constant) of x_0..x_{n-1}
            and g_0..g_{i-1};  the pair (L_i, R_i) is the reduced row-echelon basis of the
            2-dimensional space it spans (so L_i, R_i are linearly independent);
  output t: target_t = e_t + sum_k ell_{t,k} x_k + sum_i lam_{t,i} g_i  (all coefficients free).
Optional: --root a,b fixes gate 0 to the product of the linear forms with input masks a, b.

usage: gen_cnf.py <problem> <k> [--root a,b] [--helper p] > file.cnf
       gen_cnf.py <problem> <k> [--root a,b] --decode solver_output > circuit.txt
"""
import sys
from itertools import product


def targets(problem):
    """returns n, list of target functions given as callables on input tuples (independent
    re-implementation of the definitions)"""
    if problem == "mm222":  # x = a11 a12 a21 a22 b11 b12 b21 b22
        fs = []
        for i in range(2):
            for j in range(2):
                fs.append(lambda x, i=i, j=j: (x[2*i] & x[4+j]) ^ (x[2*i+1] & x[6+j]))
        return 8, fs
    if problem in ("polymul2", "polymul3"):
        t = 2 if problem == "polymul2" else 3
        fs = []
        for s in range(2*t - 1):
            def f(x, s=s):
                v = 0
                for i in range(t):
                    if 0 <= s - i < t:
                        v ^= x[i] & x[t + s - i]
                return v
            fs.append(f)
        return 2*t, fs
    if problem == "f4":
        return 4, [lambda x: (x[0] & x[2]) ^ (x[1] & x[3]),
                   lambda x: (x[0] & x[3]) ^ (x[1] & x[2]) ^ (x[1] & x[3])]
    if problem == "mm221":
        return 6, [lambda x, i=i: (x[2*i] & x[4]) ^ (x[2*i+1] & x[5]) for i in range(2)]
    raise SystemExit("unknown problem")


class CNF:
    def __init__(self):
        self.nv = 0
        self.cl = []

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, c):
        self.cl.append(c)

    # values are ints (literals) or Python bools (constants)
    def xor(self, a, b):
        if isinstance(a, bool) and isinstance(b, bool):
            return a != b
        if isinstance(a, bool):
            return -b if a else b
        if isinstance(b, bool):
            return -a if b else a
        z = self.var()
        self.add([-z, a, b]); self.add([-z, -a, -b]); self.add([z, -a, b]); self.add([z, a, -b])
        return z

    def and_(self, a, b):
        if isinstance(a, bool):
            return b if a else False
        if isinstance(b, bool):
            return a if b else False
        z = self.var()
        self.add([-z, a]); self.add([-z, b]); self.add([z, -a, -b])
        return z

    def equal_const(self, a, c):
        if isinstance(a, bool):
            if a != c:
                self.add([])  # contradiction
            return
        self.add([a] if c else [-a])

    def dimacs(self):
        out = [f"p cnf {self.nv} {len(self.cl)}"]
        out += [" ".join(map(str, c)) + " 0" for c in self.cl]
        return "\n".join(out) + "\n"


def rref_plane(a, b, npos):
    """reduced echelon basis (pivot = first nonzero position) of span{a,b}, as bit lists"""
    rows = [[(a >> c) & 1 for c in range(npos)], [(b >> c) & 1 for c in range(npos)]]
    p1 = min(c for c in range(npos) if rows[0][c] or rows[1][c])
    if not rows[0][p1]:
        rows.reverse()
    if rows[1][p1]:
        rows[1] = [u ^ v for u, v in zip(rows[0], rows[1])]
    p2 = min(c for c in range(npos) if rows[1][c])
    if rows[0][p2]:
        rows[0] = [u ^ v for u, v in zip(rows[0], rows[1])]
    return rows


def encode(problem, k, root=None, helper=None):
    n, fs = targets(problem)
    N = 1 << n
    pts = [tuple((p >> j) & 1 for j in range(n)) for p in range(N)]
    f = CNF()
    G = []  # G[i][p]: value of gate i at point p
    sel = []
    for i in range(k):
        npos = n + i
        Ls = [f.var() for _ in range(npos)]
        Rs = [f.var() for _ in range(npos)]
        sel.append((Ls, Rs))
        # RREF of the pair: zL[c] <-> Ls[0..c-1] all zero
        def prefzero(S):
            z = [True]
            for c in range(npos):
                v = f.var()  # v <-> z[c] and not S[c]
                prev = z[-1]
                if prev is True:
                    f.add([-v, -S[c]]); f.add([v, S[c]])
                else:
                    f.add([-v, prev]); f.add([-v, -S[c]]); f.add([v, -prev, S[c]])
                z.append(v)
            return z
        zL, zR = prefzero(Ls), prefzero(Rs)
        f.add([-zL[npos]])  # L != 0
        f.add([-zR[npos]])  # R != 0
        for c in range(npos):
            piv_L = [] if zL[c] is True else [-zL[c]]
            piv_R = [] if zR[c] is True else [-zR[c]]
            # pivot(L) = c  ->  R[0..c] = 0
            for d in range(c + 1):
                f.add(piv_L + [-Ls[c], -Rs[d]])
            # pivot(R) = c  ->  L[c] = 0
            f.add(piv_R + [-Rs[c], -Ls[c]])
        if i == 0 and root is not None:
            rl, rr = rref_plane(root[0], root[1], npos)
            for c in range(npos):
                f.add([Ls[c]] if rl[c] else [-Ls[c]])
                f.add([Rs[c]] if rr[c] else [-Rs[c]])

        # x-part shared through the recursion X(p) = X(p - highbit) xor s_highbit
        def lin_shared(S):
            X = [False] * N
            for p in range(1, N):
                h = p.bit_length() - 1
                X[p] = f.xor(X[p ^ (1 << h)], S[h])
            vals = []
            for p in range(N):
                v = X[p]
                for j in range(i):
                    v = f.xor(v, f.and_(S[n + j], G[j][p]))
                vals.append(v)
            return vals
        Lv, Rv = lin_shared(Ls), lin_shared(Rs)
        G.append([f.and_(Lv[p], Rv[p]) for p in range(N)])
    if helper is not None:
        # structural cube (README, "helper/reducer lemma"): gate 0 and gate `helper` are the only
        # gates allowed outside A+T+span(earlier helpers); every other gate i must satisfy
        # g_i = e + sum ell_k x_k + sum mu_t target_t + alpha g_0 + beta g_helper (beta only if helper < i).
        tv = [[bool(ft(pts[p])) for p in range(N)] for ft in fs]
        for i in range(1, k):
            if i == helper:
                continue
            e0 = f.var()
            ell = [f.var() for _ in range(n)]
            mu = [f.var() for _ in fs]
            hs = [0] + ([helper] if helper < i else [])
            al = [f.var() for _ in hs]
            X = [False] * N
            for p in range(1, N):
                h = p.bit_length() - 1
                X[p] = f.xor(X[p ^ (1 << h)], ell[h])
            for p in range(N):
                v = f.xor(X[p], e0)
                for t in range(len(fs)):
                    if tv[t][p]:
                        v = f.xor(v, mu[t])
                for a, j in zip(al, hs):
                    v = f.xor(v, f.and_(a, G[j][p]))
                v = f.xor(v, G[i][p])
                f.equal_const(v, False)
    outs = []
    for t, ft in enumerate(fs):
        lam = [f.var() for _ in range(k)]
        ell = [f.var() for _ in range(n)]
        e0 = f.var()
        outs.append((e0, ell, lam))
        X = [False] * N
        for p in range(1, N):
            h = p.bit_length() - 1
            X[p] = f.xor(X[p ^ (1 << h)], ell[h])
        for p in range(N):
            v = f.xor(X[p], e0)
            for i in range(k):
                v = f.xor(v, f.and_(lam[i], G[i][p]))
            f.equal_const(v, bool(ft(pts[p])))
    return f, sel, outs, n


def decode(problem, k, root, helper, model_path):
    """turn a solver model (lines 'v ...') into a circuit file for verify_circuit.py"""
    f, sel, outs, n = encode(problem, k, root, helper)
    true = set()
    for line in open(model_path):
        if line.startswith("v "):
            true.update(int(t) for t in line.split()[1:] if int(t) > 0)
    gen = lambda c: 1 + c if c < n else n + 1 + (c - n)
    s = f"# problem {problem} n={n} ands={k} (decoded SAT model)\n"
    for Ls, Rs in sel:
        s += "G " + " ".join(str(gen(c)) for c, v in enumerate(Ls) if v in true)
        s += " | " + " ".join(str(gen(c)) for c, v in enumerate(Rs) if v in true) + "\n"
    names = {"mm222": ["c11", "c12", "c21", "c22"], "f4": ["c0", "c1"], "mm221": ["c1", "c2"]}
    nm = names.get(problem, [f"c{t}" for t in range(len(outs))])
    for t, (e0, ell, lam) in enumerate(outs):
        lst = ([0] if e0 in true else []) + [1 + j for j, v in enumerate(ell) if v in true] \
            + [n + 1 + i for i, v in enumerate(lam) if v in true]
        s += f"O {nm[t]} " + " ".join(map(str, lst)) + "\n"
    return s


if __name__ == "__main__":
    problem, k = sys.argv[1], int(sys.argv[2])
    root = None
    if "--root" in sys.argv:
        a, b = sys.argv[sys.argv.index("--root") + 1].split(",")
        root = (int(a), int(b))
    helper = None
    if "--helper" in sys.argv:
        helper = int(sys.argv[sys.argv.index("--helper") + 1])
    if "--decode" in sys.argv:
        sys.stdout.write(decode(problem, k, root, helper, sys.argv[sys.argv.index("--decode") + 1]))
        sys.exit(0)
    f, sel, outs, n = encode(problem, k, root, helper)
    sys.stdout.write(f"c mc222 gen_cnf problem={problem} k={k} root={root} helper={helper}\n")
    sys.stdout.write(f.dimacs())
