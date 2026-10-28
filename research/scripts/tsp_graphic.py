"""Checks for Theorem TSP-3 of research/tsp-theorem.md (graphic / graph-metric TSP).

Run: python3 tsp_graphic.py [seed] [instances]

G1  closed-walk optimum = metric-closure TSP (permutations over the shortest-path metric)
    = min over x in {0,1,2}^E, all degrees even, supp x connected spanning, of l . x;
    and multiplicities <= 2 suffice (compared with x in {0,1,2,3}^E)
G2  identity: lowest z-power of  Phi(z) = sum_{x in {0,1,2}^E, deg_x even} z^{l.x} tau(supp x)
    is the optimum; its coefficient is sum_{x optimal} tau(supp x) > 0
G3  vertex splitting (forced path edges, parity carried as an edge state) preserves Phi exactly
G4  blob network (ext_engine, generic exact Schmidt factorisation + sign) on the original graph
    and on the split graph (max degree 3): value = Phi(Y), 9 labels per crossing edge, <= 8 on a
    forced path edge
G5  witness by self-reduction (pinning x_e), checked to be a connected even multigraph of optimal
    length; also the tau-weighted optimal count is NOT the number of optimal x in general
"""
import itertools
import random
import sys

from tsp_lib import *
from ext_engine import Spec, network_value, random_blobs, crossing_ok


FAILS = 0


def check(cond, msg):
    global FAILS
    if not cond:
        FAILS += 1
        print("  FAIL:", msg)


def connected_graph(n, m, rng):
    while True:
        E = random_graph(n, m, rng)
        adj = {v: set() for v in range(n)}
        for i, j in E:
            adj[i].add(j); adj[j].add(i)
        seen = {0}; st = [0]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in seen:
                    seen.add(y); st.append(y)
        if len(seen) == n:
            return E


def metric_tsp(n, E, lens):
    INF = 10 ** 12
    d = [[0 if i == j else INF for j in range(n)] for i in range(n)]
    for (i, j), l in zip(E, lens):
        d[i][j] = min(d[i][j], l); d[j][i] = min(d[j][i], l)
    for k in range(n):
        for i in range(n):
            for j in range(n):
                d[i][j] = min(d[i][j], d[i][k] + d[k][j])
    best = INF
    for p in itertools.permutations(range(1, n)):
        tour = (0,) + p + (0,)
        best = min(best, sum(d[tour[t]][tour[t + 1]] for t in range(n)))
    return best


def even_connected(n, E, xs):
    deg = [0] * n
    for (i, j), x in zip(E, xs):
        deg[i] += x; deg[j] += x
    if any(d % 2 for d in deg):
        return False
    supp = [E[k] for k in range(len(E)) if xs[k]]
    par = list(range(n))
    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for i, j in supp:
        par[f(i)] = f(j)
    return len({f(v) for v in range(n)}) == 1


def walk_poly(n, E, lens, maxmult=2, pins=None):
    """Phi(z) = sum_{x, deg even} z^{l.x} tau(supp x) as a polynomial; pins: dict k -> forced x_k."""
    P = {}
    m = len(E)
    ranges = [[pins[k]] if pins and k in pins else list(range(maxmult + 1)) for k in range(m)]
    for xs in itertools.product(*ranges):
        deg = [0] * n
        for (i, j), x in zip(E, xs):
            deg[i] += x; deg[j] += x
        if any(d % 2 for d in deg):
            continue
        supp = [E[k] for k in range(m) if xs[k]]
        t = det_bareiss(reduced_laplacian(n, supp, 0))
        if t:
            e = sum(x * l for x, l in zip(xs, lens))
            P[e] = P.get(e, 0) + t
    return P


class WalkSpec(Spec):
    """x_e in {0,1,2} (restricted by pins); C_v = [deg_x(v) even]; F_e = Y^{x l_e}(1+q_e) if x > 0."""
    def __init__(self, n, E, lens, Y, pins=None):
        self.n, self.edges, self.lens, self.Y = n, E, lens, Y
        self.pins = pins or {}
        self._inc = {v: [k for k, e in enumerate(E) if v in e] for v in range(n)}
    def gens(self, v): return v != 0
    def incident(self, v): return self._inc[v]
    def estates(self, k): return [self.pins[k]] if k in self.pins else [0, 1, 2]
    def C(self, v, s, sig): return 1 if sum(sig.values()) % 2 == 0 else 0
    def F(self, k, su, sv, x):
        if x == 0:
            return ONE
        u, v = self.edges[k]
        return gscale(gadd(ONE, self.q_undirected(u, v)), self.Y ** (x * self.lens[k]))


class SplitSpec(Spec):
    """The split graph G': every vertex v of degree d >= 2 becomes a path v_1 - ... - v_d of copies,
    the i-th original edge at v attached to v_i.  Path edges are forced (factor q_f) and carry the
    parity sigma in {0,1} of the x-values seen so far along the path.  Original edges keep
    x in {0,1,2}.  The root is the first copy of vertex 0."""
    def __init__(self, n, E, lens, Y):
        self.Y = Y
        deg = [0] * n
        for i, j in E:
            deg[i] += 1; deg[j] += 1
        self.copies = {}
        cnt = 0
        for v in range(n):
            self.copies[v] = list(range(cnt, cnt + max(deg[v], 1)))
            cnt += max(deg[v], 1)
        self.n = cnt
        used = {v: 0 for v in range(n)}
        self.edges = []; self.kind = []   # kind: ('orig', k) or ('path', v, i)
        for k, (i, j) in enumerate(E):
            ci = self.copies[i][used[i]]; cj = self.copies[j][used[j]]
            used[i] += 1; used[j] += 1
            self.edges.append((ci, cj)); self.kind.append(("orig", k, lens[k]))
        for v in range(n):
            cp = self.copies[v]
            for t in range(len(cp) - 1):
                self.edges.append((cp[t], cp[t + 1])); self.kind.append(("path", v, t))
        self.m_orig = len(E)
        self._inc = {u: [k for k, e in enumerate(self.edges) if u in e] for u in range(self.n)}
        # for each copy: its original edge, left path edge, right path edge
        self.role = {}
        for u in range(self.n):
            orig = [k for k in self._inc[u] if self.kind[k][0] == "orig"]
            left = [k for k in self._inc[u] if self.kind[k][0] == "path" and self.edges[k][1] == u]
            right = [k for k in self._inc[u] if self.kind[k][0] == "path" and self.edges[k][0] == u]
            self.role[u] = (orig, left, right)
        self.root = self.copies[0][0]
    def gens(self, u): return u != self.root
    def incident(self, u): return self._inc[u]
    def estates(self, k): return [0, 1, 2] if self.kind[k][0] == "orig" else [0, 1]
    def C(self, u, s, sig):
        orig, left, right = self.role[u]
        x = sum(sig[k] for k in orig)                 # 0 or 1 original edge
        sl = sig[left[0]] if left else 0
        if right:
            return 1 if sig[right[0]] == (sl + x) % 2 else 0
        return 1 if (sl + x) % 2 == 0 else 0
    def F(self, k, su, sv, st):
        u, v = self.edges[k]
        if self.kind[k][0] == "path":
            return self.q_undirected(u, v)             # forced edge, state carried by C only
        if st == 0:
            return ONE
        return gscale(gadd(ONE, self.q_undirected(u, v)), self.Y ** (st * self.kind[k][2]))


def split_sum(ss, target):
    """sum over x on the original edges (parity at every original vertex even), with the path
    states sigma determined by x, of [Omega'] prod_{path f} q_f prod_{x_e>0} Y^{x l_e}(1+q_e)."""
    tot = 0
    orig = [k for k in range(len(ss.edges)) if ss.kind[k][0] == "orig"]
    paths = [k for k in range(len(ss.edges)) if ss.kind[k][0] == "path"]
    top = 0
    for u in range(ss.n):
        if ss.gens(u):
            top |= 3 << (2 * u)
    Pq = ONE
    for k in paths:
        u, v = ss.edges[k]
        Pq = gmul(Pq, ss.q_undirected(u, v))
    for xs in itertools.product((0, 1, 2), repeat=len(orig)):
        xd = dict(zip(orig, xs))
        # parity at every original vertex: the sum over its copies' original edges
        ok = True
        for v, cp in ss.copies.items():
            s = 0
            for u in cp:
                s += sum(xd[k] for k in ss.role[u][0])
            if s % 2:
                ok = False; break
        if not ok:
            continue
        Pr = Pq
        for k in orig:
            if xd[k]:
                u, v = ss.edges[k]
                Pr = gmul(Pr, ss.F(k, 0, 0, xd[k]))
                if not Pr:
                    break
        tot += Pr.get(top, 0) if Pr else 0
    return tot


def net_check(spec, E_, target, rng, Ks=(2, 3), max_cross=6, max_inc=5, label="", parts=1):
    rows = []
    for K in Ks:
        if K > spec.n:
            continue
        for _ in range(parts):
            for _t in range(300):
                bl = random_blobs(spec.n, K, rng)
                if crossing_ok(spec.edges, bl, max_cross, max_inc):
                    break
            else:
                continue
            Z, bits, _ = network_value(spec, bl)
            check(Z == target, f"G4 {label} K={K} blob={bl}: {Z} vs {target}")
            rows.append((K, len(bits), max(bits.values()) if bits else 0))
    return rows


def main(seed=1, count=8):
    rng = random.Random(seed)
    for idx in range(count):
        n = rng.choice([4, 5, 5, 6])
        m = rng.randint(n - 1, min(n + 2, n * (n - 1) // 2, 7))
        E = connected_graph(n, m, rng)
        sys.stdout.flush()
        lens = [1] * m if idx % 2 == 0 else [rng.randint(1, 3) for _ in E]
        # ---- G1
        truth = metric_tsp(n, E, lens)
        best2 = min((sum(x * l for x, l in zip(xs, lens)) for xs in itertools.product((0, 1, 2), repeat=m)
                     if even_connected(n, E, xs)), default=None)
        check(best2 == truth, f"G1 n={n}: walks {best2} vs metric {truth}")
        if 4 ** m <= 70000:
            best3 = min(sum(x * l for x, l in zip(xs, lens)) for xs in itertools.product((0, 1, 2, 3), repeat=m)
                        if even_connected(n, E, xs))
            check(best3 == truth, f"G1 mult 3: {best3} vs {truth}")
        # ---- G2
        Phi = walk_poly(n, E, lens)
        opt = plowest(Phi)
        check(opt == truth, f"G2 lowest power {opt} vs {truth}")
        nopt_x = sum(1 for xs in itertools.product((0, 1, 2), repeat=m)
                     if even_connected(n, E, xs) and sum(x * l for x, l in zip(xs, lens)) == truth)
        tau_sum = sum(det_bareiss(reduced_laplacian(n, [E[k] for k in range(m) if xs[k]], 0))
                      for xs in itertools.product((0, 1, 2), repeat=m)
                      if even_connected(n, E, xs) and sum(x * l for x, l in zip(xs, lens)) == truth)
        check(Phi[opt] == tau_sum and tau_sum >= nopt_x, "G2 coefficient")
        # ---- G3, G4
        b = (n - 1).bit_length() + 2 * m + 4        # coefficient <= 3^m * n^{n-2} ... generous
        b = max(b, 2 * m + 3 * n)
        Y = 1 << b
        target = kron_eval(Phi, Y)
        sp = WalkSpec(n, E, lens, Y)
        ss = SplitSpec(n, E, lens, Y)
        Zs = split_sum(ss, target)                   # the plain Berezin sum on G' (G3)
        check(Zs == target, f"G3 split graph n'={ss.n}: {Zs} vs {target}")
        rows_o = net_check(sp, E, target, rng, label="orig")
        rows_s = net_check(ss, ss.edges, target, rng, label="split", max_cross=4, max_inc=3) if m <= 6 else []
        check(all(r[2] <= 9 for r in rows_o), f"G4 labels orig {rows_o}")
        check(all(r[2] <= 9 for r in rows_s), f"G4 labels split {rows_s}")
        # ---- G5 witness by self-reduction with pins
        pins = {}
        for k in range(m):
            for val in (0, 1, 2):
                pins[k] = val
                P = walk_poly(n, E, lens, pins=pins)
                if plowest(P) == opt:
                    break
            else:
                check(False, "G5 no value works")
        xs = tuple(pins[k] for k in range(m))
        check(even_connected(n, E, xs) and sum(x * l for x, l in zip(xs, lens)) == opt, f"G5 witness {xs}")
        print(f"  [{idx}] n={n} m={m} lens={'unit' if idx % 2 == 0 else 'rand'} OPT={truth} "
              f"#opt x={nopt_x} tau-weighted={Phi[opt]} split n'={ss.n} m'={len(ss.edges)} "
              f"net orig {rows_o} split {rows_s}")
    print("ALL CHECKS PASSED" if FAILS == 0 else f"{FAILS} FAILURES")
    return FAILS == 0


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    sys.exit(0 if main(seed, count) else 1)
