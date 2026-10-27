"""Multi-field version of ext_engine (research/meta-theorem.md).

Each vertex v carries nf independent Grassmann pairs (psibar_v^f, psi_v^f), f = 0..nf-1, one per
global predicate.  Generator bits: psibar_v^f = 2*(nf*v + f), psi_v^f = 2*(nf*v + f) + 1.  The
Berezin integral is the coefficient of the top monomial (ascending bits); since every pair
psibar psi is even, it equals the product over fields of the per-field Berezin integrals, so a
product of even per-field factors integrates to the product of the determinants.  A field f can
be absent at a vertex (root of that field): has(v, f) False.

The sum is
    Z = sum_{s, sigma} prod_v C_v(s_v, sigma|delta(v)) * Berezin[ prod_v M_v(s_v) prod_e F_e(s_u, s_v, sigma_e) ]
exactly as in ext_engine; only the generator layout changes.  The crossing-edge factorisation
(ext_engine.decompose_edge, an exact rank factorisation per (sigma, parity)) and the contraction
with the reordering sign (ext_engine.contract) are reused unchanged; the sign rule only needs the
parity of each piece, and every F_e is even.
"""
import itertools
import ext_engine as E
from ext_engine import (ONE, ZERO, gmul, gadd, gscale, gexp, det_exact, kron_decode,
                        random_blobs, crossing_ok, contract, decompose_edge)


class MSpec:
    n = 0
    edges = []
    nf = 1

    # ---- problem interface
    def vstates(self, v): return [0]
    def estates(self, k): return [0]
    def C(self, v, s, sig): return 1
    def M(self, v, s): return ONE
    def F(self, k, su, sv, sig): return ONE
    def has(self, v, f): return True

    # ---- generators
    def _b(self, v, f): return 2 * (self.nf * v + f)
    def pb(self, v, f): return {1 << self._b(v, f): 1} if self.has(v, f) else {}
    def ps(self, v, f): return {1 << (self._b(v, f) + 1): 1} if self.has(v, f) else {}
    def pbps(self, v, f): return {3 << self._b(v, f): 1} if self.has(v, f) else {}
    def mass(self, v, f, w):
        """1 + w psibar psi (diagonal entry w); a root has no row: 1."""
        return gadd(ONE, gscale(self.pbps(v, f), w)) if self.has(v, f) else ONE
    def delete(self, v, f):
        """psibar psi: removes v from field f (v not in the selected vertex set)."""
        return self.pbps(v, f) if self.has(v, f) else ONE
    def q_und(self, u, v, f):
        """(psibar_u - psibar_v)(psi_u - psi_v): undirected Laplacian edge."""
        return gmul(gadd(self.pb(u, f), self.pb(v, f), -1), gadd(self.ps(u, f), self.ps(v, f), -1))
    def q_out(self, u, v, f):
        """arc u->v in L_out = D_out - A: psibar_u (psi_u - psi_v); det L_out^(r) = #in-arborescences to r."""
        return gmul(self.pb(u, f), gadd(self.ps(u, f), self.ps(v, f), -1))
    def q_in(self, u, v, f):
        """arc u->v in L_in = D_in - A^T: psibar_v (psi_v - psi_u); det L_in^(r) = #out-arborescences from r."""
        return self.q_out(v, u, f)
    def incident(self, v):
        if not hasattr(self, "_inc"):
            self._inc = {x: [k for k, e in enumerate(self.edges) if x in e] for x in range(self.n)}
        return self._inc[v]
    def topmask(self, v):
        m = 0
        for f in range(self.nf):
            if self.has(v, f):
                m |= 3 << self._b(v, f)
        return m


_old_monos = E.monos
def _monos(spec, v):
    if not isinstance(spec, MSpec):
        return _old_monos(spec, v)
    bits = [b for f in range(spec.nf) if spec.has(v, f) for b in (spec._b(v, f), spec._b(v, f) + 1)]
    out = []
    for r in range(len(bits) + 1):
        for c in itertools.combinations(bits, r):
            out.append(sum(1 << b for b in c))
    return out
E.monos = _monos   # decompose_edge looks monos up in ext_engine at call time


def build_network(spec, blob):
    """ext_engine.build_network with the multi-field top monomial."""
    K = max(blob) + 1
    n = spec.n
    cross, internal = [], {a: [] for a in range(K)}
    for k, (u, v) in enumerate(spec.edges):
        (internal[blob[u]].append(k) if blob[u] == blob[v] else cross.append(k))
    lab, low = {}, {}
    for k in cross:
        u, v = spec.edges[k]
        i, j = (u, v) if blob[u] < blob[v] else (v, u)
        low[k] = (i, j)
        lab[k] = decompose_edge(spec, k, i, j)
    tables = {}
    for a in range(K):
        va = [v for v in range(n) if blob[v] == a]
        top = 0
        for v in va:
            top |= spec.topmask(v)
        inc = [k for k in cross if a in (blob[spec.edges[k][0]], blob[spec.edges[k][1]])]
        ints = internal[a]
        local_cfgs = []
        for ss in itertools.product(*[spec.vstates(v) for v in va]):
            sd = dict(zip(va, ss))
            Mp = ONE
            for v in va:
                Mp = gmul(Mp, spec.M(v, sd[v]))
                if not Mp:
                    break
            if not Mp:
                continue
            for sigs in itertools.product(*[spec.estates(k) for k in ints]):
                sigd = dict(zip(ints, sigs))
                P = Mp
                for k in ints:
                    u, v = spec.edges[k]
                    P = gmul(P, spec.F(k, sd[u], sd[v], sigd[k]))
                    if not P:
                        break
                if P:
                    local_cfgs.append((sd, sigd, P))
        tab = {}
        for labs in itertools.product(*[range(len(lab[k])) for k in inc]):
            ld = dict(zip(inc, labs))
            val = 0
            for sd, sigd, P in local_cfgs:
                sig_all = dict(sigd)
                for k in inc:
                    sig_all[k] = lab[k][ld[k]][0]
                w = 1
                for v in va:
                    w *= spec.C(v, sd[v], {k: sig_all[k] for k in spec.incident(v)})
                    if w == 0:
                        break
                if w == 0:
                    continue
                X = P
                for k in inc:
                    sig, p, al, be = lab[k][ld[k]]
                    i, j = low[k]
                    X = gmul(X, al.get(sd[i], {}) if blob[i] == a else be.get(sd[j], {}))
                    if not X:
                        break
                if X:
                    val += w * X.get(top, 0)
            if val != 0:
                tab[labs] = val
        tables[a] = (inc, tab)
    return dict(K=K, cross=cross, lab=lab, low=low, tables=tables, blob=blob)


def network_value(spec, blob):
    net = build_network(spec, blob)
    Z = contract(net)
    return Z, {k: len(net["lab"][k]) for k in net["cross"]}, net


def check_network(spec, E_, target, rng, Ks=(2, 3), parts=2, max_cross=6, max_inc=5, tries=200):
    """Evaluate the blob network on `parts` random partitions for each K; return rows
    (K, #crossing edges, max labels per crossing edge, ok)."""
    n = spec.n
    rows = []
    for K in Ks:
        if K > n:
            continue
        for _ in range(parts):
            for _t in range(tries):
                bl = random_blobs(n, K, rng)
                if crossing_ok(E_, bl, max_cross, max_inc):
                    break
            else:
                continue
            Z, bits, _ = network_value(spec, bl)
            ok = (Z == target)
            if not ok:
                print(f"   !! K={K} blob={bl} Z={Z} target={target}")
            rows.append((K, len(bits), max(bits.values()) if bits else 0, ok))
    return rows
