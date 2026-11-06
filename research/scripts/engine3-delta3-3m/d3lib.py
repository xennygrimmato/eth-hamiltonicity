import os
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1"); os.environ.setdefault("OMP_NUM_THREADS", "1")
"""d3lib.py -- (copied from ../engine3-delta3/, ls_update matmuls switched to einsum for speed; same maths)
 Delta_3 (three anti-diagonal triangles of Z_3^2) at N0 = 2, row / column triangle networks, ALS.

Nodes (r,c), r,c in Z_3.  Edges: (r,c)-(r',c') with r+c = r'+c' (mod 3), r != r'.  9 nodes, 9 edges, 18 strings.
Each node holds 2 strings (one per incident edge).  f = product of the 9 equalities (one bit per string), 2^18 entries.

Axis convention ("row order"): the 18 string axes are listed node by node, nodes in row-major order (r,c), and the two
strings of a node in the order of the partner node (row-major).  Row group r = axes 6r..6r+5 (nodes (r,0),(r,1),(r,2)).
Column group c = the strings of nodes (0,c),(1,c),(2,c).  COLPERM lists the 18 axes in "column order".

A row network with bonds (d01,d02,d12): R[g0,g1,g2] = sum W0[g0,x,y] W1[g1,x,z] W2[g2,y,z]  (g_r in 0..63).
Column network: same on the column groups, then permuted back to row order.

The routines are written for a general "configuration on 3 x 3 groups" given by (nodes, edges) so that they also serve
the restrictions of Delta_3 (e.g. two triangles) and the 3x3 level.
"""
import itertools
import numpy as np


class Config:
    def __init__(self, nodes, edges):
        """nodes: list of (r,c); edges: list of node pairs.  Rows/cols = groups by r / by c (values 0..2)."""
        self.nodes = sorted(nodes)
        self.edges = [tuple(sorted(e)) for e in edges]
        self.strings = []                       # (node, edge index), node-major, partner-sorted
        for v in self.nodes:
            inc = sorted([(e[0] if e[1] == v else e[1], i) for i, e in enumerate(self.edges) if v in e])
            for _, i in inc:
                self.strings.append((v, i))
        self.S = len(self.strings)
        self.sidx = {s: k for k, s in enumerate(self.strings)}
        self.rowgroups = [[k for k, (v, _) in enumerate(self.strings) if v[0] == r] for r in range(3)]
        self.colgroups = [[k for k, (v, _) in enumerate(self.strings) if v[1] == c] for c in range(3)]
        self.rowperm = sum(self.rowgroups, [])
        self.colperm = sum(self.colgroups, [])
        assert self.rowperm == list(range(self.S))   # node-major row-major order is row order
        self.gdims_row = [2 ** len(g) for g in self.rowgroups]
        self.gdims_col = [2 ** len(g) for g in self.colgroups]

    def target(self):
        f = np.zeros((2,) * self.S)
        for bits in itertools.product((0, 1), repeat=len(self.edges)):
            idx = tuple(bits[i] for (_, i) in self.strings)
            f[idx] = 1.0
        return f

    # --- reshape helpers -----------------------------------------------------------------
    def to3_row(self, T):
        return T.reshape(self.gdims_row)

    def to3_col(self, T):
        return np.transpose(T.reshape((2,) * self.S), self.colperm).reshape(self.gdims_col)

    def from3_col(self, T3):
        inv = np.argsort(self.colperm)
        return np.transpose(T3.reshape((2,) * self.S), inv).reshape(self.gdims_row)

    def transpose_perm(self):
        """axis permutation implementing (r,c) -> (c,r) on strings (requires the edge set to be transpose invariant)."""
        tn = lambda v: (v[1], v[0])
        eidx = {e: i for i, e in enumerate(self.edges)}
        perm = []
        for (v, i) in self.strings:
            e = self.edges[i]
            te = tuple(sorted((tn(e[0]), tn(e[1]))))
            perm.append(self.sidx[(tn(v), eidx[te])])
        return perm   # string k maps to string perm[k]

    def apply_transpose(self, T):
        perm = self.transpose_perm()
        T = T.reshape((2,) * self.S)
        # (tau T)[x] where x_{perm[k]} = y_k : out axis perm[k] <- in axis k
        out = np.transpose(T, np.argsort(perm))
        return out.reshape(self.gdims_row)


def flat_rank(T3, axis):
    other = [a for a in range(3) if a != axis]
    M = np.transpose(T3, [axis] + other).reshape(T3.shape[axis], -1)
    return np.linalg.matrix_rank(M)


def tri_net(W):
    """W[0][g0,x,y], W[1][g1,x,z], W[2][g2,y,z] -> 3-way tensor."""
    return np.einsum('axy,bxz,cyz->abc', W[0], W[1], W[2], optimize=True)


def env(W, i):
    """environment matrix for group i: shape (bond_i_1*bond_i_2, prod of other group dims), so that
    T3 transposed to (i, others) reshaped = W_i.reshape(gi, -1) @ env."""
    if i == 0:
        return np.einsum('bxz,cyz->xybc', W[1], W[2], optimize=True).reshape(W[0].shape[1] * W[0].shape[2], -1)
    if i == 1:
        return np.einsum('axy,cyz->xzac', W[0], W[2], optimize=True).reshape(W[1].shape[1] * W[1].shape[2], -1)
    return np.einsum('axy,bxz->yzab', W[0], W[1], optimize=True).reshape(W[2].shape[1] * W[2].shape[2], -1)


def unfold(T3, i):
    other = [a for a in range(3) if a != i]
    return np.transpose(T3, [i] + other).reshape(T3.shape[i], -1)


def ls_update(T3, W, i, reg=1e-10):
    M = env(W, i)                       # (k, n)
    Y = unfold(T3, i)                   # (g, n)
    G = np.einsum('kn,ln->kl', M, M)    # einsum: OpenBLAS is pathologically slow on (4 x 4096) @ (4096 x 64) here
    G += reg * (np.trace(G) / G.shape[0] + 1e-30) * np.eye(G.shape[0])
    X = np.linalg.solve(G, np.einsum('kn,gn->kg', M, Y)).T   # (g, k)
    W[i] = X.reshape(W[i].shape)


def rand_net(rng, gdims, bonds, scale=None):
    d01, d02, d12 = bonds
    shapes = [(gdims[0], d01, d02), (gdims[1], d01, d12), (gdims[2], d02, d12)]
    s = scale if scale is not None else 1.0
    return [rng.standard_normal(sh) * s for sh in shapes]


def als_sum(cfg, f3, terms, rng, sweeps=200, tol=1e-12, init_scale=0.3, verbose=False):
    """terms: list of ('row'|'col', bonds).  Fit f ~ sum of the networks by ALS (block-coordinate exact LS).
    Returns (best relative residual, list of factor lists)."""
    nf = np.linalg.norm(f3)
    Ws = []
    for kind, bonds in terms:
        gd = cfg.gdims_row if kind == 'row' else cfg.gdims_col
        Ws.append(rand_net(rng, gd, bonds, init_scale))
    def full(k):
        T = tri_net(Ws[k])
        return T if terms[k][0] == 'row' else cfg.from3_col(T)
    parts = [full(k) for k in range(len(terms))]
    best = np.inf; hist = []
    for it in range(sweeps):
        for k, (kind, bonds) in enumerate(terms):
            tgt = f3 - (sum(parts) - parts[k])
            if kind == 'col':
                tgt = cfg.to3_col(tgt)
            for i in range(3):
                ls_update(tgt, Ws[k], i)
            parts[k] = full(k)
        res = np.linalg.norm(f3 - sum(parts)) / nf
        hist.append(res)
        best = min(best, res)
        if res < tol:
            break
        if it > 40 and hist[-40] - res < 1e-7 * hist[-40]:
            break
    return best, Ws, hist


def delta3():
    nodes = [(r, c) for r in range(3) for c in range(3)]
    edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
    assert len(edges) == 9
    return Config(nodes, edges)


def two_triangles():
    """restriction of Delta_3 to the triangles s = 0, 1 (fix the strings of triangle 2 to a consistent value)."""
    nodes = [(r, c) for r in range(3) for c in range(3) if (r + c) % 3 in (0, 1)]
    edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
    return Config(nodes, edges)


# ---- three-merge extension (engine3-delta3-3m): diagonal groups r - c, generic merge kinds, the symmetry sigma' ----------
def _merge_fn(kind):
    return {'row': lambda v: v[0], 'col': lambda v: v[1], 'diag': lambda v: (v[0] - v[1]) % 3}[kind]

def groups(cfg, kind):
    fn = _merge_fn(kind)
    return [[k for k, (v, _) in enumerate(cfg.strings) if fn(v) == g] for g in range(3)]

def perm_of(cfg, kind):
    return sum(groups(cfg, kind), [])

def gdims(cfg, kind):
    return [2 ** len(g) for g in groups(cfg, kind)]

def to3(cfg, T, kind):
    if kind == 'row': return T.reshape(cfg.gdims_row)
    return np.transpose(T.reshape((2,) * cfg.S), perm_of(cfg, kind)).reshape(gdims(cfg, kind))

def from3(cfg, T3, kind):
    if kind == 'row': return T3.reshape(cfg.gdims_row)
    inv = np.argsort(perm_of(cfg, kind))
    return np.transpose(T3.reshape((2,) * cfg.S), inv).reshape(cfg.gdims_row)

def node_perm(cfg, nmap):
    """axis permutation for a node map preserving the edge set: string k maps to string perm[k]."""
    eidx = {e: i for i, e in enumerate(cfg.edges)}
    perm = []
    for (v, i) in cfg.strings:
        e = cfg.edges[i]
        te = tuple(sorted((nmap(e[0]), nmap(e[1]))))
        perm.append(cfg.sidx[(nmap(v), eidx[te])])
    return perm

def apply_perm(cfg, T, perm):
    T = T.reshape((2,) * cfg.S)
    return np.transpose(T, np.argsort(perm)).reshape(cfg.gdims_row)

SIGMA = lambda v: ((v[1] - v[0]) % 3, (-v[0]) % 3)      # sigma'(r,c) = (c - r, -r): rows -> cols -> diags, fixes triangles
