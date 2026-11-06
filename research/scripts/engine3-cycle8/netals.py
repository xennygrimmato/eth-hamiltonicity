"""netals.py -- generic ALS for  target ~= sum_t (network t),  each term a tensor network on the groups of one merge
(complete graph on the groups, given bond dimensions), at N = 2, one bit per edge (graph tensor: each edge = 2 strings,
equal).  Node leg = the node's strings (dim 2^deg).  Each sweep updates every group tensor of every term by exact least
squares (normal equations with a tiny ridge), the other terms held fixed.  Reports relative residual ||f - sum|| / ||f||.
Used for: rectangle control, planted / known decompositions with 4 groups, the 8-cycle two-cell sub-configuration, prism."""
import itertools, string, numpy as np

class Instance:
    def __init__(self, nodes, edges, merges):
        self.nodes = list(nodes); self.edges = list(edges); self.merges = merges
        self.str_at = {v: [e for e in edges if v in e] for v in self.nodes}
        self.dim = {v: 2 ** len(self.str_at[v]) for v in self.nodes}
        f = np.zeros([self.dim[v] for v in self.nodes])
        for bits in itertools.product((0, 1), repeat=len(edges)):
            val = dict(zip(edges, bits)); idx = []
            for v in self.nodes:
                x = 0
                for e in self.str_at[v]: x = 2 * x + val[e]
                idx.append(x)
            f[tuple(idx)] = 1.0
        self.f = f; self.letters = {v: string.ascii_letters[i] for i, v in enumerate(self.nodes)}

class Net:
    """network on the groups of a merge; bonds: dict (i,j)->dim (i<j); tensors W[i] axes: group nodes, then bonds of i."""
    def __init__(self, inst, groups, bonds, rng, scale=1.0):
        self.inst = inst; self.groups = groups; r = len(groups)
        self.pairs = list(itertools.combinations(range(r), 2)); self.bonds = {p: bonds.get(p, 1) for p in self.pairs}
        bl = string.ascii_letters[len(inst.nodes):]
        self.blet = {p: bl[k] for k, p in enumerate(self.pairs)}
        self.inc = [[p for p in self.pairs if i in p] for i in range(r)]
        self.W = [rng.standard_normal([inst.dim[v] for v in g] + [self.bonds[p] for p in self.inc[i]]) * scale for i, g in enumerate(groups)]
        self.out = ''.join(inst.letters[v] for v in inst.nodes)
    def sub(self, i): return ''.join(self.inst.letters[v] for v in self.groups[i]) + ''.join(self.blet[p] for p in self.inc[i])
    def full(self):
        return np.einsum(','.join(self.sub(i) for i in range(len(self.groups))) + '->' + self.out, *self.W, optimize='greedy')
    def update(self, i, T, ridge=1e-10):
        others = [k for k in range(len(self.groups)) if k != i]
        gl = ''.join(self.inst.letters[v] for v in self.groups[i]); bi = ''.join(self.blet[p] for p in self.inc[i])
        rest = ''.join(self.inst.letters[v] for v in self.inst.nodes if v not in self.groups[i])
        env = np.einsum(','.join(self.sub(k) for k in others) + '->' + bi + rest, *[self.W[k] for k in others], optimize='greedy')
        P = int(np.prod([self.bonds[p] for p in self.inc[i]])); env2 = env.reshape(P, -1)
        Tm = np.einsum(self.out + '->' + gl + rest, T).reshape(-1, env2.shape[1])
        Gm = env2 @ env2.T; Gm += ridge * np.trace(Gm) / P * np.eye(P) + 1e-300 * np.eye(P)
        Wm = np.linalg.solve(Gm, (Tm @ env2.T).T).T   # (Tm @ env2.T): avoids an OpenBLAS slow path
        self.W[i] = Wm.reshape(self.W[i].shape)

def als(inst, specs, rng, sweeps=100, tol=1e-10, verbose=False):
    """specs: list of (groups, bonds).  returns best relative residual and nets."""
    f = inst.f; nf = np.linalg.norm(f)
    nets = [Net(inst, g, b, rng, scale=0.5) for g, b in specs]
    parts = [n.full() for n in nets]; best = np.inf; hist = []
    for s in range(sweeps):
        for t, n in enumerate(nets):
            T = f - sum(parts[u] for u in range(len(nets)) if u != t)
            for i in range(len(n.groups)): n.update(i, T)
            parts[t] = n.full()
        res = np.linalg.norm(f - sum(parts)) / nf; hist.append(res)
        best = min(best, res)
        if verbose: print(s, res, flush=True)
        if res < tol: break
        if s > 30 and hist[-30] - res < 1e-7 * max(res, 1e-12): break   # stalled
    return best, nets, len(hist)
