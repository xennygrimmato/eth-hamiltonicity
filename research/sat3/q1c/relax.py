"""Convex relaxation giving an UPPER bound on the CAT(0) price value of Delta_3 (and of other small nets).

Unknowns (all reduced modulo the automorphism group of the configuration):
  D(p,q)   squared distances on a finite point set  P = hubs + auxiliary points (midpoints, barycentres)
  dd(p,q)  with dd^2 <= D   (a lower bound for the distance; = sqrt(D) at a true placement)
  f_eps(p) for each end eps = (edge, node): the function  |leg, p| - |legs of the edge|/2
Valid constraints at every placement in a CAT(0) space (legs anywhere, also at infinity):
  midpoint m of x,v:  D(x,m) = D(v,m) = D(x,v)/4 ;  CN: D(z,m) <= D(z,x)/2 + D(z,v)/2 - D(x,v)/4  for all z
  barycentre b of x1..xr:  D(z,b) <= mean_i D(z,x_i) - mean_i D(b,x_i)                         (C.4(c))
  f convex:  f(m) <= (f(x)+f(v))/2 ,  f(b) <= mean f(x_i)        (distance to a point is convex; Jensen)
  f 1-Lipschitz:  f(p) - f(q) <= dd(p,q)
  f_(e,n) + f_(e,n') >= 0                                         (triangle inequality)
  D(o,o') <= delta_k^2 for hubs of the same merge k
Objective:  sum_k (1/delta_k) sum_e s^k_e ,  s^k_e = - f_(e,n)(o^k(n)) - f_(e,n')(o^k(n'))  = sum_k b_k.
The feasible set is convex (squared metrics of CAT(0) spaces form a convex cone; sqrt is concave), so the optimum is
a rigorous upper bound for sum_k b_k over all CAT(0) placements with the given delta's, up to solver tolerance.
"""
import itertools, sys, time
import numpy as np, scipy.sparse as sp, cvxpy as cp

class Net:
    """3-net of Z_g with classes r, c, r-c; edge set given by a list of differences v (generic)."""
    def __init__(self, g, diffs):
        self.g = g
        self.nodes = [(r, c) for r in range(g) for c in range(g)]
        self.hubs = [(k, v) for k in range(3) for v in range(g)]
        E = set()
        for n in self.nodes:
            for (a, b) in diffs:
                n2 = ((n[0] + a) % g, (n[1] + b) % g)
                E.add(frozenset((n, n2)))
        self.edges = sorted(tuple(sorted(e)) for e in E)
        self.diffs = set()
        for (a, b) in diffs:
            self.diffs.add((a % g, b % g)); self.diffs.add((-a % g, -b % g))
    def hub_of(self, n, k):
        r, c = n
        return (k, [r, c, (r - c) % self.g][k])
    def group(self):
        """automorphisms: n -> M n + t, M invertible mod g, permuting the three classes and preserving the edge set.
        Returned as (node map, hub map)."""
        g = self.g
        out = []
        dirs = [(0, 1), (1, 0), (1, 1)]      # direction vectors of the lines of class r, c, r-c
        for a, b, c, d in itertools.product(range(g), repeat=4):
            det = (a * d - b * c) % g
            if np.gcd(det, g) != 1: continue
            M = lambda n: ((a * n[0] + b * n[1]) % g, (c * n[0] + d * n[1]) % g)
            # must permute the three classes
            perm = []
            ok = True
            for k in range(3):
                im = M(dirs[k])
                kk = [j for j in range(3) if (im[0] * dirs[j][1] - im[1] * dirs[j][0]) % g == 0]
                if len(kk) != 1: ok = False; break
                perm.append(kk[0])
            if not ok or sorted(perm) != [0, 1, 2]: continue
            if any(M(v) not in self.diffs for v in self.diffs): continue
            for t in itertools.product(range(g), repeat=2):
                nm = {n: ((M(n)[0] + t[0]) % g, (M(n)[1] + t[1]) % g) for n in self.nodes}
                hm = {}
                for n in self.nodes:
                    for k in range(3):
                        hm[self.hub_of(n, k)] = self.hub_of(nm[n], perm[k])
                out.append((nm, hm))
        return out

def canon_mid(a, b):
    return ('m',) + tuple(sorted((a, b), key=repr))
def canon_bar(xs):
    return ('b',) + tuple(sorted(xs, key=repr))

def act(pt, hm):
    if pt[0] == 'h': return ('h',) + hm[pt[1:]]
    if pt[0] == 'm': return canon_mid(act(pt[1], hm), act(pt[2], hm))
    if pt[0] == 'b': return canon_bar([act(x, hm) for x in pt[1:]])
    raise ValueError

def close(points, G):
    S = set()
    for p in points:
        for (_, hm) in G:
            S.add(act(p, hm))
    return S

def solve(net, extra_points, deltas=(1.0, 1.0, 1.0), verbose=True, solver='CLARABEL', lazy_triangle=0):
    t0 = time.time()
    G = net.group()
    hubs = [('h',) + h for h in net.hubs]
    pts = set(hubs) | close(extra_points, G)
    # make sure parents of auxiliary points are present
    changed = True
    while changed:
        changed = False
        for p in list(pts):
            if p[0] in 'mb':
                for x in p[1:]:
                    if x not in pts: pts.add(x); changed = True
    pts = sorted(pts, key=lambda p: (len(repr(p)), repr(p)))
    idx = {p: i for i, p in enumerate(pts)}
    N = len(pts)
    ng = len(G)
    PP = np.array([[idx[act(p, hm)] for p in pts] for (_, hm) in G])        # ng x N
    ends = [(e, n) for e in net.edges for n in e]
    eidx = {x: i for i, x in enumerate(ends)}
    EP = np.array([[eidx[(tuple(sorted((nm[e[0]], nm[e[1]]))), nm[n])] for (e, n) in ends] for (nm, _) in G])
    # orbit ids for pairs
    I, J = np.triu_indices(N, 1)
    a = PP[:, I]; b = PP[:, J]
    code = (np.minimum(a, b) * N + np.maximum(a, b)).min(axis=0)
    uniq, inv = np.unique(code, return_inverse=True)
    nD = len(uniq)
    pair_id = np.full((N, N), -1, dtype=np.int64)
    pair_id[I, J] = inv; pair_id[J, I] = inv
    # orbit ids for (end, point)
    nE = len(ends)
    EE, QQ = np.meshgrid(np.arange(nE), np.arange(N), indexing='ij')
    EE = EE.ravel(); QQ = QQ.ravel()
    codeF = (EP[:, EE] * N + PP[:, QQ]).min(axis=0)
    uniqF, invF = np.unique(codeF, return_inverse=True)
    nF = len(uniqF)
    f_id = invF.reshape(nE, N)
    if verbose: print(f"points {N}, group {ng}, D-orbits {nD}, f-orbits {nF}, setup {time.time()-t0:.1f}s", flush=True)
    nx = 2 * nD + nF
    Dv = lambda p, q: int(pair_id[p, q])
    dv = lambda p, q: nD + int(pair_id[p, q])
    Fv = lambda e, p: 2 * nD + int(f_id[e, p])
    rows_le = set(); rows_eq = set()
    def add(coefs, rhs, eq=False):
        acc = {}
        for v, c in coefs:
            acc[v] = acc.get(v, 0.0) + c
        key = (tuple(sorted((v, round(c, 12)) for v, c in acc.items() if abs(c) > 1e-14)), round(rhs, 12))
        if not key[0]:
            return
        (rows_eq if eq else rows_le).add(key)
    e0 = 0                                   # one end suffices: the group is transitive on ends (checked below)
    assert len(set(EP[:, e0])) == nE, "group not transitive on ends"
    other = {eidx[(e, n)]: eidx[(e, [m for m in e if m != n][0])] for (e, n) in ends}
    for p in pts:
        i = idx[p]
        if p[0] == 'm':
            x, v = idx[p[1]], idx[p[2]]
            add([(Dv(x, i), 1.0), (Dv(x, v), -0.25)], 0.0, eq=True)
            add([(Dv(v, i), 1.0), (Dv(x, v), -0.25)], 0.0, eq=True)
            for z in range(N):
                if z in (i,): continue
                co = [(Dv(z, i), 1.0), (Dv(x, v), 0.25)]
                if z != x: co.append((Dv(z, x), -0.5))
                if z != v: co.append((Dv(z, v), -0.5))
                add(co, 0.0)
            add([(Fv(e0, i), 1.0), (Fv(e0, x), -0.5), (Fv(e0, v), -0.5)], 0.0)
        if p[0] == 'b':
            xs = [idx[x] for x in p[1:]]; r = len(xs)
            for z in range(N):
                if z == i: continue
                co = [(Dv(z, i), 1.0)] + [(Dv(z, x), -1.0 / r) for x in xs if x != z] + [(Dv(i, x), 1.0 / r) for x in xs]
                add(co, 0.0)
            add([(Fv(e0, i), 1.0)] + [(Fv(e0, x), -1.0 / r) for x in xs], 0.0)
    for i in range(N):
        add([(Fv(e0, i), -1.0), (Fv(other[e0], i), -1.0)], 0.0)
        for j in range(N):
            if i != j:
                add([(Fv(e0, i), 1.0), (Fv(e0, j), -1.0), (dv(i, j), -1.0)], 0.0)
    for k in range(3):
        for v1, v2 in itertools.combinations(range(net.g), 2):
            add([(Dv(idx[('h', k, v1)], idx[('h', k, v2)]), 1.0)], deltas[k] ** 2)
    obj = np.zeros(nx)
    for (e, n) in ends:
        for k in range(3):
            obj[Fv(eidx[(e, n)], idx[('h',) + net.hub_of(n, k)])] -= 1.0 / deltas[k]
    def mat(rows):
        r, c, d, rhs = [], [], [], []
        for t, (co, b) in enumerate(rows):
            for v, x in co:
                r.append(t); c.append(v); d.append(x)
            rhs.append(b)
        return sp.csr_matrix((d, (r, c)), shape=(len(rows), nx)), np.array(rhs)
    rows_le = list(rows_le); rows_eq = list(rows_eq)
    A, bA = mat(rows_le); Aeq, beq = mat(rows_eq)
    if verbose: print(f"vars {nx}, ineq {A.shape[0]}, eq {Aeq.shape[0]}, build {time.time()-t0:.1f}s", flush=True)
    x = cp.Variable(nx)
    cons = [A @ x <= bA, x[:2 * nD] >= 0, cp.square(x[nD:2 * nD]) <= x[:nD]]
    if Aeq.shape[0]: cons.append(Aeq @ x == beq)
    tri_rows = []
    it = 0
    while True:
        cc = list(cons)
        if tri_rows:
            # triangle inequalities sqrt(D_xz) <= sqrt(D_xy) + sqrt(D_yz):  D_xz <= D_xy + D_yz + 2 t, t <= geo_mean
            t = cp.Variable(len(tri_rows))
            ia = np.array([r[0] for r in tri_rows]); ib = np.array([r[1] for r in tri_rows]); ic = np.array([r[2] for r in tri_rows])
            cc.append(x[ia] <= x[ib] + x[ic] + 2 * t)
            cc.append(t <= cp.geo_mean(cp.vstack([x[ib], x[ic]]), ) if False else cp.square(t) <= 1e9)  # placeholder (overwritten below)
            cc = cc[:-1]
            for j in range(len(tri_rows)):
                cc.append(cp.quad_over_lin(t[j], x[ib[j]]) <= x[ic[j]])
        prob = cp.Problem(cp.Maximize(obj @ x), cc)
        val = prob.solve(solver=solver, verbose=False)
        if verbose: print(f"  solve {it}: status {prob.status}, bound on sum_k b_k = {val:.6f}  (per merge {val/3:.6f}; |E| = {len(net.edges)}), tri {len(tri_rows)}, {time.time()-t0:.1f}s", flush=True)
        if it >= lazy_triangle or x.value is None: break
        Dm = np.zeros((N, N)); Dm[I, J] = x.value[inv]; Dm[J, I] = Dm[I, J]
        R = np.sqrt(np.maximum(Dm, 0))
        viol = {}
        for y in range(N):
            S = R[:, [y]] + R[[y], :]
            V = R - S
            np.fill_diagonal(V, -1)
            V[y, :] = -1; V[:, y] = -1
            xs, zs = np.where(V > 1e-5)
            for xx, zz in zip(xs, zs):
                if xx < zz:
                    key = (int(pair_id[xx, zz]), *sorted((int(pair_id[xx, y]), int(pair_id[y, zz]))))
                    viol[key] = max(viol.get(key, 0), V[xx, zz])
        if not viol: 
            if verbose: print("  no triangle violations", flush=True)
            break
        new = sorted(viol, key=lambda k: -viol[k])[:400]
        if verbose: print(f"  triangle violations: {len(viol)} orbits-types, max {max(viol.values()):.4f}; adding {len(new)}", flush=True)
        tri_rows = list(dict.fromkeys(tri_rows + new))
        it += 1
    info = dict(N=N, nD=nD, nF=nF, pts=pts, idx=idx, pair_id=pair_id, f_id=f_id, x=x.value, ends=ends, eidx=eidx, inv=inv, I=I, J=J)
    return val, info

def delta3():
    return Net(3, [(1, -1)])

def level_points(net, spec):
    """spec: list of keywords."""
    H = [('h',) + h for h in net.hubs]
    P = []
    nodes = net.nodes
    nodemid = {}
    for n in nodes:
        hs = [('h',) + net.hub_of(n, k) for k in range(3)]
        for a, b in itertools.combinations(hs, 2):
            nodemid.setdefault(n, []).append(canon_mid(a, b))
    if 'nodemid' in spec:
        for n in nodes: P += nodemid[n]
    if 'samemid' in spec:
        for k in range(3):
            for v1, v2 in itertools.combinations(range(net.g), 2):
                P.append(canon_mid(('h', k, v1), ('h', k, v2)))
    if 'nodebar' in spec:
        for n in nodes:
            P.append(canon_bar([('h',) + net.hub_of(n, k) for k in range(3)]))
    if 'edgemid' in spec:      # midpoints between node-midpoints of the two ends of an edge
        for e in net.edges:
            for a in nodemid[e[0]]:
                for b in nodemid[e[1]]:
                    P.append(canon_mid(a, b))
    if 'edgebar' in spec:      # midpoints of the node barycentres along an edge
        for e in net.edges:
            P.append(canon_mid(canon_bar([('h',) + net.hub_of(e[0], k) for k in range(3)]), canon_bar([('h',) + net.hub_of(e[1], k) for k in range(3)])))
    if 'nodemidmid' in spec:   # midpoints between the three node-midpoints of one node
        for n in nodes:
            for a, b in itertools.combinations(nodemid[n], 2):
                P.append(canon_mid(a, b))
    if 'hubnodemid' in spec:   # midpoint between a hub of the node and the midpoint of the other two
        for n in nodes:
            hs = [('h',) + net.hub_of(n, k) for k in range(3)]
            for k in range(3):
                o = [hs[j] for j in range(3) if j != k]
                P.append(canon_mid(hs[k], canon_mid(o[0], o[1])))
    if 'collmid' in spec:      # midpoints between node-midpoints of collinear nodes
        for n, n2 in itertools.combinations(nodes, 2):
            if frozenset((n, n2)) not in set(map(frozenset, net.edges)):
                for a in nodemid[n]:
                    for b in nodemid[n2]:
                        P.append(canon_mid(a, b))
    return P

if __name__ == "__main__":
    net = delta3()
    specs = [[], ['nodemid'], ['nodemid', 'samemid'], ['nodemid', 'nodebar'], ['nodemid', 'samemid', 'nodebar', 'edgebar']]
    if len(sys.argv) > 1:
        specs = [s.split(',') for s in sys.argv[1:]]
    for spec in specs:
        print("spec", spec, flush=True)
        val, info = solve(net, level_points(net, spec), lazy_triangle=3)
