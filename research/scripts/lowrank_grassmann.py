"""K-blob sum-of-products for n * #HC(G) via the matrix-tree theorem written as a Berezin
(Grassmann) integral, with the fermionic reordering sign made explicit.

Identity checked here (exact integers):

  n * #HC(G) = sum_{x 2-factor} tau(G[x]) = sum_{x 2-factor} det L_x^{(r)}
             = sum_{labels l on crossing edges} eps(l) * prod_a W_a(l restricted to delta(a))

* every crossing edge e=(i in blob a, j in blob b), a<b, carries a label in {N,0,1,2,3}
  (N: x_e=0; 0..3: x_e=1 and which of the 4 Schmidt terms of the edge factor is taken);
* W_a = sum over internal edge choices at blob a, with the degree-2 constraint at every vertex of a,
  of the Berezin integral over blob a's generators of (internal edge factors) * (a's pieces);
* eps(l) = (-1)^{sum_{k<l} pi_k pi_l c_kl}, pi = [label in {2,3}] (odd pieces),
  c_kl = [a_l<a_k]+[a_l<b_k]+[b_l<a_k]+[b_l<b_k] mod 2.
  For edge pairs on four distinct blobs c_kl = [chords {a_k,b_k},{a_l,b_l} interleave on the circle
  1..K]; pairs sharing a blob are local to that blob.  Hence eps = (local signs) *
  (-1)^{sum_{interleaving blob-pairs {ab},{cd}} P_ab P_cd}, P_ab = parity of odd labels on pair ab.
  This is checked too.

Run: python3 lowrank_grassmann.py
"""
import itertools, random, sys
import numpy as np
import networkx as nx

# ---------- tiny Grassmann algebra: element = dict{bitmask: int} ----------
def gmul_mono(m1, m2):
    if m1 & m2:
        return None, 0
    # sign = (-1)^{#pairs (p in m1, q in m2) with p > q}
    s = 0
    x = m2
    while x:
        q = (x & -x).bit_length() - 1
        x &= x - 1
        s += bin(m1 >> (q + 1)).count("1")
    return m1 | m2, (-1) ** (s & 1)

def gmul(A, B):
    out = {}
    for m1, c1 in A.items():
        for m2, c2 in B.items():
            m, s = gmul_mono(m1, m2)
            if m is None:
                continue
            out[m] = out.get(m, 0) + s * c1 * c2
    return {m: c for m, c in out.items() if c}

def gadd(A, B, cb=1):
    out = dict(A)
    for m, c in B.items():
        out[m] = out.get(m, 0) + cb * c
    return {m: c for m, c in out.items() if c}

ONE = {0: 1}

def gen(idx):
    return {1 << idx: 1}

# ---------- graph helpers ----------
def count_hc(G):
    nodes = list(G.nodes()); n = len(nodes)
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [[idx[u] for u in G[v]] for v in nodes]
    cnt = 0
    def dfs(v, visited, length):
        nonlocal cnt
        for u in adj[v]:
            if u == 0 and length == n:
                cnt += 1
            elif not (visited >> u) & 1:
                dfs(u, visited | (1 << u), length + 1)
    dfs(0, 1, 1)
    return cnt // 2

def two_factor_tau_sum(G, r):
    """sum over 2-factors x of det(L_x^{(r)}) -- brute force check."""
    E = list(G.edges()); nodes = list(G.nodes()); n = len(nodes)
    idx = {v: i for i, v in enumerate(nodes)}
    tot = 0
    # enumerate 2-factors by backtracking over edges
    deg = {v: 0 for v in nodes}
    chosen = []
    def rec(k):
        nonlocal tot
        if k == len(E):
            if all(deg[v] == 2 for v in nodes):
                L = np.zeros((n, n))
                for (u, v) in chosen:
                    a, b = idx[u], idx[v]
                    L[a, a] += 1; L[b, b] += 1; L[a, b] -= 1; L[b, a] -= 1
                ri = idx[r]
                M = np.delete(np.delete(L, ri, 0), ri, 1)
                tot += int(round(np.linalg.det(M)))
            return
        u, v = E[k]
        rec(k + 1)
        if deg[u] < 2 and deg[v] < 2:
            deg[u] += 1; deg[v] += 1; chosen.append((u, v))
            rec(k + 1)
            chosen.pop(); deg[u] -= 1; deg[v] -= 1
    rec(0)
    return tot

# ---------- the K-blob construction ----------
def build(G, blob, r):
    """blob: dict vertex -> blob index 0..K-1. Returns (crossing edge list, W tables, K)."""
    nodes = sorted(G.nodes())
    K = max(blob.values()) + 1
    gidx = {}
    for v in nodes:  # psibar_v -> 2v, psi_v -> 2v+1 (canonical order = prod_v psibar_v psi_v)
        gidx[v] = (2 * nodes.index(v), 2 * nodes.index(v) + 1)
    def pb(v):  # psibar
        return {} if v == r else gen(gidx[v][0])
    def ps(v):
        return {} if v == r else gen(gidx[v][1])
    cross = []
    internal = {a: [] for a in range(K)}
    for (u, v) in G.edges():
        if blob[u] == blob[v]:
            internal[blob[u]].append((u, v))
        else:
            if blob[u] > blob[v]:
                u, v = v, u
            cross.append((u, v))  # u in lower blob
    cross.sort()
    def edge_factor(u, v):
        d1 = gadd(pb(u), pb(v), -1); d2 = gadd(ps(u), ps(v), -1)
        return gadd(ONE, gmul(d1, d2))  # 1 + x_e q_e with x_e = 1
    W = {}
    for a in range(K):
        va = [v for v in nodes if blob[v] == a]
        top = 0
        for v in va:
            if v != r:
                top |= (1 << gidx[v][0]) | (1 << gidx[v][1])
        inc = [k for k, (u, v) in enumerate(cross) if blob[u] == a or blob[v] == a]
        table = {}
        for labs in itertools.product(range(5), repeat=len(inc)):  # 4 = N
            lab = dict(zip(inc, labs))
            # pieces of a in global crossing order
            A = ONE
            degc = {v: 0 for v in va}
            for k in inc:
                u, v = cross[k]; l = lab[k]
                if l != 4:
                    degc[u if blob[u] == a else v] += 1
                if blob[u] == a:  # alpha side, vertex i=u
                    i = u
                    piece = {4: ONE, 0: ONE, 1: gmul(pb(i), ps(i)), 2: pb(i), 3: ps(i)}[l]
                else:  # beta side, vertex j=v
                    j = v
                    piece = {4: ONE, 0: gadd(ONE, gmul(pb(j), ps(j))), 1: ONE,
                             2: {m: -c for m, c in ps(j).items()}, 3: pb(j)}[l]
                A = gmul(A, piece)
                if not A:
                    break
            if not A or any(degc[v] > 2 for v in va):
                table[labs] = 0
                continue
            val = 0
            ints = internal[a]
            for xs in itertools.product((0, 1), repeat=len(ints)):
                dg = dict(degc)
                F = ONE
                for x, (u, v) in zip(xs, ints):
                    if x:
                        dg[u] += 1; dg[v] += 1
                        F = gmul(F, edge_factor(u, v))
                if any(dg[v] != 2 for v in va):
                    continue
                P = gmul(F, A)
                val += P.get(top, 0)
            table[labs] = val
        W[a] = (inc, table)
    return cross, W, K

def contract(cross, W, K, blob, check_formula=True):
    m = len(cross)
    ba = [blob[u] for u, v in cross]; bb = [blob[v] for u, v in cross]
    c = np.zeros((m, m), dtype=np.int64)
    for k in range(m):
        for l in range(k + 1, m):
            c[k, l] = (int(ba[l] < ba[k]) + int(ba[l] < bb[k]) + int(bb[l] < ba[k])
                       + int(bb[l] < bb[k])) % 2
    labs = np.array(list(itertools.product(range(5), repeat=m)), dtype=np.int64).reshape(-1, m)
    pi = ((labs == 2) | (labs == 3)).astype(np.int64)
    eps = 1 - 2 * ((np.einsum('nk,kl,nl->n', pi, c, pi)) % 2)
    tot = np.ones(len(labs), dtype=np.int64)
    for a in range(K):
        inc, table = W[a]
        arr = np.zeros(5 ** len(inc), dtype=np.int64)
        for key, val in table.items():
            arr[int(sum(d * 5 ** (len(inc) - 1 - t) for t, d in enumerate(key)))] = val
        code = np.zeros(len(labs), dtype=np.int64)
        for k in inc:
            code = code * 5 + labs[:, k]
        tot = tot * arr[code]
    Z = int(np.sum(tot * eps))
    ok_formula = None
    if check_formula:
        # local + interleaving decomposition of eps
        loc = np.zeros((m, m), dtype=np.int64)
        for k in range(m):
            for l in range(k + 1, m):
                if len({ba[k], bb[k], ba[l], bb[l]}) < 4:
                    loc[k, l] = c[k, l]
        pairs = sorted({(ba[k], bb[k]) for k in range(m)})
        P = {p: np.zeros(len(labs), dtype=np.int64) for p in pairs}
        for k in range(m):
            P[(ba[k], bb[k])] += pi[:, k]
        q = np.einsum('nk,kl,nl->n', pi, loc, pi)
        for (a1, b1) in pairs:
            for (a2, b2) in pairs:
                if (a1 < a2 < b1 < b2):
                    q = q + P[(a1, b1)] * P[(a2, b2)]
        eps2 = 1 - 2 * (q % 2)
        ok_formula = bool(np.all(eps2 == eps))
    return Z, ok_formula

def random_partition(G, K, rng):
    nodes = list(G.nodes()); rng.shuffle(nodes)
    return {v: i % K for i, v in enumerate(nodes)}

def main():
    rng = random.Random(1)
    graphs = {
        'K4': nx.complete_graph(4),
        'prism': nx.circular_ladder_graph(3),
        'K33': nx.complete_bipartite_graph(3, 3),
        'cube': nx.convert_node_labels_to_integers(nx.hypercube_graph(3)),
        'K5': nx.complete_graph(5),
        'wheel6': nx.wheel_graph(6),
        'C8+chords': nx.Graph([(i, (i + 1) % 8) for i in range(8)] + [(0, 4), (2, 6), (1, 5)]),
        'grid2x4': nx.convert_node_labels_to_integers(nx.grid_2d_graph(2, 4)),
        'petersen': nx.petersen_graph(),
        'rand3reg8': nx.random_regular_graph(3, 8, seed=3),
        'rand3reg10': nx.random_regular_graph(3, 10, seed=5),
    }
    print(f"{'graph':12s} {'n':>3s} {'#HC':>4s} {'n#HC':>5s} {'sum tau':>7s}  K  m_cross  Z(blob)  eps-formula")
    allok = True
    for name, G in graphs.items():
        G = nx.convert_node_labels_to_integers(G)
        n = G.number_of_nodes(); hc = count_hc(G); r = 0
        st = two_factor_tau_sum(G, r)
        for K in (2, 3, 4, 5):
            if K > n:
                continue
            for trial in range(30):
                blob = random_partition(G, K, rng)
                cross0 = [e for e in G.edges() if blob[e[0]] != blob[e[1]]]
                maxinc = max(sum(1 for e in cross0 if blob[e[0]] == a or blob[e[1]] == a) for a in range(K))
                if len(cross0) > 9 or maxinc > 7:
                    continue
                cross, W, KK = build(G, blob, r)
                Z, okf = contract(cross, W, KK, blob)
                ok = (Z == n * hc == st) and okf
                allok &= ok
                print(f"{name:12s} {n:3d} {hc:4d} {n*hc:5d} {st:7d}  {K}  {len(cross):5d}  {Z:7d}  {okf}  {'OK' if ok else 'FAIL'}")
                break
    print("ALL OK" if allok else "SOME FAILURE")

if __name__ == '__main__':
    main()
