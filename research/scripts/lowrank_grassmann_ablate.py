"""Ablation: is the blob-level crossing sign (-1)^{sum_{interleaving ab,cd} P_ab P_cd} needed?
For K=4,5 partitions, compare Z(full sign), Z(local signs only), Z(no sign) with n*#HC.
Also reports the label budget: log2(5) bits per crossing edge + one parity bit per (pair, pair)."""
import itertools, random, math
import numpy as np
import networkx as nx
from lowrank_grassmann import build, count_hc

def Zvariants(G, blob, r=0):
    cross, W, K = build(G, blob, r)
    m = len(cross)
    ba = [blob[u] for u, v in cross]; bb = [blob[v] for u, v in cross]
    labs = np.array(list(itertools.product(range(5), repeat=m)), dtype=np.int64).reshape(-1, m)
    pi = ((labs == 2) | (labs == 3)).astype(np.int64)
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
    loc = np.zeros((m, m), dtype=np.int64)
    for k in range(m):
        for l in range(k + 1, m):
            if len({ba[k], bb[k], ba[l], bb[l]}) < 4:
                loc[k, l] = (int(ba[l] < ba[k]) + int(ba[l] < bb[k]) + int(bb[l] < ba[k]) + int(bb[l] < bb[k])) % 2
    ql = np.einsum('nk,kl,nl->n', pi, loc, pi)
    pairs = sorted({(ba[k], bb[k]) for k in range(m)})
    P = {p: np.zeros(len(labs), dtype=np.int64) for p in pairs}
    for k in range(m):
        P[(ba[k], bb[k])] += pi[:, k]
    qi = np.zeros(len(labs), dtype=np.int64); ninter = 0
    for (a1, b1) in pairs:
        for (a2, b2) in pairs:
            if a1 < a2 < b1 < b2:
                qi = qi + P[(a1, b1)] * P[(a2, b2)]; ninter += 1
    s = lambda q: 1 - 2 * (q % 2)
    return (int(np.sum(tot * s(ql + qi))), int(np.sum(tot * s(ql))), int(np.sum(tot)), m, ninter)

rng = random.Random(3)
gs = {'K5': nx.complete_graph(5), 'K33': nx.complete_bipartite_graph(3, 3),
      'prism': nx.circular_ladder_graph(3), 'wheel6': nx.wheel_graph(6),
      'cube': nx.hypercube_graph(3), 'K6': nx.complete_graph(6)}
print("graph  K  m_cross  #interleaving-pair-pairs  n#HC  Z_full  Z_localonly  Z_nosign")
for name, G in gs.items():
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes(); hc = count_hc(G)
    done = 0
    for trial in range(200):
        K = rng.choice([4, 5])
        if K > n:
            continue
        nodes = list(G.nodes()); rng.shuffle(nodes)
        blob = {v: i % K for i, v in enumerate(nodes)}
        m = sum(1 for e in G.edges() if blob[e[0]] != blob[e[1]])
        if m > 9:
            continue
        zf, zl, zn, m, ni = Zvariants(G, blob)
        if ni == 0:
            continue
        print(f"{name:6s} {K}  {m:3d}  {ni:3d}  {n*hc:5d}  {zf:6d}  {zl:6d}  {zn:6d}", flush=True)
        done += 1
        if done == 3:
            break
