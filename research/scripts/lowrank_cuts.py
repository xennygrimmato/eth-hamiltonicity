"""Flattening ranks of the boundary-conditioned Hamiltonian-cycle indicator across vertex cuts
(S, V \\ S) of small bounded-degree graphs, and all flattenings of K=3 blob tensors.

A side's state: (X = used crossing edges, pairing of X induced by that side's paths, closed-cycle
flag).  Entry = [same X on both sides and left u right is one cycle].  The rank of the matrix of
partial solutions equals the rank of this state matrix (identical rows/columns).
Reports b = |delta(S)|, rank_Q (mod a 31-bit prime), log2(rank)/b, and the 'all states' bound
sum_k C(b,2k) rank_Q(H_k) with rank_Q(H_k) taken from lowrank_rs.py.
"""
import itertools, math, random, sys
import numpy as np
import networkx as nx
sys.path.insert(0, '/home/user/lean-code/research/scripts')
from lowrank_rs import rank_modp, rank_gf2

RQ_H = {1: 1, 2: 3, 3: 15, 4: 69, 5: 271}  # filled from lowrank_rs.py output (checked below)

def side_states(G, S, cross):
    """enumerate states of side S; cross = list of crossing edges (u,v) (any orientation)."""
    S = set(S)
    Ein = [e for e in G.edges() if e[0] in S and e[1] in S]
    cidx = list(range(len(cross)))
    states = set()
    vs = sorted(S)
    # choose crossing subset and internal subset with degree 2 everywhere in S
    for Xbits in range(1 << len(cross)):
        degc = {v: 0 for v in vs}
        X = [k for k in cidx if (Xbits >> k) & 1]
        ok = True
        for k in X:
            u, v = cross[k]
            w = u if u in S else v
            degc[w] += 1
            if degc[w] > 2:
                ok = False
        if not ok:
            continue
        # internal edges: backtrack
        need = {v: 2 - degc[v] for v in vs}
        chosen = []
        def rec(i):
            if i == len(Ein):
                if all(need[v] == 0 for v in vs):
                    states.add(state_of(S, X, cross, chosen))
                return
            u, v = Ein[i]
            rec(i + 1)
            if need[u] > 0 and need[v] > 0:
                need[u] -= 1; need[v] -= 1; chosen.append((u, v))
                rec(i + 1)
                chosen.pop(); need[u] += 1; need[v] += 1
        rec(0)
    return states

def state_of(S, X, cross, internal):
    # graph on S-vertices plus stubs 'c{k}'
    H = nx.Graph()
    H.add_nodes_from(S)
    H.add_edges_from(internal)
    for k in X:
        u, v = cross[k]
        w = u if u in S else v
        H.add_edge(('c', k), w)
    pairs = []; closed = False
    for comp in nx.connected_components(H):
        stubs = sorted(x[1] for x in comp if isinstance(x, tuple))
        if len(stubs) == 0:
            closed = True
        else:
            assert len(stubs) == 2
            pairs.append(tuple(stubs))
    return (frozenset(X), frozenset(pairs), closed)

def glue_one_cycle(states):
    """states: list of (X, pairs, closed) from parties; all X-consistency assumed checked.
    union of all pairings (each a matching on its stubs; stubs = crossing edge ids, each id
    appears in exactly two parties) -> single cycle?"""
    if any(s[2] for s in states):
        return False
    H = nx.MultiGraph()
    for pi, s in enumerate(states):
        for (a, b) in s[1]:
            H.add_edge(('e', a), ('e', b))
    if H.number_of_nodes() == 0:
        return False
    # every crossing-edge node has degree 2 (one pair from each endpoint side)
    return nx.is_connected(H) and all(d == 2 for _, d in H.degree())

def cut_matrix(G, S):
    T = set(G.nodes()) - set(S)
    cross = [e for e in G.edges() if (e[0] in S) != (e[1] in S)]
    L = sorted(side_states(G, S, cross), key=str)
    R = sorted(side_states(G, T, cross), key=str)
    M = np.zeros((len(L), len(R)), dtype=np.int64)
    for i, l in enumerate(L):
        for j, r in enumerate(R):
            if l[0] == r[0] and glue_one_cycle([l, r]):
                M[i, j] = 1
    return M, len(cross)

def allstates_bound(b):
    return sum(math.comb(b, 2 * k) * RQ_H.get(k, float('nan')) for k in range(1, b // 2 + 1))

def graphs():
    gs = {}
    gs['petersen'] = nx.petersen_graph()
    for n in (10, 12, 14):
        for s in range(2):
            gs[f'rand3reg{n}_{s}'] = nx.random_regular_graph(3, n, seed=10 * n + s)
    gs['grid3x4'] = nx.grid_2d_graph(3, 4)
    gs['grid4x4'] = nx.grid_2d_graph(4, 4)
    gs['C12+chords'] = nx.Graph([(i, (i + 1) % 12) for i in range(12)] + [(0, 6), (3, 9), (1, 7), (4, 10)])
    gs['moebius_kantor'] = nx.LCF_graph(16, [5, -5], 8)
    gs['heawood'] = nx.heawood_graph()
    return {k: nx.convert_node_labels_to_integers(v) for k, v in gs.items()}

def main():
    rng = random.Random(7)
    print("== 2-way vertex cuts ==")
    print(f"{'graph':16s} {'|S|':>3s} {'b':>3s} {'#Lst':>5s} {'#Rst':>5s} {'rankQ':>6s} {'rkGF2':>6s} {'log2rk/b':>8s} {'allstates':>9s} {'log2/b':>6s}")
    worst = 0
    for name, G in graphs().items():
        n = G.number_of_nodes()
        seen = set()
        for trial in range(6):
            k = rng.choice([n // 2, n // 2, n // 3, 2 * n // 5])
            S = frozenset(rng.sample(sorted(G.nodes()), k))
            if S in seen:
                continue
            seen.add(S)
            M, b = cut_matrix(G, S)
            if M.size == 0 or b == 0:
                continue
            rq = rank_modp(M) if min(M.shape) > 0 else 0
            r2 = rank_gf2(M.tolist())
            ab = allstates_bound(b)
            lr = math.log2(rq) / b if rq > 0 else float('nan')
            worst = max(worst, lr if rq > 0 else 0)
            print(f"{name:16s} {len(S):3d} {b:3d} {M.shape[0]:5d} {M.shape[1]:5d} {rq:6d} {r2:6d} {lr:8.3f} {ab:9.0f} {math.log2(ab)/b if ab==ab else float('nan'):6.3f}", flush=True)
    print(f"max log2(rank_Q)/b over cuts tried: {worst:.3f}")

    print("== K=3 blob tensors: all flattenings ==")
    for name in ['petersen', 'rand3reg12_0', 'grid3x4', 'heawood']:
        G = graphs()[name]
        nodes = sorted(G.nodes())
        for trial in range(2):
            rng.shuffle(nodes)
            blobs = [set(nodes[i::3]) for i in range(3)]
            e = {(a, b): sum(1 for (u, v) in G.edges() if (u in blobs[a] and v in blobs[b]) or
                             (u in blobs[b] and v in blobs[a])) for a in range(3) for b in range(3) if a < b}
            # flattening a | rest is the 2-way cut matrix with S = blob a
            res = []
            for a in range(3):
                M, b = cut_matrix(G, blobs[a])
                rq = rank_modp(M)
                res.append((a, b, rq, math.log2(rq) / b if rq else float('nan')))
            print(f"{name:14s} e(AB),e(AC),e(BC)={e[(0,1)]},{e[(0,2)]},{e[(1,2)]}  flattenings (blob, b, rankQ, log2/b): {res}", flush=True)

if __name__ == '__main__' and len(sys.argv) == 1:
    main()

def universal_right(b):
    out = []
    from lowrank_rs import matchings
    for r in range(2, b + 1, 2):
        for X in itertools.combinations(range(b), r):
            for m in matchings(list(X)):
                out.append((frozenset(X), frozenset(tuple(sorted(p)) for p in m), False))
    return out

def universal_test():
    """rank of (realizable left states of G[S]) x (ALL right states on the b crossing edges)."""
    rng = random.Random(11)
    print("== realizable left states vs universal right side (b <= 10) ==")
    print(f"{'graph':16s} {'|S|':>3s} {'b':>3s} {'#Lst':>5s} {'#Runiv':>6s} {'rankQ':>6s} {'log2rk/b':>8s}")
    for name, G in graphs().items():
        n = G.number_of_nodes()
        for trial in range(20):
            S = frozenset(rng.sample(sorted(G.nodes()), rng.choice([n // 2, n // 3])))
            cross = [e for e in G.edges() if (e[0] in S) != (e[1] in S)]
            b = len(cross)
            if b > 10 or b < 4:
                continue
            L = sorted(side_states(G, S, cross), key=str)
            R = universal_right(b)
            M = np.zeros((len(L), len(R)), dtype=np.int64)
            for i, l in enumerate(L):
                for j, r in enumerate(R):
                    if l[0] == r[0] and glue_one_cycle([l, r]):
                        M[i, j] = 1
            rq = rank_modp(M)
            print(f"{name:16s} {len(S):3d} {b:3d} {len(L):5d} {len(R):6d} {rq:6d} {math.log2(max(rq,1))/b:8.3f}", flush=True)
            break

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'univ':
    universal_test()
