"""Core utilities for the derandomization track (Track E).

Graphs are given as (n, edges) with edges a list of (u, v) pairs, u < v.
Hamiltonian cycles are returned as edge bitmasks (int), bit i <-> edges[i].

Key quantity (see derandomization.md, Lemma 1 / Theorem 1):
    c_T = #{H in HC(G) : T subset H}
    t_q(G) = min{|T| : c_T != 0 mod q}
and t_Q = min over a set of moduli.  By Mobius inversion, t_q is also the minimum
size |F|+|D| of a restriction (force F, delete D) whose HC count is nonzero mod q.
"""
import itertools
import random
from collections import Counter

import networkx as nx


def edge_index(edges):
    return {e: i for i, e in enumerate(edges)}


def normalize(edges):
    return sorted({(min(u, v), max(u, v)) for u, v in edges if u != v})


def ham_cycles(n, edges):
    """All Hamiltonian cycles as edge bitmasks (each undirected cycle once)."""
    if n < 3:
        return []
    idx = edge_index(edges)
    adj = [[] for _ in range(n)]
    for (u, v), i in idx.items():
        adj[u].append((v, i))
        adj[v].append((u, i))
    if any(len(a) < 2 for a in adj):
        return []
    res = []
    start = 0
    full = (1 << n) - 1
    # closing edges at start
    start_nb = {v: i for v, i in adj[start]}
    path_first = [None]

    def dfs(v, visited, mask, depth, first):
        if depth == n:
            if v in start_nb and first < v:
                res.append(mask | (1 << start_nb[v]))
            return
        for w, i in adj[v]:
            if not (visited >> w) & 1:
                # pruning: unvisited vertex with < 2 available neighbours
                dfs(w, visited | (1 << w), mask | (1 << i), depth + 1,
                    first if first is not None else w)

    # iterative-friendly recursion; n <= ~26 fine
    for w, i in adj[start]:
        dfs(w, (1 << start) | (1 << w), 1 << i, 2, w)
    return res


def ham_cycles_fast(n, edges):
    """Same as ham_cycles but with degree pruning (faster on cubic graphs)."""
    idx = edge_index(edges)
    adj = [[] for _ in range(n)]
    for (u, v), i in idx.items():
        adj[u].append((v, i))
        adj[v].append((u, i))
    if n < 3 or any(len(a) < 2 for a in adj):
        return []
    nbmask = [0] * n
    for v in range(n):
        for w, _ in adj[v]:
            nbmask[v] |= 1 << w
    res = []
    start = 0
    start_nb = {v: i for v, i in adj[start]}

    def ok(visited, v):
        # every unvisited vertex needs >= 2 neighbours among unvisited + {v, start}
        free = ~visited
        avail = free | (1 << v) | (1 << start)
        u = free & ((1 << n) - 1)
        while u:
            b = u & -u
            x = b.bit_length() - 1
            if bin(nbmask[x] & avail).count("1") < 2:
                return False
            u ^= b
        return True

    def dfs(v, visited, mask, depth, first):
        if depth == n:
            if v in start_nb and first < v:
                res.append(mask | (1 << start_nb[v]))
            return
        if depth % 3 == 0 and not ok(visited, v):
            return
        for w, i in adj[v]:
            if not (visited >> w) & 1:
                dfs(w, visited | (1 << w), mask | (1 << i), depth + 1, first)

    for w, i in adj[start]:
        dfs(w, (1 << start) | (1 << w), 1 << i, 2, w)
    return res


def bits(mask):
    out = []
    while mask:
        b = mask & -mask
        out.append(b.bit_length() - 1)
        mask ^= b
    return out


def t_value(hcs, moduli, smax=None):
    """min |T| with c_T != 0 mod q for some q in moduli; returns (t, q, T) or (None,..)."""
    if not hcs:
        return None, None, None
    n = len(bits(hcs[0]))
    smax = n if smax is None else smax
    for s in range(0, smax + 1):
        cnt = Counter()
        for h in hcs:
            for T in itertools.combinations(bits(h), s):
                cnt[T] += 1
        for T, c in cnt.items():
            for q in moduli:
                if c % q:
                    return s, q, T
    return None, None, None


def t_per_modulus(hcs, moduli, smax=None):
    """dict q -> t_q, computed jointly."""
    if not hcs:
        return {q: None for q in moduli}
    n = len(bits(hcs[0]))
    smax = n if smax is None else smax
    out = {}
    for s in range(0, smax + 1):
        todo = [q for q in moduli if q not in out]
        if not todo:
            break
        cnt = Counter()
        for h in hcs:
            for T in itertools.combinations(bits(h), s):
                cnt[T] += 1
        vals = list(cnt.values())
        for q in todo:
            if any(c % q for c in vals):
                out[q] = s
    for q in moduli:
        out.setdefault(q, None)
    return out


def random_regular(n, d, rng):
    while True:
        G = nx.random_regular_graph(d, n, seed=rng.randrange(1 << 30))
        if nx.is_connected(G):
            return n, normalize(G.edges())


def random_maxdeg(n, d, m, rng):
    """Random connected graph, max degree d, m edges, min degree 2."""
    for _ in range(10000):
        n_, edges = random_regular(n, d, rng)
        rng.shuffle(edges)
        deg = Counter()
        for u, v in edges:
            deg[u] += 1
            deg[v] += 1
        kept = list(edges)
        excess = len(edges) - m
        for e in list(edges):
            if excess <= 0:
                break
            u, v = e
            if deg[u] > 2 and deg[v] > 2:
                kept.remove(e)
                deg[u] -= 1
                deg[v] -= 1
                excess -= 1
        G = nx.Graph(kept)
        G.add_nodes_from(range(n))
        if excess <= 0 and nx.is_connected(G):
            return n, normalize(kept)
    raise RuntimeError


def double_edge_swap(n, edges, rng):
    G = nx.Graph(edges)
    G.add_nodes_from(range(n))
    nx.double_edge_swap(G, nswap=1, max_tries=1000, seed=rng.randrange(1 << 30))
    return n, normalize(G.edges())


def necklace(gadgets):
    """Cycle of 2-terminal gadgets. gadget = (k, edges, a, d) with terminals a, d.
    Returns (n, edges)."""
    edges = []
    off = 0
    ends = []
    for (k, ge, a, d) in gadgets:
        edges += [(u + off, v + off) for u, v in ge]
        ends.append((a + off, d + off))
        off += k
    for i in range(len(ends)):
        edges.append((ends[i][1], ends[(i + 1) % len(ends)][0]))
    return off, normalize(edges)


DIAMOND = (4, [(0, 1), (1, 2), (2, 3), (0, 2), (1, 3)], 0, 3)
