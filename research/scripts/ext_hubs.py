"""Bit-budget checks for the blob network (Lemma 8 needs a per-node bound P with gP/K small).

1. Ghost / root vertex: the root has no generators, so an edge (v, root) with no degree test at
   the root costs 0 bits (1 label) -- the ghost of the forest/matrix-forest theorem is free.
   Check: rooted spanning forests of G = det(L+I) = tau(G + ghost), via the network.
2. Label counts per crossing edge for Steiner forest with c colours (bits grow like log2(4c+1)).
3. Hub splitting: replacing a vertex h by a path h_1..h_k of copies joined by *forced* edges
   (factor q_e, copies share y) preserves #subtrees containing T and #induced forests, and
   brings max degree down to O(avg degree).  Checked by brute force on both graphs.
4. HC-type problems: a hub needs no splitting -- with deg_x(h) = 2 the number of realisable
   labelings of h's d crossing edges is 1 + 4d + 16 C(d,2) = O(d^2) instead of 5^d.

Run: python3 ext_hubs.py
"""
import itertools, random, math
from fractions import Fraction
from ext_engine import (Spec, ONE, ZERO, gmul, gadd, gscale, gexp, det_exact, network_value,
                        random_blobs, crossing_ok, decompose_edge)
from ext_problems import (rand_graph, laplacian, minor, components, subtrees, SFSpec,
                          ForestSpec, kron_decode)

ok_all = True

# ---------------------------------------------------------------- 1. ghost
class GhostSpec(Spec):
    def __init__(s, n, E, ghost):
        s.n, s.edges, s.ghost = n, E, ghost
        s._inc = {v: [k for k, e in enumerate(E) if v in e] for v in range(n)}
    def incident(s, v): return s._inc[v]
    def gens(s, v): return v != s.ghost
    def F(s, k, a, b, sig):
        u, v = s.edges[k]
        return gadd(ONE, s.q_undirected(u, v))

rng = random.Random(7)
for trial in range(4):
    n = 6; E = rand_graph(n, 8, rng)
    L = laplacian(list(range(n)), E)
    for i in range(n):
        L[i][i] += 1
    target = det_exact(L)
    g = n
    E2 = E + [(v, g) for v in range(n)]
    sp = GhostSpec(n + 1, E2, g)
    bl = random_blobs(n + 1, 3, rng)
    while not crossing_ok(E2, bl, 9, 9):
        bl = random_blobs(n + 1, 3, rng)
    Z, bits, net = network_value(sp, bl)
    ghost_bits = [bits[k] for k in bits if g in E2[k]]
    ok = Z == target and all(b_ == 1 for b_ in ghost_bits)
    ok_all &= ok
    print(f"1 ghost: rooted forests={target} network={Z}  labels on ghost edges={ghost_bits}  {'OK' if ok else 'FAIL'}")

# ---------------------------------------------------------------- 2. Steiner forest colours
for c in range(1, 5):
    n = 2; E = [(0, 1)]
    sp = SFSpec(n, E, {}, (), c, lambda k: 1)
    labs = decompose_edge(sp, 0, 0, 1)
    print(f"2 Steiner forest with {c} colour classes: {len(labs)} labels per crossing edge "
          f"= {math.log2(len(labs)):.2f} bits (4c+1 = {4 * c + 1})")
    ok_all &= len(labs) == 4 * c + 1

# ---------------------------------------------------------------- 3. hub splitting
def split_hub(n, E, h, k):
    """replace h by copies h=c_0, c_1..c_{k-1} (new ids n..n+k-2), path edges forced.
    h's edges dealt round-robin to the copies."""
    copies = [h] + list(range(n, n + k - 1))
    nb = [e for e in E if h in e]
    rest = [e for e in E if h not in e]
    newE = list(rest)
    for t, (a, b) in enumerate(nb):
        o = b if a == h else a
        c = copies[t % k]
        newE.append((min(o, c), max(o, c)))
    path = [(copies[t], copies[t + 1]) for t in range(k - 1)]
    return n + k - 1, newE, path, copies

class SplitSteinerSpec(Spec):
    def __init__(s, n, E, forced, term, root):
        s.n, s.edges, s.forced, s.term, s.root = n, E, set(forced), set(term), root
        s._inc = {v: [k for k, e in enumerate(E) if v in e] for v in range(n)}
    def incident(s, v): return s._inc[v]
    def gens(s, v): return v != s.root
    def vstates(s, v): return [1] if v in s.term else [0, 1]
    def M(s, v, y): return ONE if y else s.pbps(v)
    def F(s, k, yu, yv, sig):
        u, v = s.edges[k]
        if k in s.forced:
            if yu != yv:
                return ZERO
            return s.q_undirected(u, v) if yu else ONE
        if yu and yv:
            return gadd(ONE, s.q_undirected(u, v))
        return ONE

def induced_forests(n, E):
    cnt = 0
    for r in range(n + 1):
        for S in itertools.combinations(range(n), r):
            ES = [e for e in E if e[0] in S and e[1] in S]
            if not components(sorted(S), ES)[1]:
                cnt += 1
    return cnt

for trial in range(4):
    n = 7
    # a hub: vertex 0 adjacent to everything, plus a sparse rest
    rest = rand_graph(n - 1, n, rng, connected=False)
    E = sorted({(0, v) for v in range(1, n)} | {(a + 1, b + 1) for a, b in rest})
    term = [1, 2] if trial % 2 else [0, 3]
    base = len(subtrees(n, E, term))
    n2, E2, path, copies = split_hub(n, E, 0, 3)
    forced = [E2.index(p) for p in path] if all(p in E2 for p in path) else None
    if forced is None:
        E2 = E2 + path; forced = list(range(len(E2) - len(path), len(E2)))
    term2 = term
    root = term2[0]
    sp = SplitSteinerSpec(n2, E2, forced, term2, root)
    bl = random_blobs(n2, 3, rng)
    tries = 0
    while not crossing_ok(E2, bl, 8, 6) and tries < 500:
        bl = random_blobs(n2, 3, rng); tries += 1
    Z, bits, _ = network_value(sp, bl)
    # degrees
    d1 = max(sum(1 for e in E if v in e) for v in range(n))
    d2 = max(sum(1 for e in E2 if v in e) for v in range(n2))
    ok = Z == base
    ok_all &= ok
    print(f"3 hub split (Steiner, T={term}): #subtrees G={base}  network on split G'={Z}  "
          f"maxdeg {d1}->{d2}  {'OK' if ok else 'FAIL'}")
    # induced forests: copies must agree; forest identity applied to G' counts S' with copies
    # all-in or all-out.  Check by brute force (combinatorially).
    cnt_split = 0
    for r in range(n2 + 1):
        for S in itertools.combinations(range(n2), r):
            Sset = set(S)
            ins = [c in Sset for c in copies]
            if any(ins) and not all(ins):
                continue
            ES = [e for e in E2 if e[0] in Sset and e[1] in Sset]
            if not components(sorted(S), ES)[1]:
                cnt_split += 1
    cf = induced_forests(n, E)
    ok = cf == cnt_split
    ok_all &= ok
    print(f"3 hub split (induced forests): G={cf}  G' (copies tied)={cnt_split}  {'OK' if ok else 'FAIL'}")

# ---------------------------------------------------------------- 4. HC hub label compression
for d in (2, 4, 8, 16, 64):
    real = 1 + 4 * d + 16 * math.comb(d, 2)
    print(f"4 deg-2 hub with {d} crossing edges: {real} realisable labelings "
          f"({math.log2(real):.1f} bits) vs 5^d ({d * math.log2(5):.1f} bits)")

print("ALL OK" if ok_all else "SOME FAILURE")
