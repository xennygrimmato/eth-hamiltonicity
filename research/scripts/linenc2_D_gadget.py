"""Loophole 2: a linear-size signed gadget from a 'nowhere-zero local turn labelling'.

Definition.  A turn at v is an ordered pair (e_in, e_out) of distinct edges at v.  A k-labelling
is F: turns -> GF(2)^k; F(C) := XOR of F over the turns of a directed cycle C.  F is
*nowhere-zero* (for root r) if F(C) != 0 for every directed simple cycle C of G - r.

Gadget.  Give every mixed edge a colour chi in GF(2)^k \\ {0}, equal along the mixed arcs (local:
in-colour = out-colour at every mixed vertex).  Weight of a coloured labelling:
        (-1)^{ sum_v  chi_v . F_v(turn at v) }   (local: O(k) gates per vertex).
Since sum_{chi != 0} (-1)^{chi.y} = -1 for y != 0, each mixed cycle contributes exactly -1, so
        sum_{eta valid} sum_{colourings} weight = sum_eta (-1)^{c(eta)} = n * #HC(G).
Size: O(k m) extra variables (k bits per edge) -- linear when k = O(1).

Checks:
 (a) k=1 nowhere-zero labellings exist for the planar test graphs and NOT for K5, K3,3, nor for a
     subdivided K3,3 / K5 inside random graphs (so k=1 <=> planar, via Kuratowski + subdivision lemma);
 (b) for random graphs (n<=8) a k=2 labelling is found by local search, and then labelling by labelling
     sum over colourings == (-1)^c, and the total == n*#HC (exact integers);
 (c) Ramsey obstruction: on 6 ordered vertices there is a directed cycle in which each of the 6
     order-types of turns occurs an even number of times (so order-type labellings vanish on it).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from linenc2_lib import *  # noqa


def xor_search(nv, cons, k, rng, flips=60000, restarts=30):
    """min-conflicts: values in [0, 2^k), constraint XOR != 0."""
    occ = [[] for _ in range(nv)]
    for ci, c in enumerate(cons):
        for t in c: occ[t].append(ci)
    K = 1 << k
    for rs in range(restarts):
        val = [rng.randrange(K) for _ in range(nv)]
        s = [0] * len(cons)
        for ci, c in enumerate(cons):
            for t in c: s[ci] ^= val[t]
        bad = set(i for i, x in enumerate(s) if x == 0)
        for it in range(flips):
            if not bad: return val
            ci = rng.choice(tuple(bad))
            best, cand = None, []
            for t in cons[ci]:
                for a in range(K):
                    if a == val[t]: continue
                    d = a ^ val[t]
                    delta = sum(((s[cj] ^ d) == 0) - (s[cj] == 0) for cj in occ[t])
                    if best is None or delta < best: best, cand = delta, [(t, a)]
                    elif delta == best: cand.append((t, a))
            if best > 0 and rng.random() < 0.25:
                t = rng.choice(cons[ci]); a = rng.randrange(K)
            else:
                t, a = rng.choice(cand)
            d = a ^ val[t]; val[t] = a
            for cj in occ[t]:
                s[cj] ^= d
                if s[cj] == 0: bad.add(cj)
                else: bad.discard(cj)
    return None


def cons_of(n, edges, r=None):
    E = eid_map(edges); T = turn_index(n, edges)
    cyc = [c for c in directed_simple_cycles(n, edges) if r is None or r not in c]
    return T, E, cyc, [cycle_turns(c, E, T) for c in cyc]


rng = random.Random(777)
fails = dict(a=0, b_found=0, b_cycle=0, b_total=0, c=0)
st = dict(graphs=0, labellings=0, colourings=0)
# (a)
K5 = [(i, j) for i in range(5) for j in range(i + 1, 5)]
K33 = [(i, j) for i in range(3) for j in range(3, 6)]
def subdivide(n, edges, times, rng):
    edges = list(edges)
    for _ in range(times):
        k = rng.randrange(len(edges)); a, b = edges.pop(k)
        edges += [tuple(sorted((a, n))), tuple(sorted((b, n)))]; n += 1
    return n, edges
planar = [(4, [(i, j) for i in range(4) for j in range(i + 1, 4)]),
          (8, [(a, b) for a in range(8) for b in range(a + 1, 8) if bin(a ^ b).count('1') == 1]),
          (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5), (0, 4)])]
for n, E in planar:
    if not local_gf2_certificate(n, E): fails['a'] += 1
for n, E in [(5, K5), (6, K33), subdivide(6, K33, 2, rng), subdivide(5, K5, 2, rng)]:
    if local_gf2_certificate(n, E): fails['a'] += 1
    # embed in a random supergraph
    extra = [(i, j) for i in range(n) for j in range(i + 1, n) if (i, j) not in E]
    E2 = sorted(set(E) | set(rng.sample(extra, min(3, len(extra)))))
    if local_gf2_certificate(n, E2): fails['a'] += 1
# (b)
for trial in range(40):
    n = rng.randint(5, 8)
    m = rng.randint(n + 2, min(n * (n - 1) // 2, 2 * n + 1))
    edges = random_graph(n, m, rng, min_deg2=True)
    r = rng.randrange(n)
    T, E, cyc, cons = cons_of(n, edges, r)
    F = xor_search(len(T), cons, 2, rng) if cons else [0] * len(T)
    if F is None:
        fails['b_found'] += 1; continue
    st['graphs'] += 1
    total = 0
    for lab in valid_labellings(n, edges, r):
        st['labellings'] += 1
        A = arcs(lab); succ = dict(A); pred = {b: a for a, b in A}
        # enumerate colourings: one colour per mixed cycle is forced by equality; enumerate per edge
        # literally (all assignments of colours to mixed edges, keep those constant along arcs)
        mixed_e = [E[frozenset(a)] for a in A]
        s = 0
        for cols in itertools.product(range(1, 4), repeat=len(A)):
            col = dict(zip(A, cols))
            if any(col[(pred[v], v)] != col[(v, succ[v])] for v in succ):
                continue
            st['colourings'] += 1
            e = 0
            for v in succ:
                t = T[(v, E[frozenset((pred[v], v))], E[frozenset((v, succ[v]))])]
                e ^= bin(col[(v, succ[v])] & F[t]).count('1') & 1
            s += (-1) ** e
        if s != (-1) ** n_cycles(A): fails['b_cycle'] += 1
        total += s
    if total != n * hc_count(n, edges): fails['b_total'] += 1
# (c)
def otype(u, v, w):
    return tuple(sorted(range(3), key=lambda i: (u, v, w)[i]))
found = None
for perm in itertools.permutations(range(1, 6)):
    c = (0,) + perm; cnt = {}
    for t in range(6):
        ty = otype(c[t - 1], c[t], c[(t + 1) % 6]); cnt[ty] = cnt.get(ty, 0) ^ 1
    if not any(cnt.values()):
        found = c; break
if found is None: fails['c'] += 1
print('stats:', st, ' zero-type cycle on 6 ordered vertices:', found)
for k, v in fails.items():
    print(f'check {k:8s}: {"PASS" if v == 0 else "FAIL"} ({v} failures)')
print('ALL PASS' if not any(fails.values()) else 'SOME FAIL')
