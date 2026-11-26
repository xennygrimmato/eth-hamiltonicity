"""Checks for q1-notes section 4.2: partition of the generic edges of the F_2^m 3-net into copies of X_4,
balance (Def. 2.1 of notes.md) of X_4 and of the matchings E_D."""
import itertools
def rank2(d1, d2):            # columns d1, d2 in F_2^m (ints): rank of the m x 2 matrix
    return (d1 != 0) + (d2 != 0) - (d1 == d2 != 0) if (d1 == 0 or d2 == 0 or d1 == d2) else 2
def check_partition(m):
    g = 1 << m
    nodes = [(r, c) for r in range(g) for c in range(g)]
    copies = {}
    for n, n2 in itertools.combinations(nodes, 2):
        d1, d2 = n[0] ^ n2[0], n[1] ^ n2[1]
        if rank2(d1, d2) == 2:
            S = frozenset({0, d1, d2, d1 ^ d2})
            # coset of Hom(F_2^2,S): canonical representative = lexicographically smallest node
            rep = min((n[0] ^ a, n[1] ^ b) for a in S for b in S)
            copies.setdefault((S, rep), []).append((n, n2))
    sizes = sorted(set(len(v) for v in copies.values()))
    print(f"m={m}: generic edges {sum(len(v) for v in copies.values())}, copies {len(copies)}, edges per copy {sizes}")
def balance(edges, classes):
    lines = {}
    deg = {}
    for (n, n2) in edges:
        deg[n] = deg.get(n, 0) + 1; deg[n2] = deg.get(n2, 0) + 1
    ok = True
    nodes = list(deg)
    for k, l in itertools.permutations(range(3), 2):
        cnt = {}
        for (n, n2) in edges:
            for (y, z) in ((n, n2), (n2, n)):
                key = (classes(y)[k], classes(z)[l]); cnt[key] = cnt.get(key, 0) + 1
        rhs = {}
        for n in nodes:
            key = (classes(n)[k], classes(n)[l]); rhs[key] = rhs.get(key, 0) + deg[n]
        keys = set(cnt) | set(rhs)
        ok &= all(cnt.get(x, 0) == rhs.get(x, 0) for x in keys)
    return ok
cl = lambda n: (n[0], n[1], n[0] ^ n[1])
nodes4 = [(r, c) for r in range(4) for c in range(4)]
X4 = [(n, n2) for n, n2 in itertools.combinations(nodes4, 2) if rank2(n[0] ^ n2[0], n[1] ^ n2[1]) == 2]
print("X4: edges", len(X4), "balanced:", balance(X4, cl))
for D in [(d1, d2) for d1 in range(1, 4) for d2 in range(1, 4) if d1 != d2]:
    ED = [(n, (n[0] ^ D[0], n[1] ^ D[1])) for n in nodes4 if n < (n[0] ^ D[0], n[1] ^ D[1])]
    print("E_D", D, "edges", len(ED), "balanced:", balance(ED, cl))
for m in (2, 3, 4):
    check_partition(m)
