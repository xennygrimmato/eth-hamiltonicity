#!/usr/bin/env python3
"""Exact check of a Ryser-type *local product* formula for #PM of a general graph, i.e. a sum over
x in {0,1}^n of a product of factors with small scope and total X-degree O(n) -- the input shape that
OpenAI's replacement-form engine (ETH paper Sec. 2-4) needs:

  #PM(G) = [y^{n/2}]  sum_{x in {0,1}^n}  prod_v (2x_v - 1)  *  prod_u ( 1 + y * x_u * sum_{w>u, w~u} x_w )

Factor of u has scope {u} u N^+(u) (size deg+1) and X-degree 2, so total degree 3n and incidences
m + 2n. (Expanding, each u in a set L picks a higher neighbour; inclusion-exclusion keeps the
multisets covering every vertex; with |L| = n/2 the 2|L| = n endpoints are distinct: a perfect
matching, each counted once via its lower endpoints.)  Bipartite Ryser is the special case of
rows picking columns.  Checks random graphs n <= 10 against brute force; prints PASS/FAIL.
"""
import itertools, random

def pm_brute(n, E):
    adj = {frozenset(e) for e in E}
    def rec(rem):
        if not rem: return 1
        u = min(rem); tot = 0
        for w in rem:
            if w != u and frozenset((u, w)) in adj: tot += rec(rem - {u, w})
        return tot
    return rec(frozenset(range(n)))

def pm_product(n, E):
    up = {u: [w for (a, w) in [tuple(sorted(e)) for e in E] if a == u] for u in range(n)}
    # coefficient list in y
    tot = [0] * (n + 1)
    for x in itertools.product((0, 1), repeat=n):
        sign = 1
        for v in range(n): sign *= (2 * x[v] - 1)
        poly = [1]
        for u in range(n):
            c = x[u] * sum(x[w] for w in up[u])
            if c:
                poly = [a + (c * poly[i - 1] if i >= 1 else 0) for i, a in enumerate(poly + [0])]
        for i, a in enumerate(poly): tot[i] += sign * a
    return tot[n // 2] if n % 2 == 0 else 0

if __name__ == '__main__':
    rng = random.Random(7); ok = True
    for trial in range(40):
        n = rng.choice([2, 4, 6, 8, 10]); p = rng.choice([0.3, 0.5, 0.8, 1.0])
        E = [(u, w) for u in range(n) for w in range(u + 1, n) if rng.random() < p]
        a, b = pm_brute(n, E), pm_product(n, E)
        ok &= (a == b)
        if trial < 6 or a != b: print('n=%2d m=%2d  #PM brute=%5d  product formula=%5d  %s' % (n, len(E), a, b, 'PASS' if a == b else 'FAIL'))
    print('ALL PASS' if ok else 'SOME FAIL')
