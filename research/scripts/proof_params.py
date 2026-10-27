"""Checks of the combinatorial preprocessing and bookkeeping facts of research/exact-hc-theorem.md
(Section 6).  Exact integer arithmetic.  Run: python3 proof_params.py [seed]

  P1 Lemma 6.1  branching on high-degree vertices: #HC(G) = sum_pi #HC(G_pi)
  P2 Lemma 6.2  the prefix-sum partition has every blob degree sum <= 2m/g + Delta
  P3 (5.x)      sum_{b=1}^{g} (b-1)(g-b) = C(g,3); copy-bit counts; P_a, sum_b c_ab <= P
  P4 Cor. 7.2   search by self-reduction returns a Hamiltonian cycle (counting oracle = brute force)
  P5 (6.x)      #high vertices < 2 m h / n
"""
import itertools
import random
import sys
from math import comb

from proof_lib import hc_count, random_graph, width5

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 7
rng = random.Random(seed)
FAIL = []
COUNT = {}


def check(name, cond, info=""):
    COUNT[name] = COUNT.get(name, 0) + 1
    if not cond:
        FAIL.append((name, info)); print("FAIL", name, info)


def degrees(n, E):
    d = [0] * n
    for i, j in E:
        d[i] += 1; d[j] += 1
    return d


def branch_graphs(n, E, thr):
    """Lemma 6.1: high = {v : deg v > thr}; for each choice pi of a 2-set of edges at every high
    vertex, G_pi = G minus the edges at a high vertex v that are not in pi_v."""
    d = degrees(n, E)
    high = [v for v in range(n) if d[v] > thr]
    inc = {v: [e for e in E if v in e] for v in high}
    for choice in itertools.product(*[list(itertools.combinations(inc[v], 2)) for v in high]):
        pi = dict(zip(high, choice))
        keep = [e for e in E if all((v not in e) or (e in pi[v]) for v in high)]
        yield keep


def p1():
    for _ in range(150):
        n = rng.randint(4, 9)
        m = rng.randint(n, min(comb(n, 2), 3 * n))
        E = random_graph(n, m, rng)
        thr = rng.randint(2, 5)
        d0 = degrees(n, E)
        nbr = 1
        for v in range(n):
            if d0[v] > thr:
                nbr *= comb(d0[v], 2)
        if nbr > 3000:
            continue
        tot = 0
        nb = 0
        for Ek in branch_graphs(n, E, thr):
            nb += 1
            tot += hc_count(n, Ek)
            dk = degrees(n, Ek)
            check("P1 branch graph has max degree <= max(thr, 2)", max(dk) <= max(thr, 2))
            check("P1 branch graph has at most |E| edges", len(Ek) <= len(E))
        check("P1 #HC(G) = sum_pi #HC(G_pi)", tot == hc_count(n, E), (n, E, thr))
        d = degrees(n, E)
        nh = sum(1 for v in range(n) if d[v] > thr)
        check("P5 #high * thr < 2m", nh * thr < 2 * len(E) or nh == 0)
        check("P1 #branches <= n^(2 #high)", nb <= n ** (2 * nh))


def prefix_partition(n, E, g, order):
    d = degrees(n, E)
    m = len(E)
    blob = [0] * n
    S = 0
    for v in order:
        # blob of v: min(g, floor(S * g / (2m)) + 1), 1-based; here 0-based
        blob[v] = min(g - 1, (S * g) // (2 * m))
        S += d[v]
    return blob


def p2():
    for _ in range(400):
        n = rng.randint(3, 40)
        m = rng.randint(1, min(comb(n, 2), 4 * n))
        E = random_graph(n, m, rng)
        g = rng.randint(1, 12)
        order = list(range(n)); rng.shuffle(order)
        blob = prefix_partition(n, E, g, order)
        d = degrees(n, E)
        Delta = max(d)
        for a in range(g):
            mu_a = sum(d[v] for v in range(n) if blob[v] == a)
            # exact form of mu_a <= 2m/g + Delta
            check("P2 g * mu_a <= 2m + g * Delta", g * mu_a <= 2 * len(E) + g * Delta, (n, m, g, a))


def p3():
    for g in range(1, 60):
        check("P3 sum (b-1)(g-b) = C(g,3)", sum((b - 1) * (g - b) for b in range(1, g + 1)) == comb(g, 3))
        for a in range(1, g + 1):
            Qa = sum(1 for c in range(a + 1, g + 1) for d in range(c + 1, g + 1))
            check("P3 |Q_a| = C(g-a,2) <= g^2/2", Qa == comb(g - a, 2) and 2 * Qa <= g * g)
            copies_at_a = sum(g - b for b in range(a + 1, g + 1)) + sum(g - a for b in range(1, a))
            check("P3 copy bits on pairs at a <= 3g^2/4", 4 * copies_at_a <= 3 * g * g)
        check("P3 g^2 + 2C(g,3) <= g^3 (g>=2)", g < 2 or g * g + 2 * comb(g, 3) <= g ** 3)
    # w(e) = ceil(e log2 5) and subadditivity-type bound sum_b w_ab <= ceil(log2 5 * sum e) + #b
    for _ in range(500):
        es = [rng.randint(0, 9) for _ in range(rng.randint(1, 8))]
        check("P3 sum_b w(e_b) <= w(sum e_b) + #b", sum(width5(e) for e in es) <= width5(sum(es)) + len(es))


def p4():
    for _ in range(60):
        n = rng.randint(4, 8)
        m = rng.randint(n, min(comb(n, 2), 2 * n + 2))
        E = random_graph(n, m, rng)
        if hc_count(n, E) == 0:
            continue
        H = list(E)
        for e in list(E):
            Hm = [f for f in H if f != e]
            if hc_count(n, Hm) > 0:
                H = Hm
        d = degrees(n, H)
        check("P4 self-reduction leaves exactly a Hamiltonian cycle",
              len(H) == n and all(x == 2 for x in d) and hc_count(n, H) == 1)


if __name__ == "__main__":
    p1(); p2(); p3(); p4()
    for k in sorted(COUNT):
        print(f"  {COUNT[k]:8d}  {k}")
    print("ALL CHECKS PASSED" if not FAIL else f"{len(FAIL)} FAILURES")
