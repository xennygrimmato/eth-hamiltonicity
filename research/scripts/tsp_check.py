"""Checks for Theorem TSP-1 of research/tsp-theorem.md (weighted #HC / TSP generating polynomial).

Run: python3 tsp_check.py [seed] [instances]

T1  weighted identity  n * sum_H z^{w(H)} = sum_{2-factors X} z^{w(X)} tau(V,X)  (as polynomials,
    tau by brute-force spanning-tree enumeration)
T2  weighted Berezin form  [Omega_V] prod_{e in X} z^{w_e}(1+q_e) = z^{w(X)} tau(V,X), z = Y = 2^b
T3  weighted pieces  alpha_N beta_N = 1,  sum_{l=0..3} alpha_l beta_l = Y^{w_e} (1+q_e), weight on alpha
T4  weighted blob factorisation  sum_l eps(l) prod_a I_a(l) = n sum_H Y^{w(H)}
T5  the weighted network (Definition 5.1 with weights): value by brute force = value via the
    K-grouping = n sum_H Y^{w(H)}; decoding gives the optimum, the number of optimal tours and the
    whole weight distribution
T6  Definition 2 parameters: P_a <= P, (i), U, and |W_a| < 2^B with B = 2 mu + 1 + b W mu
T7  the table bit-length grows linearly in W on a fixed instance (the Kronecker barrier, Section 5)
"""
import random
import sys

from tsp_lib import *
from proof_lib import planted_graph


def check(cond, msg):
    global FAILS
    if not cond:
        FAILS += 1
        print("  FAIL:", msg)


FAILS = 0


def inst_graphs(rng, count):
    """random sparse graphs with min degree >= 2, random partitions (empty blobs allowed),
    plus planted interleaving instances."""
    out = []
    for t in range(count):
        kind = t % 3
        if kind == 0:
            n = rng.randint(4, 8); m = rng.randint(n + 1, min(2 * n, n * (n - 1) // 2))
            E = random_graph(n, m, rng, min_deg2=True)
            g = rng.randint(2, 4)
            blob = [rng.randrange(g) for _ in range(n)]
        elif kind == 1:
            sizes = [rng.randint(1, 3) for _ in range(rng.randint(2, 4))]
            n, E, blob = planted_graph(sizes, 0.4, rng.randint(2, 4), rng, plant_hc=True)
            g = len(sizes)
        else:
            g = rng.choice([4, 5])
            sizes = [rng.randint(1, 2) for _ in range(g)]
            # interleaving visiting order 0,2,1,3,(4)
            order = [0, 2, 1, 3] + ([4] if g == 5 else [])
            n, E, blob = planted_graph(sizes, 0.3, rng.randint(1, 3), rng, plant_hc=True, border=order)
        deg = [0] * n
        for i, j in E:
            deg[i] += 1; deg[j] += 1
        if n < 3 or min(deg) < 2:
            continue
        out.append((n, E, blob, g))
    return out


def main(seed=1, count=24):
    global FAILS
    rng = random.Random(seed)
    graphs = inst_graphs(rng, count)
    print(f"seed {seed}: {len(graphs)} instances")
    for idx, (n, E, blob, g) in enumerate(graphs):
        m = len(E)
        Wmax = rng.choice([1, 2, 3, 4])
        w = [rng.randint(0, Wmax) for _ in E]
        wdict = {E[k]: w[k] for k in range(m)}
        b = m + (n - 1).bit_length() + 2          # coefficients are <= n * #HC <= n 2^m < 2^b
        Y = 1 << b
        r = rng.randrange(n)
        # ---- T1: polynomial identity
        TP = tour_poly(n, E, w)
        XP = twofactor_poly(n, E, w)
        check(XP == pscale(TP, n), f"T1 n={n} m={m}: {XP} vs n*{TP}")
        # ---- T2: Berezin form with weights, for every 2-factor and some random subsets
        Gn = Gens(n, r, rng)
        for X in two_factors(n, E) + [tuple(sorted(rng.sample(range(m), rng.randint(0, m)))) for _ in range(3)]:
            el = [E[k] for k in X]
            val = Gn.top(gprod([gscale(Gn.one_plus_q(i, j), Y ** wdict[(i, j)]) for (i, j) in el]), range(n))
            check(val == Y ** sum(w[k] for k in X) * tau_brute(n, el), f"T2 n={n} X={X}")
        # ---- T3: weighted pieces for both orientations and root ends
        for (i, j) in E:
            for (s, t) in ((i, j), (j, i)):
                Yw = Y ** wdict[(i, j)]
                tot = ZERO
                for l in (0, 1, 2, 3):
                    al, be = pieces(Gn, s, t, l)
                    al = gscale(al, Yw)
                    check(parity_of(al) in (pi_(l), 0) and parity_of(be) in (pi_(l), 0) and
                          (parity_of(al) == pi_(l) or not al) and (parity_of(be) == pi_(l) or not be),
                          f"T3 parity n={n} e={(s,t)} l={l}")
                    tot = gadd(tot, gmul(al, be))
                aN, bN = pieces(Gn, s, t, "N")
                check(gmul(aN, bN) == ONE, "T3 N")
                check(tot == gscale(Gn.one_plus_q(s, t), Yw), f"T3 sum n={n} e={(s,t)}")
        # ---- T4, T5: instance, blob factorisation, network
        inst = WInstance(n, E, blob, r, wdict, Y, g=g, rng=rng, gen_rng=rng)
        target = n * kron_eval(TP, Y)
        if 5 ** inst.m <= 20000:
            tot = 0
            for labs in itertools.product(("N", 0, 1, 2, 3), repeat=inst.m):
                lab = dict(enumerate(labs))
                prod = inst.eps(lab)
                for a in range(g):
                    prod *= inst.I(a, {k: lab[k] for k in inst.delta[a]})
                    if not prod:
                        break
                tot += prod
            check(tot == target, f"T4 n={n} g={g}: {tot} vs {target}")
        net = LabelNetwork(inst, ("N", 0, 1, 2, 3))
        # the literal evaluators enumerate every setting of every node: |S_a| = 5^{|delta(a)|} 2^{|Q_a|}
        small = max(5 ** len(inst.delta[a]) * 2 ** len(net.Q[a]) for a in range(g)) <= 40000
        if inst.m <= 7 and small:
            Z = eval_network_brute(net)
            check(Z == target, f"T5 brute n={n} g={g} m_x={inst.m}: {Z} vs {target}")
            for K in (2, 3):
                if K <= g:
                    Zg = eval_network_grouped(net, random_groups(g, K, rng))
                    check(Zg == target, f"T5 grouped K={K} n={n}: {Zg} vs {target}")
            # decode: optimum, number of optimal tours, distribution
            dist = kron_decode_nonneg(Z, b, n * Wmax + 2)
            opt = plowest(dist)
            true_opt = plowest(TP)
            check(opt == true_opt, f"T5 opt {opt} vs {true_opt}")
            check(all(c % n == 0 for c in dist.values()) and {e: c // n for e, c in dist.items()} == TP,
                  f"T5 distribution {dist} vs {TP}")
        # ---- T6: Definition 2 parameters
        mu = inst.mu()
        P = width_base(5, mu) + g + g * g
        check(all(net.Plen[a] <= P for a in range(g)), "T6 P_a <= P")
        check(all(sum(net.c[(a, bb)] for bb in range(g) if bb != a) <= P for a in range(g)), "T6 (i)")
        U = net.U()
        from math import comb
        check(U == 2 * sum(net.w[(a, bb)] for a in range(g) for bb in range(a + 1, g)) + 2 * comb(g, 3), "T6 U")
        B = 2 * mu + 1 + b * Wmax * mu
        if inst.m <= 7 and small:
            mb = net.max_table_bits()
            check(mb <= B, f"T6 |W_a| bits {mb} > B={B}")
        print(f"  [{idx}] n={n} m={m} g={g} crossing={inst.m} W={Wmax} opt={plowest(TP)} "
              f"#HC={sum(TP.values())} U={U} P={P} B={B}")
    # ---- T7: bit growth in W on one fixed small instance
    n, E = 6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5), (0, 3), (1, 4), (2, 5)]
    blob = [0, 0, 1, 1, 2, 2]
    rows = []
    for Wmax in (1, 2, 4, 8, 16):
        w = {e: Wmax for e in E}        # all weights = W: exponents w(X) = n W
        b = len(E) + 5
        inst = WInstance(n, E, blob, 0, w, 1 << b, rng=random.Random(7), gen_rng=random.Random(7))
        net = LabelNetwork(inst, ("N", 0, 1, 2, 3))
        rows.append((Wmax, net.max_table_bits(), b))
    print("  T7 table bits vs W (b = %d):" % rows[0][2], [(W_, bits) for W_, bits, _ in rows])
    incs = [rows[t + 1][1] - rows[t][1] for t in range(len(rows) - 1)]
    check(all(incs[t + 1] >= 1.8 * incs[t] for t in range(len(incs) - 1)),
          f"T7 increments not doubling: {incs}")
    print("ALL CHECKS PASSED" if FAILS == 0 else f"{FAILS} FAILURES")
    return FAILS == 0


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    ok = main(seed, count)
    sys.exit(0 if ok else 1)
