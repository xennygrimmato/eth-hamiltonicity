"""Checks for Theorem TSP-2 of research/tsp-theorem.md (ATSP on sparse digraphs).

Run: python3 tsp_atsp.py [seed] [instances]

A1  directed matrix-tree theorem: det L_out^{(r)}(F) = #spanning in-arborescences towards r,
    on random arc sets (brute-force arborescence count)
A2  two-matrix Berezin form: [Omega_V] prod_k thetabar(b_k) theta(c_k) = det(B) det(C)
A3  Berezin form of det L_out^{(r)}: [Omega_V] prod_{a in F} (1 + psibar_i(psi_i - psi_j)) = det L_out(F)^{(r)}
A4  identity  sum_{H directed HC} z^{w(H)} = sum_{cycle covers X} z^{w(X)} det L_out(X)^{(r)}
    (as polynomials, no factor n; the arborescence count is 1 on a Hamiltonian cycle, 0 otherwise)
A5  directed pieces: 3 labels per arc, both blob orientations, root ends; sum = Y^w(1 + psibar_i(psi_i-psi_j))
A6  blob factorisation and the base-3 network: brute force = grouping = sum_H Y^{w(H)}; decoding
A7  parameters: U = 2 sum ceil(e log 3) + 2 C(g,3), |W_a| < 2^B
"""
import random
import sys
from math import comb

from tsp_lib import *


FAILS = 0


def check(cond, msg):
    global FAILS
    if not cond:
        FAILS += 1
        print("  FAIL:", msg)


def main(seed=1, count=20):
    rng = random.Random(seed)
    done = 0
    # ---- A2 on random integer matrices
    for _ in range(40):
        N = rng.randint(1, 4)
        Gn = Gens(N + 1, N, rng)        # root N, generators for 0..N-1
        B = [[rng.randint(-2, 2) for _ in range(N)] for _ in range(N)]   # columns b_k = B[.][k]
        C = [[rng.randint(-2, 2) for _ in range(N)] for _ in range(N)]
        prod = ONE
        for k in range(N):
            tb = ZERO; tc = ZERO
            for u in range(N):
                tb = gadd(tb, gscale(Gn.pb(u), B[u][k]))
                tc = gadd(tc, gscale(Gn.ps(u), C[u][k]))
            prod = gmul(prod, gmul(tb, tc))
        check(Gn.top(prod, range(N)) == det_bareiss(B) * det_bareiss(C), "A2")
    print("  A2 done (40 random matrix pairs)")
    while done < count:
        n = rng.randint(3, 6)
        m = rng.randint(n + 2, min(3 * n, n * (n - 1)))
        arcs = random_digraph(n, m, rng)
        r = rng.randrange(n)
        Gn = Gens(n, r, rng)
        # ---- A1, A3 on random arc subsets of size n-1 and on random subsets
        for _ in range(6):
            F = sorted(rng.sample(range(m), rng.randint(0, m)))
            al = [arcs[k] for k in F]
            d = det_bareiss(reduced_Lout(n, al, r))
            arb = in_arborescences_brute(n, al, r)
            check(d == arb, f"A1 n={n} F={F}: det {d} arb {arb}")
            val = Gn.top(gprod([gadd(ONE, gmul(Gn.pb(i), gadd(Gn.ps(i), Gn.ps(j), -1))) for (i, j) in al]),
                         range(n))
            check(val == d, f"A3 n={n} F={F}: {val} vs {d}")
        # ---- A4
        Wmax = rng.choice([1, 2, 3])
        w = [rng.randint(0, Wmax) for _ in arcs]
        TP = dtour_poly(n, arcs, w)
        CP = cyclecover_poly(n, arcs, w, r)
        check(TP == CP, f"A4 n={n}: tours {TP} covers {CP}")
        # each cycle cover: arborescence count is 1 iff Hamiltonian
        for X in cycle_covers(n, arcs):
            d = det_bareiss(reduced_Lout(n, [arcs[k] for k in X], r))
            check(d == int(frozenset(X) in set(dham_cycles(n, arcs))), f"A4b n={n} X={X} d={d}")
        # ---- A5 pieces
        b = m + (n - 1).bit_length() + 2
        Y = 1 << b
        for k, (i, j) in enumerate(arcs):
            for (s, t) in ((i, j), (j, i)):
                Yw = Y ** w[k]
                tot = ZERO
                for l in DLABELS:
                    al, be = dpieces(Gn, i, j, s, t, l, Yw)
                    for pc in (al, be):
                        check(not pc or parity_of(pc) == pi_(l), f"A5 parity l={l}")
                    if l == "N":
                        check(gmul(al, be) == ONE, "A5 N")
                    else:
                        tot = gadd(tot, gmul(al, be))
                check(tot == gscale(gadd(ONE, gmul(Gn.pb(i), gadd(Gn.ps(i), Gn.ps(j), -1))), Yw),
                      f"A5 sum arc {(i,j)} low {s}")
        # ---- A6: partition and network
        g = rng.randint(2, 4)
        blob = [rng.randrange(g) for _ in range(n)]
        inst = DInstance(n, arcs, blob, r, w, Y, g=g, rng=rng, gen_rng=rng)
        if inst.m > 7:
            continue
        done += 1
        target = kron_eval(TP, Y)
        if 3 ** inst.m <= 20000:
            tot = 0
            for labs in itertools.product(DLABELS, repeat=inst.m):
                lab = dict(enumerate(labs))
                prod = inst.eps(lab)
                for a in range(g):
                    prod *= inst.I(a, {k: lab[k] for k in inst.delta[a]})
                    if not prod:
                        break
                tot += prod
            check(tot == target, f"A6 blob factorisation n={n} g={g}: {tot} vs {target}")
        net = LabelNetwork(inst, DLABELS)
        Z = eval_network_brute(net)
        check(Z == target, f"A6 brute n={n} g={g}: {Z} vs {target}")
        for K in (2, 3):
            if K <= g:
                Zg = eval_network_grouped(net, random_groups(g, K, rng))
                check(Zg == target, f"A6 grouped K={K}: {Zg} vs {target}")
        dist = kron_decode_nonneg(Z, b, n * Wmax + 2)
        check(dist == TP, f"A6 decode {dist} vs {TP}")
        # ---- A7
        U = net.U()
        check(U == 2 * sum(net.w[(a, bb)] for a in range(g) for bb in range(a + 1, g)) + 2 * comb(g, 3), "A7 U")
        check(all(net.w[(a, bb)] == width_base(3, net.e[(a, bb)]) for (a, bb) in net.w), "A7 w_ab = ceil(e log 3)")
        mu = inst.mu()
        B = 2 * mu + 1 + b * Wmax * mu
        check(net.max_table_bits() <= B, "A7 B")
        print(f"  n={n} m={m} g={g} crossing={inst.m} W={Wmax} opt={plowest(TP)} #DHC={sum(TP.values())} U={U}")
    print("ALL CHECKS PASSED" if FAILS == 0 else f"{FAILS} FAILURES")
    return FAILS == 0


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    sys.exit(0 if main(seed, count) else 1)
