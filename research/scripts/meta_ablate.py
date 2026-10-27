"""Ablations for the meta-theorem constructions (research/meta-theorem.md).

A. Drop the fermionic reordering sign in the multi-field network: values become wrong.
B. Merge the two independent Grassmann fields into one (both predicates read the same
   generators): the integrand then computes det of the *combined* Laplacian, not the product,
   and the identity fails (two edge-disjoint spanning trees; strong connectivity).

Run: python3 meta_ablate.py
"""
import itertools, random
from ext_engine import ONE, gadd, gmul, gscale, random_blobs, crossing_ok
from ext_problems import rand_graph, rand_digraph
from meta_engine import build_network, network_value
import meta_problems as MP


def contract_nosign(net):
    K, cross, lab, tables = net["K"], net["cross"], net["lab"], net["tables"]
    partial = {(): 1}
    for a in range(K):
        inc, tab = tables[a]
        new = {}
        for key, val in partial.items():
            kd = dict(key)
            for labs, w in tab.items():
                if any(k in kd and kd[k] != l for k, l in zip(inc, labs)):
                    continue
                nd = dict(kd); nd.update(zip(inc, labs))
                nk = tuple(sorted(nd.items()))
                new[nk] = new.get(nk, 0) + val * w
        partial = {k: v for k, v in new.items() if v}
    return sum(v for k, v in partial.items() if len(k) == len(cross))


class TwoTreeOneField(MP.TwoTreeSpec):
    nf = 1
    def F(s, k, a, c, x):
        u, v = s.edges[k]
        if x == 1:
            return gscale(gadd(ONE, s.q_und(u, v, 0)), s.Z1)
        if x == 2:
            return gscale(gadd(ONE, s.q_und(u, v, 0)), s.Z2)
        return ONE


def pick(n, E, K, rng, mc=6, mi=5):
    for _ in range(500):
        bl = random_blobs(n, K, rng)
        if crossing_ok(E, bl, mc, mi):
            return bl
    return None


rng = random.Random(11)
bad_sign = tot_sign = 0
bad_merge = tot_merge = 0
# ---------------- A: sign ablation on P1 (CFVS) and P9 (strong connectivity) instances
for trial in range(6):
    if trial % 2 == 0:
        n = 5; E = rand_graph(n, 7, rng)
        Y = 1 << 64
        sp = MP.CFVSSpec(n, E, Y, Y ** ((n + 1) ** 2), Y ** (n + 1)); nm = "CFVS"
    else:
        n = 5
        while True:
            A = rand_digraph(n, 9, rng)
            if len(MP.reach(n, A, 0)) == n and len(MP.reach(n, A, 0, rev=True)) == n:
                break
        E = A; sp = MP.StrongSpec(n, A, 1 << 40); nm = "MSCS"
    for K in (2, 3):
        bl = pick(n, E, K, rng)
        if bl is None:
            continue
        Z, bits, net = network_value(sp, bl)
        Zn = contract_nosign(net)
        tot_sign += 1; bad_sign += (Zn != Z)
        print(f"A {nm} K={K}: with sign {'=' if Zn == Z else '!='} without sign")
# ---------------- B: merged field
for trial in range(2):
    n = 5; m = 8; E = rand_graph(n, m, rng)
    Y = 1 << 32
    good = MP.TwoTreeSpec(n, E, Y, Y ** (m + 1))
    merged = TwoTreeOneField(n, E, Y, Y ** (m + 1))
    bl = pick(n, E, 2, rng, 5, 4)
    Zg, _, _ = network_value(good, bl)
    Zm, _, _ = network_value(merged, bl)
    tot_merge += 1; bad_merge += (Zg != Zm)
    print(f"B two-trees m={m}: independent fields {'=' if Zg == Zm else '!='} one shared field")
print(f"sign ablation changed the value in {bad_sign}/{tot_sign} cases; "
      f"field merging changed it in {bad_merge}/{tot_merge}")
