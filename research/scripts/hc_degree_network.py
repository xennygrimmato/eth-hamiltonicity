#!/usr/bin/env python3
"""Degree-based (rank-encoded) Hamiltonian-cycle network: exact verification.

Write-up: research/hc-degree-theorem.md.  Run:  python3 hc_degree_network.py [seed] [instances]

The network of exact-hc-theorem.md §5 shares, on the pair {a,b}, the base-5 code of the labels of
ALL crossing edges between the blobs V_a and V_b (w_ab = ceil(e_ab log 5) bits), so U ~ 2 log5 |E|.
Here a *profile* mu = (mu_ab)_{a<b} is fixed, and the pair {a,b} shares only

    (S_ab, lambda_ab):  S_ab = the set of crossing edges between a and b that carry a label != N
                        (|S_ab| = mu_ab), encoded as the colex rank of S_ab among the mu_ab-subsets
                        of E(a,b) in ceil(log2 C(e_ab, mu_ab)) bits, followed by the 2-bit labels
                        lambda_ab(k) in {0,1,2,3} of the k in S_ab, in crossing order.

Node a's setting is this block for every b != a, then the copy bits y^(a) on Q_a (unchanged).
Everything else (W_a = sigma_a chi_a I_a, Psi, the copy bits, f = [proj = theta]) is the §5
network, since (S_ab, lambda_ab) is just a re-encoding of the labels on E(a,b).  A profile is
*admissible* if sum_b mu_ab <= 2|V_a| for every a (otherwise some vertex of V_a would have three
crossing edges in X, and every W_a vanishes).

Checks (exact integers; PASS/FAIL):
  D1  rank/unrank of k-subsets is a bijection onto [0, C(e,k))
  D2  settings: fixed length P_a, decode(encode) = id, invalid ranks rejected, P_a <= P, (i) sum_b c_ab <= P
  D3  Psi_ab = sum_theta f_ab f_ba (exhaustive over theta when c_ab <= 10), c symmetric, |W_a| < 2^B,
      |I_a| <= Delta^{2 nu_a} 20^{nu_a} and <= 2^{|E_int(a)|} 20^{nu_a}
  D4  per node: sum_b ceil(log C(e_ab,mu_ab)) <= ceil(log C(|delta(a)|, M_a)) + #{b: C >= 2};
      sum_b c'_ab <= 2 nu_a log2(2e Delta) + g - 1 and <= 3.45 mu_a + g - 1
  D5  U(mu) = sum_{a != b} c_ab <= 2 ceil(log C(m_x, M)) + 2 C(g,2) + 4M + 2 C(g,3)
             <= 2 n log2(2e dbar) + g^3 <= 2 n log2(2e Delta) + g^3     (dbar = 2m/n)
  D6  #admissible profiles <= (2 nu + 1)^{C(g,2)}
  D7  sum over admissible profiles of the network value (brute force over prod_a S_a, W/Psi as black
      boxes) = n #HC(G); every inadmissible profile has value 0
The U table compares max_mu U(mu) with the old U = 2 sum w_ab + 2 C(g,3).
"""
import itertools
import math
import os
import random
import sys
from math import comb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from proof_lib import (Instance, HCNetwork, LABELS, hc_count, random_graph, planted_graph,
                       to_bits, from_bits)

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
NINST = int(sys.argv[2]) if len(sys.argv) > 2 else 24
rng = random.Random(seed)
FAIL = []
COUNT = {}
LOG2E = math.log2(math.e)


def check(name, cond, info=""):
    COUNT[name] = COUNT.get(name, 0) + 1
    if not cond:
        FAIL.append((name, info))
        print("FAIL", name, info)


def clog2(c):
    """ceil(log2 c) for an integer c >= 1."""
    return (c - 1).bit_length()


# ------------------------------------------------------------------ combinatorial number system
def rank_subset(S, e):
    """colex rank of the sorted k-subset S of range(e): sum_i C(S[i], i+1), in [0, C(e,k))."""
    return sum(comb(s, i + 1) for i, s in enumerate(S))


def unrank_subset(r, e, k):
    """inverse of rank_subset; None if r >= C(e,k)."""
    if r >= comb(e, k):
        return None
    S = []
    for i in range(k, 0, -1):
        s = i - 1
        while comb(s + 1, i) <= r:
            s += 1
        S.append(s)
        r -= comb(s, i)
    return sorted(S)


def d1():
    for e in range(0, 9):
        for k in range(0, e + 1):
            subs = list(itertools.combinations(range(e), k))
            ranks = [rank_subset(list(S), e) for S in subs]
            check("D1", sorted(ranks) == list(range(comb(e, k))), (e, k))
            check("D1", all(unrank_subset(r, e, k) == list(S) for r, S in zip(ranks, subs)), (e, k))
            check("D1", unrank_subset(comb(e, k), e, k) is None, (e, k))


# ------------------------------------------------------------------ the profile network
class DegNetwork(HCNetwork):
    """The network N_mu of hc-degree-theorem.md Definition 2.1 (settings as fixed-length bit tuples)."""

    def __init__(self, inst, mu):
        self.inst = inst
        self.g = g = inst.g
        self.sign_mode = "full"
        self.e, self.mu, self.cp, self.w1 = {}, {}, {}, {}
        for a in range(g):
            for b in range(g):
                if a != b:
                    key = (min(a, b), max(a, b))
                    self.e[(a, b)] = len(inst.Eab[key])
                    self.mu[(a, b)] = mu[key]
                    self.w1[(a, b)] = clog2(comb(self.e[(a, b)], self.mu[(a, b)]))
                    self.cp[(a, b)] = self.w1[(a, b)] + 2 * self.mu[(a, b)]
        self.Q = {a: [(c, d) for c in range(a + 1, g) for d in range(c + 1, g)] for a in range(g)}
        self.layout = {}
        for a in range(g):
            pos, lay = 0, {}
            for b in range(g):
                if b != a:
                    lay[b] = (pos, self.cp[(a, b)])
                    pos += self.cp[(a, b)]
            lay["Q"] = (pos, len(self.Q[a]))
            self.layout[a] = lay
        self.Plen = {a: sum(w for (p, w) in self.layout[a].values()) for a in range(g)}
        self.c = {(a, b): self.cp[(a, b)] + (g - 1 - max(a, b)) for (a, b) in self.cp}
        self._Wcache = {}

    def row(self, a):
        return tuple(self.mu[(a, b)] for b in range(self.g) if b != a)

    def admissible(self):
        return all(sum(self.row(a)) <= 2 * len(self.inst.V[a]) for a in range(self.g))

    # ---- encoding: block_b(z_a) = (rank of S_ab in w1 bits, 2 bits per label of S_ab), then y
    def block(self, a, b, lab_at):
        ks = self.inst.Eab[(min(a, b), max(a, b))]           # crossing order
        S = [t for t, k in enumerate(ks) if lab_at[k] != "N"]
        if len(S) != self.mu[(a, b)]:
            return None
        bits = list(to_bits(rank_subset(S, len(ks)), self.w1[(a, b)]))
        for t in S:
            bits += list(to_bits(lab_at[ks[t]], 2))
        return bits

    def encode(self, a, lab_at, y):
        bits = [0] * self.Plen[a]
        for b in range(self.g):
            if b == a:
                continue
            blk = self.block(a, b, lab_at)
            if blk is None:
                return None
            p, w = self.layout[a][b]
            bits[p:p + w] = blk
        p, w = self.layout[a]["Q"]
        bits[p:p + w] = [y[cd] for cd in self.Q[a]]
        return tuple(bits)

    def decode(self, a, z):
        if len(z) != self.Plen[a]:
            return None
        lab_at = {}
        for b in range(self.g):
            if b == a:
                continue
            p, w = self.layout[a][b]
            ks = self.inst.Eab[(min(a, b), max(a, b))]
            w1 = self.w1[(a, b)]
            S = unrank_subset(from_bits(z[p:p + w1]), len(ks), self.mu[(a, b)])
            if S is None:
                return None
            for k in ks:
                lab_at[k] = "N"
            for i, t in enumerate(S):
                q = p + w1 + 2 * i
                lab_at[ks[t]] = from_bits(z[q:q + 2])
        p, w = self.layout[a]["Q"]
        y = {cd: z[p + i] for i, cd in enumerate(self.Q[a])}
        return lab_at, y

    def pair_choices(self, a, b):
        ks = self.inst.Eab[(min(a, b), max(a, b))]
        for S in itertools.combinations(range(len(ks)), self.mu[(a, b)]):
            for labs in itertools.product((0, 1, 2, 3), repeat=len(S)):
                d = {k: "N" for k in ks}
                for t, l in zip(S, labs):
                    d[ks[t]] = l
                yield d

    def settings(self, a):
        others = [b for b in range(self.g) if b != a]
        for parts in itertools.product(*[list(self.pair_choices(a, b)) for b in others]):
            lab_at = {}
            for d in parts:
                lab_at.update(d)
            for ys in itertools.product((0, 1), repeat=len(self.Q[a])):
                yield self.encode(a, lab_at, dict(zip(self.Q[a], ys)))

    def U(self):
        return sum(self.c.values())


def profiles(inst):
    """all profiles 0 <= mu_ab <= e_ab, as dicts on the pairs a < b."""
    keys = sorted(inst.Eab)
    for vals in itertools.product(*[range(len(inst.Eab[k]) + 1) for k in keys]):
        yield dict(zip(keys, vals))


def eval_brute(net, tables):
    """Z = sum_{z in prod S_a} prod_a W_a(z_a) prod_{a<b} Psi_ab, node by node, W and Psi as black
    boxes; settings with W_a = 0 contribute nothing and are dropped first."""
    g = net.g
    S = [[(z, w) for z, w in tables[a].items() if w != 0] for a in range(g)]
    total = 0

    def rec(a, chosen, prod):
        nonlocal total
        if a == g:
            total += prod
            return
        for z, w in S[a]:
            p = prod * w
            for b in range(a):
                if not p:
                    break
                p *= net.Psi(b, a, chosen[b], z)
            if p:
                chosen.append(z)
                rec(a + 1, chosen, p)
                chosen.pop()
    rec(0, [], 1)
    return total


# ------------------------------------------------------------------ one instance
def degrees(n, E):
    deg = [0] * n
    for i, j in E:
        deg[i] += 1; deg[j] += 1
    return deg


def run_instance(name, n, E, blob, r, g):
    inst = Instance(n, E, blob, r, g=g, rng=rng, gen_rng=rng)
    deg = degrees(n, E)
    m = len(E)
    Delta = max(deg)
    dbar = 2 * m / n
    nu = max(len(inst.V[a]) for a in range(g))
    mu_a = {a: sum(deg[v] for v in inst.V[a]) for a in range(g)}
    mu_max = max(mu_a.values())
    hc = hc_count(n, E)
    lam = math.log2(2 * math.e * Delta)
    Pparam = math.ceil(min(2 * nu * lam, 3.45 * mu_max)) + g + g * g
    Bparam = math.ceil(min(2 * nu * lam, 2.7 * mu_max)) + 1
    mx = inst.m
    old = HCNetwork(inst)
    U_old = old.U()
    tables = {}                       # (a, row) -> {z: W}
    total_adm = total_all = 0
    n_adm = n_all = 0
    U_max = 0
    for mu in profiles(inst):
        net = DegNetwork(inst, mu)
        n_all += 1
        adm = net.admissible()
        # tables, cached by (node, profile row)
        tabs = []
        for a in range(g):
            key = (a, net.row(a))
            if key not in tables:
                tab = {}
                for z in net.settings(a):
                    check("D2", z is not None and len(z) == net.Plen[a], (name, a))
                    w = net.W(a, z)
                    if w:
                        tab[z] = w
                tables[key] = tab
            tabs.append(tables[key])
        Z = eval_brute(net, tabs)
        total_all += Z
        if adm:
            n_adm += 1
            total_adm += Z
            U_max = max(U_max, net.U())
        else:
            check("D7", Z == 0, (name, "inadmissible profile with nonzero value", mu))
            continue
        # ---- Definition 2 checks on admissible profiles
        M = sum(mu.values())
        for a in range(g):
            Pa = net.Plen[a]
            check("D2", Pa <= Pparam, (name, a, Pa, Pparam))
            check("D2", sum(net.c[(a, b)] for b in range(g) if b != a) <= Pparam, (name, a))
            Ma = sum(net.row(a))
            Na = len(inst.delta[a])
            # D4 exact: sum_b ceil(log C) <= ceil(log C(|delta(a)|, M_a)) + #{b: C >= 2}
            lhs = sum(net.w1[(a, b)] for b in range(g) if b != a)
            nb = sum(1 for b in range(g) if b != a and comb(net.e[(a, b)], net.mu[(a, b)]) >= 2)
            check("D4", lhs <= clog2(comb(Na, Ma)) + nb, (name, a))
            cpa = sum(net.cp[(a, b)] for b in range(g) if b != a)
            check("D4", cpa <= 2 * len(inst.V[a]) * lam + g - 1 + 1e-9, (name, a, cpa))
            check("D4", cpa <= 3.45 * mu_a[a] + g - 1 + 1e-9, (name, a, cpa))
            # settings: roundtrip, invalid ranks rejected, |W| < 2^B, |I| bounds
            zs = list(net.settings(a))
            sample = zs if len(zs) <= 300 else rng.sample(zs, 300)
            for z in sample:
                dec = net.decode(a, z)
                check("D2", dec is not None and net.encode(a, *dec) == z, (name, a, "roundtrip"))
                for b in range(g):
                    if b == a:
                        continue
                    e_, mu_, w1 = net.e[(a, b)], net.mu[(a, b)], net.w1[(a, b)]
                    if (1 << w1) > comb(e_, mu_):      # an unused rank exists
                        p, w = net.layout[a][b]
                        bad = list(z); bad[p:p + w1] = to_bits(comb(e_, mu_), w1)
                        check("D2", net.decode(a, tuple(bad)) is None, (name, a, b, "invalid rank"))
            for z, w in tabs[a].items():
                check("D3", abs(w) < 2 ** Bparam, (name, a, w, Bparam))
                nua = len(inst.V[a])
                I = inst.I(a, net.decode(a, z)[0])
                check("D3", abs(I) <= Delta ** (2 * nua) * 20 ** nua, (name, a, I))
                check("D3", abs(I) <= 2 ** len(inst.internal[a]) * 20 ** nua, (name, a, I))
        # D3: Psi = sum_theta f f'  and symmetry
        for a in range(g):
            for b in range(a + 1, g):
                check("D3", net.c[(a, b)] == net.c[(b, a)], (name, a, b))
                za_s = list(tabs[a]) or list(itertools.islice(net.settings(a), 4))
                zb_s = list(tabs[b]) or list(itertools.islice(net.settings(b), 4))
                pairs = [(x, y) for x in za_s[:6] for y in zb_s[:6]]
                for za, zb in pairs:
                    psi = net.Psi(a, b, za, zb)
                    check("D3", psi == net.Psi(b, a, zb, za), (name, a, b, "symmetry"))
                    cab = net.c[(a, b)]
                    if cab <= 10:
                        thetas = itertools.product((0, 1), repeat=cab)
                    else:
                        thetas = {net.proj(a, b, za), net.proj(b, a, zb)} | \
                                 {tuple(rng.randrange(2) for _ in range(cab)) for _ in range(20)}
                    tot = sum(net.f(a, b, za, th) * net.f(b, a, zb, th) for th in thetas)
                    check("D3", tot == psi, (name, a, b, "factorisation"))
        # D5: U(mu)
        U = net.U()
        prodC = 1
        npairs = 0
        for (a, b), v in mu.items():
            cc = comb(len(inst.Eab[(a, b)]), v)
            prodC *= cc
            npairs += cc >= 2
        check("D5", prodC <= comb(mx, M), (name, "Vandermonde"))
        check("D5", M <= n, (name, "M <= n"))
        check("D5", U == 2 * sum(net.cp[(a, b)] for (a, b) in mu) + 2 * comb(g, 3), (name, "U formula"))
        check("D5", U <= 2 * clog2(comb(mx, M)) + 2 * npairs + 4 * M + 2 * comb(g, 3), (name, U))
        check("D5", U <= 2 * n * math.log2(2 * math.e * dbar) + g ** 3 + 1e-9, (name, U))
        check("D5", U <= 2 * n * lam + g ** 3 + 1e-9, (name, U))
    check("D6", n_adm <= (2 * nu + 1) ** comb(g, 2), (name, n_adm))
    check("D7", total_adm == n * hc, (name, total_adm, n * hc))
    check("D7", total_all == n * hc, (name, total_all, n * hc))
    bound_exact = 2 * clog2(comb(mx, min(n, mx))) + 2 * comb(g, 2) + 4 * n + 2 * comb(g, 3)
    bound_D = 2 * n * lam + g ** 3
    print(f"{name:<10} n={n} m={m:2d} Δ={Delta} d̄={dbar:4.2f} g={g} ν={nu} m_×={mx:2d} #HC={hc:3d} "
          f"profiles={n_all:4d} adm={n_adm:4d} | U_new={U_max:3d} U_old={U_old:3d} "
          f"bound_exact={bound_exact:3d} 2n·log(2eΔ)+g³={bound_D:6.1f} P={Pparam} B={Bparam}"
          f" {'ok' if total_adm == n * hc else 'MISMATCH'}")


# ------------------------------------------------------------------ instances
def balanced_blob(n, g):
    return [v * g // n for v in range(n)]


def fits(n, E, blob, g, max_delta=6, max_cross=9):
    cross = [e for e in E if blob[e[0]] != blob[e[1]]]
    if len(cross) > max_cross:
        return False
    inc = [sum(1 for e in cross if a in (blob[e[0]], blob[e[1]])) for a in range(g)]
    return max(inc) <= max_delta and len(set(blob)) == g


def make_instance(i):
    kind = i % 5
    for _ in range(500):
        if kind == 0:      # random graph, random (arbitrary) blobs
            n = rng.randrange(5, 10); g = rng.choice([2, 2, 3, 3, 4])
            m = rng.randrange(n, min(comb(n, 2), n + 6) + 1)
            E = random_graph(n, m, rng, min_deg2=True)
            blob = [rng.randrange(g) for _ in range(n)]
        elif kind == 1:    # random graph, vertex-balanced blobs
            n = rng.randrange(5, 10); g = rng.choice([2, 3, 3, 4])
            m = rng.randrange(n, min(comb(n, 2), n + 6) + 1)
            E = random_graph(n, m, rng, min_deg2=True)
            perm = list(range(n)); rng.shuffle(perm)
            bb = balanced_blob(n, g); blob = [bb[perm[v]] for v in range(n)]
        elif kind == 2:    # a hub of degree n-1 on a cycle (Δ large, m ~ 2n)
            n = rng.randrange(5, 9); g = rng.choice([2, 3])
            cyc = list(range(1, n)); rng.shuffle(cyc)
            E = {(min(x, y), max(x, y)) for x, y in zip(cyc, cyc[1:] + cyc[:1])}
            E |= {(0, v) for v in range(1, n)}
            E = sorted(E)
            blob = [rng.randrange(g) for _ in range(n)]
        elif kind == 3:    # planted Hamiltonian cycle visiting blobs in interleaving order (g = 4)
            g = 4
            sizes = [rng.randrange(1, 3) for _ in range(g)]
            n, E, blob = planted_graph(sizes, 0.3, rng.randrange(0, 3), rng, plant_hc=True,
                                       border=[0, 2, 1, 3])
        else:              # planted blobs, random crossing edges, g = 3
            g = 3
            sizes = [rng.randrange(2, 4) for _ in range(g)]
            n, E, blob = planted_graph(sizes, 0.5, rng.randrange(2, 6), rng)
        if n < 4:
            continue
        deg = degrees(n, E)
        if min(deg) < 2:
            continue
        if fits(n, E, blob, g):
            return f"inst{i}/k{kind}", n, E, blob, rng.randrange(n), g
    raise RuntimeError("no instance")


def main():
    d1()
    print(f"seed={seed}, {NINST} instances; U_new = max over admissible profiles of U(mu); "
          f"U_old = 2 sum w_ab + 2C(g,3) (exact-hc-theorem.md §5)")
    for i in range(NINST):
        run_instance(*make_instance(i))
    # the asymptotic comparison, for the record
    print("\nasymptotic U bounds (bits): new 2n·log2(2eΔ)   vs   old 2·log2(5)·m = log2(5)·n·Δ (Δ-regular)")
    for n, D in [(10 ** 3, 3), (10 ** 3, 10), (10 ** 3, 100), (10 ** 6, 10), (10 ** 6, 1000)]:
        print(f"  n={n:>8} Δ={D:>5}: new={2 * n * math.log2(2 * math.e * D):12.0f}  old={math.log2(5) * n * D:12.0f}")
    print("\ncheck counts:", ", ".join(f"{k}={v}" for k, v in sorted(COUNT.items())))
    if FAIL:
        print(f"FAIL ({len(FAIL)} failed checks)")
        return 1
    print("PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
