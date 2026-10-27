"""Independent numerical checks of every identity in research/exact-hc-theorem.md.
Exact integer arithmetic throughout.  Run:  python3 proof_checks.py [seed] [instances]

  C1  Lemma 2.1   n #HC(G) = sum_{2-factors X} tau(V,X); tau(V,X) in {0,n}; tau by brute force
  C2  Lemma 2.3   tau(V,X) = det L_X^(r) = [Omega] prod_{e in X} (1 + q_e)      (random generator order)
  C3  Lemma 2.2   [Omega] prod_k thetabar(b_k) theta(b_k) = det(b_1..b_N)^2      (random integer vectors)
  C4  Lemma 3.1   Koszul rule for random homogeneous sequences and permutations
  C5  Lemma 3.3   factorisation over blobs: [Omega](A_1...A_g) = prod_a [Omega_a](A_a)
  C6  (3.1)       sum_l alpha_l beta_l = 1 + q_e, parities of the pieces, also when an end is r
  C7  Prop 4.1    prod_k alpha_k beta_k = eps(l) Gamma_1 ... Gamma_g as algebra elements
  C8  Prop 4.2    eps(l) = prod_a sigma_a(l) * (-1)^{sum_{a<c<b<d} P_ab P_cd} = prod_a sigma_a chi_a
  C9  Prop 4.1'   the sign rule with fresh generators (no cancellation), random blob pairs/orders
  C10 Thm 5.2     Definition-2 conditions of the network; Psi = sum_theta f f'; bit bounds
  C11 Thm 5.2     Z(network) by brute force over all settings = n #HC; also via Lemma-1 grouping
  C12 ablations   dropping the interleaving or local signs gives wrong values on some instance
"""
import itertools
import random
import sys
from math import comb

from proof_lib import (ONE, ZERO, gmul, gadd, gprod, gscale, word, parity_of, mono_mul,
                       hc_count, two_factors, det_bareiss, reduced_laplacian,
                       count_spanning_trees_brute, random_graph, planted_graph, Gens,
                       LABELS, pieces, pi_, c_kl, interleave, Instance, HCNetwork,
                       eval_network_brute, eval_network_grouped, width5)

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
NINST = int(sys.argv[2]) if len(sys.argv) > 2 else 60
rng = random.Random(seed)
FAIL = []
COUNT = {}


def check(name, cond, info=""):
    COUNT[name] = COUNT.get(name, 0) + 1
    if not cond:
        FAIL.append((name, info))
        print("FAIL", name, info)


# ------------------------------------------------------------------------------------- C3, C4
def c3():
    for _ in range(200):
        N = rng.randint(1, 5)
        Bv = [[rng.randint(-2, 2) for _ in range(N)] for _ in range(N)]
        gens_order = list(range(2 * N)); rng.shuffle(gens_order)
        bar = {u: gens_order[2 * u] for u in range(N)}
        psi = {u: gens_order[2 * u + 1] for u in range(N)}
        def tb(b):
            return {1 << bar[u]: b[u] for u in range(N) if b[u]} if any(b) else {}
        def th(b):
            return {1 << psi[u]: b[u] for u in range(N) if b[u]} if any(b) else {}
        # the elements thetabar(b) need sums of generators
        def lin(coeffs, gm):
            out = {}
            for u in range(N):
                if coeffs[u]:
                    out[1 << gm[u]] = coeffs[u]
            return out
        prod = gprod([gmul(lin(Bv[k], bar), lin(Bv[k], psi)) for k in range(N)])
        Om = gprod([gmul({1 << bar[u]: 1}, {1 << psi[u]: 1}) for u in range(N)])
        (m, s), = Om.items()
        top = prod.get(m, 0) * s
        cols = [[Bv[k][u] for k in range(N)] for u in range(N)]
        check("C3 Berezin-Cauchy-Binet", top == det_bareiss(cols) ** 2, (Bv, top))


def c4():
    for _ in range(300):
        ngen = rng.randint(2, 10)
        M = rng.randint(1, 6)
        ys, par = [], []
        for _ in range(M):
            # random homogeneous element: sum of monomials of one parity
            p = rng.randint(0, 1)
            el = {}
            for _ in range(rng.randint(1, 3)):
                deg = rng.choice([d for d in range(ngen + 1) if d % 2 == p])
                gens = rng.sample(range(ngen), deg)
                for mm, cc in word(gens).items():
                    el[mm] = el.get(mm, 0) + cc * rng.choice([-2, -1, 1, 2])
            el = {k: v for k, v in el.items() if v}
            ys.append(el); par.append(p)
        sigma = list(range(M)); rng.shuffle(sigma)
        lhs = gprod([ys[s] for s in sigma])
        rhs = gprod(ys)
        pos = {s: t for t, s in enumerate(sigma)}
        e = sum(par[s] * par[t] for s in range(M) for t in range(s + 1, M) if pos[s] > pos[t])
        check("C4 Koszul", lhs == (gscale(rhs, -1) if e & 1 else rhs))


# ------------------------------------------------------------------------------------- C9
def c9():
    """sign rule with fresh generators: every piece is a fresh odd generator (odd edges) or a
    product of two fresh generators / 1 (even edges); random g, blob pairs, edge order, gen order."""
    for _ in range(400):
        g = rng.randint(2, 7)
        m = rng.randint(1, 8)
        pairs = [tuple(sorted(rng.sample(range(g), 2))) for _ in range(m)]
        par = [rng.randint(0, 1) for _ in range(m)]
        ngen = 0
        al, be = [], []
        order_of = list(range(4 * m)); rng.shuffle(order_of)
        for k in range(m):
            if par[k]:
                al.append({1 << order_of[ngen]: 1}); be.append({1 << order_of[ngen + 1]: 1}); ngen += 2
            else:
                al.append(word([order_of[ngen], order_of[ngen + 1]]))
                be.append(ONE if rng.random() < 0.5 else word([order_of[ngen + 2], order_of[ngen + 3]]))
                ngen += 4
        lhs = gprod([gmul(al[k], be[k]) for k in range(m)])
        Gam = []
        for a in range(g):
            seq = []
            for k in range(m):
                if pairs[k][0] == a:
                    seq.append(al[k])
                elif pairs[k][1] == a:
                    seq.append(be[k])
            Gam.append(gprod(seq))
        rhs = gprod(Gam)
        tot = sum(par[k] * par[l] * c_kl(*pairs[k], *pairs[l]) for k in range(m) for l in range(k + 1, m))
        check("C9 sign rule (fresh generators)", lhs == (gscale(rhs, -1) if tot & 1 else rhs))
        # decomposition: local part + interleaving part
        loc = 0
        for k in range(m):
            for l in range(k + 1, m):
                if set(pairs[k]) & set(pairs[l]):
                    loc += par[k] * par[l] * c_kl(*pairs[k], *pairs[l])
                else:
                    check("C9 c_kl = interleave mod 2",
                          c_kl(*pairs[k], *pairs[l]) % 2 == interleave(*pairs[k], *pairs[l]))
        Pab = {}
        for k in range(m):
            Pab[pairs[k]] = (Pab.get(pairs[k], 0) + par[k]) % 2
        inter = sum(Pab.get((a, b), 0) * Pab.get((c, d), 0)
                    for a in range(g) for c in range(a + 1, g) for b in range(c + 1, g) for d in range(b + 1, g))
        check("C9 eps = local * interleave", (tot - loc - inter) % 2 == 0)


# ------------------------------------------------------------------------------------- graph instances
def make_instance(kind):
    if kind == "random":
        n = rng.randint(4, 9)
        m = rng.randint(n, min(n * (n - 1) // 2, 2 * n))
        E = random_graph(n, m, rng)
        g = rng.randint(2, min(5, n))
        blob = [rng.randrange(g) for _ in range(n)]  # arbitrary partition, empty blobs allowed
    elif kind == "interleave":
        # g in {4,5}, Hamiltonian cycle visiting the blobs in a cyclic order with interleaving
        # chords (e.g. 0,2,1,3), the case in which the interleaving sign matters
        g = rng.choice([4, 4, 5])
        sizes = [rng.randint(1, 3) for _ in range(g)]
        border = [0, 2, 1, 3] if g == 4 else rng.choice([[0, 2, 4, 1, 3], [0, 3, 1, 4, 2], [0, 2, 1, 3, 4]])
        n, E, blob = planted_graph(sizes, rng.choice([0.5, 1.0]), rng.randint(0, 2), rng,
                                   plant_hc=True, border=border)
    else:
        g = rng.randint(2, 4)
        sizes = [rng.randint(2, 4) for _ in range(g)]
        while sum(sizes) > 12:
            sizes[rng.randrange(g)] -= 1
        sizes = [max(1, s) for s in sizes]
        n_cross = rng.randint(0, 3) if kind == "planted_hc" else rng.randint(2, 6)
        n, E, blob = planted_graph(sizes, rng.choice([0.3, 0.6, 1.0]), n_cross, rng,
                                   plant_hc=(kind == "planted_hc"))
        # random relabelling of blob indices so the circle order is arbitrary
        perm = list(range(g)); rng.shuffle(perm)
        blob = [perm[b] for b in blob]
    r = rng.randrange(n)
    if kind == "interleave2":
        # a 2-factor with a non-root cycle through the blobs in an interleaving cyclic order
        # (0,2,1,3[,4]): here the odd labels contribute and the interleaving sign is needed
        g = rng.choice([4, 5])
        border = [0, 2, 1, 3] if g == 4 else rng.choice([[0, 2, 4, 1, 3], [0, 3, 1, 4, 2], [0, 2, 1, 3, 4]])
        extra = rng.randint(3, 6)
        blob = list(range(g)) + [rng.randrange(g) for _ in range(extra)]
        n = len(blob)
        perm = list(range(n)); rng.shuffle(perm)
        blob = [blob[perm[v]] for v in range(n)]
        first = {}
        for v in range(n):
            first.setdefault(blob[v], v)
        C1 = [first[a] for a in border]
        rest = [v for v in range(n) if v not in C1]
        rng.shuffle(rest)
        Es = set()
        for cyc in (C1, rest):
            for x, y in zip(cyc, cyc[1:] + cyc[:1]):
                Es.add((min(x, y), max(x, y)))
        allp = [(i, j) for i in range(n) for j in range(i + 1, n) if (i, j) not in Es]
        for e in rng.sample(allp, rng.randint(1, 4)):
            Es.add(e)
        E = sorted(Es)
        r = rng.choice(rest)
    return n, E, blob, r, g


def graph_checks(n, E, blob, r, g):
    hc = hc_count(n, E)
    F = two_factors(n, E)
    Gn = Gens(n, r, rng)  # random generator order
    tot = 0
    for X in F:
        XE = [E[k] for k in X]
        t_brute = count_spanning_trees_brute(n, XE)
        t_det = det_bareiss(reduced_laplacian(n, XE, r))
        t_ber = Gn.top(gprod([Gn.one_plus_q(i, j) for (i, j) in XE]), range(n))
        check("C1 tau in {0,n}", t_brute in (0, n))
        check("C2 tau = det = Berezin", t_brute == t_det == t_ber, (t_brute, t_det, t_ber))
        tot += t_brute
    check("C1 n#HC = sum tau", n * hc == tot, (n, hc, tot))
    # C6 pieces, all edges (as crossing edges with either end low)
    for (i, j) in E:
        for s, t in ((i, j), (j, i)):
            S = ZERO
            for l in (0, 1, 2, 3):
                al, be = pieces(Gn, s, t, l)
                pa, pb_ = parity_of(al), parity_of(be)
                check("C6 pieces homogeneous of parity pi(l)",
                      pa is not None and pb_ is not None and
                      (not al or pa == pi_(l)) and (not be or pb_ == pi_(l)))
                S = gadd(S, gmul(al, be))
            check("C6 sum of pieces = 1+q_e", S == Gn.one_plus_q(i, j))
    return hc


def instance_checks(n, E, blob, r, g, hc, do_net=True):
    inst = Instance(n, E, blob, r, g=g, rng=rng, gen_rng=rng)
    m = inst.m
    # C5 factorisation of the top coefficient over blobs, random elements A_a in Lambda_a
    for _ in range(3):
        As = []
        for a in range(g):
            gens = []
            for v in inst.V[a]:
                gens += [inst.Gn.pb(v), inst.Gn.ps(v)]
            gens = [x for x in gens if x]
            A = {0: rng.randint(-2, 2)}
            for _ in range(4):
                if gens:
                    k = rng.randint(1, len(gens))
                    A = gadd(A, gscale(gprod(rng.sample(gens, k)), rng.randint(-2, 2)))
            A = gadd(A, gscale(inst.Gn.omega(inst.V[a]), rng.randint(-3, 3)))
            As.append(A)
        lhs = inst.Gn.top(gprod(As), range(n))
        rhs = 1
        for a in range(g):
            rhs *= inst.Gn.top(As[a], inst.V[a])
        check("C5 blockwise Berezin", lhs == rhs)
    # C7/C8 on all labellings (or a sample)
    labs_all = itertools.product(LABELS, repeat=m) if 5 ** m <= 4000 else \
        (tuple(rng.choice(LABELS) for _ in range(m)) for _ in range(4000))
    for lab in labs_all:
        prod = gprod([gmul(*pieces(inst.Gn, s, t, lab[k])) for k, (s, t) in enumerate(inst.cross)])
        lab_at_all = dict(enumerate(lab))
        Gam = gprod([inst.Gamma(a, {k: lab[k] for k in inst.delta[a]}) for a in range(g)])
        e = inst.eps(lab)
        check("C7 sign rule as elements", prod == (gscale(Gam, -1) if e < 0 else Gam))
        sig = 1
        for a in range(g):
            sig *= inst.sigma(a, {k: lab[k] for k in inst.delta[a]})
        inter = 0
        for a in range(g):
            for c in range(a + 1, g):
                for b in range(c + 1, g):
                    for d in range(b + 1, g):
                        inter += inst.P(a, b, lab_at_all) * inst.P(c, d, lab_at_all)
        check("C8 eps = local * interleave", e == sig * (-1) ** inter)
        chi_tot = 1
        net0 = HCNetwork(inst)
        for a in range(g):
            y = {(c, d): inst.P(c, d, lab_at_all) for (c, d) in net0.Q[a]}
            chi_tot *= net0.chi(a, {k: lab[k] for k in inst.delta[a]}, y)
        check("C8 prod chi_a = interleaving sign", chi_tot == (-1) ** inter)
    # direct labelling sum  sum_l eps(l) prod_a I_a(l) = n #HC
    if 5 ** m <= 80000:
        Z = 0
        for lab in itertools.product(LABELS, repeat=m):
            val = inst.eps(lab)
            for a in range(g):
                val *= inst.I(a, {k: lab[k] for k in inst.delta[a]})
                if not val:
                    break
            Z += val
        check("C11 sum_l eps prod I_a = n#HC", Z == n * hc, (Z, n * hc))
    if not do_net:
        return None
    net = HCNetwork(inst)
    # C10 Definition 2
    P = net.P_param()
    mu = net.mu()
    for a in range(g):
        check("C10 P_a <= P", net.Plen[a] <= P)
        check("C10 (i) sum_b c_ab <= P", sum(net.c[(a, b)] for b in range(g) if b != a) <= P)
        for b in range(g):
            if b != a:
                check("C10 c symmetric", net.c[(a, b)] == net.c[(b, a)])
    check("C10 U = 2 sum_{a<b} w_ab + 2 C(g,3) (exact)",
          net.U() == 2 * sum(width5(len(v)) for v in inst.Eab.values()) + 2 * comb(g, 3))
    for (a, b), ks in inst.Eab.items():
        w = width5(len(ks))
        check("C10 w_ab = ceil(e_ab log2 5) (exact: 2^(w-1) < 5^e <= 2^w)",
              (len(ks) == 0 and w == 0) or (2 ** (w - 1) < 5 ** len(ks) <= 2 ** w))
    check("C10 U <= 2 log2(5) m_x + g^2 + g^3/3 (via w_ab <= e log2 5 + 1)",
          net.U() <= 2 * sum(width5(len(v)) for v in inst.Eab.values()) + 2 * comb(g, 3)
          and 2 * comb(g, 3) <= g ** 3 / 3 and len(inst.Eab) <= g * g / 2)
    S = [list(net.settings(a)) for a in range(g)]
    B = 2 * mu + 1
    for a in range(g):
        check("C10 |S_a| = 5^|delta(a)| 2^|Q_a|", len(S[a]) == 5 ** len(inst.delta[a]) * 2 ** len(net.Q[a]))
        check("C10 settings distinct and in S_a", len(set(S[a])) == len(S[a]) and all(net.in_S(a, z) for z in S[a]))
        bound = 10 ** len(inst.internal[a]) * 2 ** len(inst.delta[a])
        for z in S[a]:
            check("C10 |W_a| <= 10^|E(V_a)| 2^|delta(a)| < 2^B", abs(net.W(a, z)) <= bound < 2 ** B)
    # factorisation Psi = sum_theta f f'  (all setting pairs if small, else a sample)
    for a in range(g):
        for b in range(a + 1, g):
            if len(S[a]) * len(S[b]) <= 3000:
                pairs = [(za, zb) for za in S[a] for zb in S[b]]
            else:
                pairs = [(rng.choice(S[a]), rng.choice(S[b])) for _ in range(1500)]
                # and pairs that agree on the shared labels (where Psi can be 1)
                byproj = {}
                for zb in S[b]:
                    byproj.setdefault(net.proj(b, a, zb), []).append(zb)
                for za in rng.sample(S[a], min(1500, len(S[a]))):
                    cand = byproj.get(net.proj(a, b, za))
                    if cand:
                        pairs.append((za, rng.choice(cand)))
            cab = net.c[(a, b)]
            for za, zb in pairs:
                pa, pb_ = net.proj(a, b, za), net.proj(b, a, zb)
                check("C10 proj length c_ab", len(pa) == cab == len(pb_))
                # Psi = sum_theta f_ab(za,theta) f_ba(zb,theta); f is the indicator of proj, so the
                # sum has the single possible term theta = proj(za)
                fsum = net.f(a, b, za, pa) * net.f(b, a, zb, pa)
                check("C10 Psi = sum f f'", net.Psi(a, b, za, zb) == fsum == net.Psi(b, a, zb, za))
            if cab <= 10 and len(S[a]) * len(S[b]) <= 400:
                for za in S[a]:
                    for zb in S[b]:
                        fs = sum(net.f(a, b, za, th) * net.f(b, a, zb, th)
                                 for th in itertools.product((0, 1), repeat=cab))
                        check("C10 Psi = sum over all theta", fs == net.Psi(a, b, za, zb))
    # C11 brute force value of the network
    size = 1
    for a in range(g):
        size *= len(S[a])
    Zb = None
    if size <= 10 ** 13:
        Zb = eval_network_brute(net)
        check("C11 Z(network, brute force) = n#HC", Zb == n * hc, (Zb, n * hc))
    # Lemma-1 grouping into K = 2 groups (and K = 3 if g >= 3)
    for K in (2, 3):
        if g < K:
            continue
        nodes = list(range(g)); rng.shuffle(nodes)
        groups = [sorted(nodes[i::K]) for i in range(K)]
        if max(sum(len(S[a]) for a in G) for G in groups) > 0 and \
           max(eval_size(S, G) for G in groups) <= 2 * 10 ** 6:
            Zg = eval_network_grouped(net, groups)
            check("C11 Z(network via grouping) = n#HC", Zg == n * hc, (K, Zg, n * hc))
    # ablations (C12)
    abl = {}
    for mode in ("nointerleave", "nolocal", "none"):
        netx = HCNetwork(inst, sign_mode=mode)
        if size <= 10 ** 13:
            abl[mode] = eval_network_brute(netx)
    return Zb, abl


def eval_size(S, G):
    s = 1
    for a in G:
        s *= len(S[a])
    return s


def main():
    c3(); c4(); c9()
    ablation_hits = {"nointerleave": 0, "nolocal": 0, "none": 0}
    n_net = 0
    print(f"{'kind':8s} {'n':>2s} {'|E|':>3s} {'g':>2s} {'m_x':>3s} {'#HC':>4s} {'n#HC':>5s} {'Z_net':>6s}  ablations")
    done = 0
    tries = 0
    while done < NINST and tries < 50 * NINST:
        tries += 1
        kind = ["random", "planted", "planted_hc", "interleave", "interleave2", "interleave2"][done % 6]
        n, E, blob, r, g = make_instance(kind)
        inst_probe = Instance(n, E, blob, r, g=g)
        if inst_probe.m > 7 or max(len(inst_probe.delta[a]) for a in range(g)) > 6 or \
           max(len(inst_probe.internal[a]) for a in range(g)) > 10:
            continue
        hc = graph_checks(n, E, blob, r, g)
        res = instance_checks(n, E, blob, r, g, hc)
        done += 1
        Zb, abl = res
        if Zb is not None:
            n_net += 1
        for k, v in abl.items():
            if v != n * hc:
                ablation_hits[k] += 1
        print(f"{kind:8s} {n:2d} {len(E):3d} {g:2d} {inst_probe.m:3d} {hc:4d} {n*hc:5d} {str(Zb):>6s}  "
              + " ".join(f"{k}={v}" for k, v in abl.items()))
    check("C12 ablation: no interleaving sign is wrong somewhere", ablation_hits["nointerleave"] > 0)
    check("C12 ablation: no local sign is wrong somewhere", ablation_hits["nolocal"] > 0)
    print()
    for k in sorted(COUNT):
        print(f"  {COUNT[k]:8d}  {k}")
    print(f"instances: {done}, brute-force network evaluations: {n_net}, ablation failures: {ablation_hits}")
    print("ALL CHECKS PASSED" if not FAIL else f"{len(FAIL)} FAILURES")


if __name__ == "__main__":
    main()
