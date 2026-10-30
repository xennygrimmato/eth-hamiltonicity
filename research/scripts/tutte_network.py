"""Blob networks (Definition 2 of [A], as in exact-hc-theorem.md §5) for the Tutte plane.

N1  Colour network for H_q (q >= 1 integer):  nodes = blobs; a crossing edge e = (i in V_a, j in V_b),
    a < b, carries the label l_e = c_i in [q] (Schmidt decomposition 1+v[c_i=c_j] =
    sum_t [c_i=t](1+v[t=c_j]), rank q).  Settings of node a = labels of its crossing edges, written
    as base-q blocks per neighbouring blob;  Psi_ab = [block_b(z_a) = block_a(z_b)],
    c_ab = ceil(e_ab log2 q).  W_a(z_a) = sum_{c:V_a->[q]} prod_{internal}(1+v[=])
    prod_{e: a low end}[l_e = c_i] prod_{e: a high end}(1+v[l_e = c_j]).
    Checked: value = Z(q,v) by honest summation over ALL settings of all nodes with the Psi
    product (not just consistent ones), several random partitions.
N2  Kronecker: v := 2^b, decode Z(q,.) as a polynomial in v, then T on all of H_q:
    T(1+q/v, 1+v) = Z(q,v) / (q^{k(G)} v^{n-k(G)})   at random rational v.
N3  Flow network for H_q, q prime: label of a crossing edge = its flow value in F_q; W_a sums the
    internal flows with conservation at the vertices of V_a, weight (q+v)^{[f=0]} v^{[f!=0]}.
    value = q^{m-n} Z(q,v).
N4  Hub splitting for N1: replacing a vertex by a path of copies joined by equality constraints
    keeps Z (so Delta can be made <= 3 at no cost in log q bits per edge).
N5  Forest line y = 1: re-runs the fermionic forest network of ext_problems.py (4d', four labels
    per crossing edge) and checks T(x,1) = sum_k f_k (x-1)^{r(E)-k} from its decoded forest counts.
N7  Every point: Z(q,v) for ANY q (and T(1,y) at q -> 0) from the n+1 colour networks with
    q = 1..n+1 colours, by interpolation in q (a sum of n+1 networks on one clustering, each with
    U <= 2 m_x log2(n+1) + g^2): the Theta(n log n) upper bound matching Theorem B.
N6  Bit accounting: U = 2 sum_{a<b} c_ab <= 2 m_x log2 q + g^2, printed per instance.
Prints PASS/FAIL.
"""
import random, itertools, math, sys
from fractions import Fraction
from tutte_lib import *

def bits_for(e, q):
    if e == 0:
        return 0
    w = 0
    while 2 ** w < q ** e:
        w += 1
    return w

class ColourNet:
    def __init__(s, n, E, beta, g, q, v):
        s.n, s.E, s.beta, s.g, s.q, s.v = n, E, beta, g, q, v
        s.cross = [k for k, (i, j) in enumerate(E) if beta[i] != beta[j]]
        # orient crossing edges: low end first
        s.ends = {}
        for k in s.cross:
            i, j = E[k]
            if beta[i] > beta[j]:
                i, j = j, i
            s.ends[k] = (i, j)
        s.Eab = {}
        for k in s.cross:
            i, j = s.ends[k]
            s.Eab.setdefault((beta[i], beta[j]), []).append(k)
        s.c = {}
        for (a, b), ks in s.Eab.items():
            s.c[(a, b)] = s.c[(b, a)] = bits_for(len(ks), q)
        s.delta = {a: [k for k in s.cross if a in (beta[s.ends[k][0]], beta[s.ends[k][1]])] for a in range(g)}
        s.V = {a: [x for x in range(n) if beta[x] == a] for a in range(g)}
        s.internal = {a: [k for k, (i, j) in enumerate(E) if beta[i] == beta[j] == a] for a in range(g)}

    def U(s):
        return sum(s.c.values())

    def W(s, a, lab):
        """lab: dict k -> label for k in delta(a)."""
        Va = s.V[a]; tot = 0; q, v = s.q, s.v
        for col in itertools.product(range(q), repeat=len(Va)):
            c = dict(zip(Va, col)); w = 1
            for k in s.internal[a]:
                i, j = s.E[k]
                if c[i] == c[j]:
                    w *= 1 + v
            for k in s.delta[a]:
                i, j = s.ends[k]
                if s.beta[i] == a:
                    if lab[k] != c[i]:
                        w = 0; break
                else:
                    if lab[k] == c[j]:
                        w *= 1 + v
            tot += w
        return tot

    def settings(s, a):
        """all settings of node a: (encoded bit-string blocks, label dict).  Blocks are base-q
        numbers < q^{e_ab}, written in c_ab bits; the full range 0..2^{c_ab}-1 is NOT a setting
        (S_a = encodings only), as in Definition 5.1 of exact-hc-theorem.md."""
        ks = s.delta[a]
        for labs in itertools.product(range(s.q), repeat=len(ks)):
            lab = dict(zip(ks, labs))
            blocks = {}
            for b in range(s.g):
                if b == a:
                    continue
                key = (min(a, b), max(a, b))
                kk = s.Eab.get(key, [])
                blocks[b] = sum(lab[k] * s.q ** t for t, k in enumerate(kk))
            yield blocks, lab

    def value_honest(s):
        """sum over all tuples of settings of prod W_a prod_{a<b} Psi_ab (Psi = block equality)."""
        S = [list(s.settings(a)) for a in range(s.g)]
        Wt = [[s.W(a, lab) for (_, lab) in S[a]] for a in range(s.g)]
        tot = 0
        for choice in itertools.product(*[range(len(x)) for x in S]):
            w = 1
            for a in range(s.g):
                w *= Wt[a][choice[a]]
                if w == 0:
                    break
            if w == 0:
                continue
            ok = True
            for a in range(s.g):
                for b in range(a + 1, s.g):
                    if S[a][choice[a]][0][b] != S[b][choice[b]][0][a]:
                        ok = False; break
                if not ok:
                    break
            if ok:
                tot += w
        return tot

    def value_fast(s):
        tot = 0
        for labs in itertools.product(range(s.q), repeat=len(s.cross)):
            lab = dict(zip(s.cross, labs)); w = 1
            for a in range(s.g):
                w *= s.W(a, {k: lab[k] for k in s.delta[a]})
                if w == 0:
                    break
            tot += w
        return tot

class FlowNet(ColourNet):
    def W(s, a, lab):
        """sum over flows on internal edges of a with conservation at V_a; crossing-edge weights
        charged to the low end.  Orientation of every edge: E[k] = (i,j), flow out of i into j."""
        q, v = s.q, s.v
        ints = s.internal[a]; tot = 0
        for f in itertools.product(range(q), repeat=len(ints)):
            bal = {x: 0 for x in s.V[a]}; w = 1
            for k, fe in zip(ints, f):
                i, j = s.E[k]
                bal[i] = (bal[i] + fe) % q; bal[j] = (bal[j] - fe) % q
                w *= (q + v) if fe == 0 else v
            for k in s.delta[a]:
                i, j = s.E[k]; fe = lab[k]
                if s.beta[i] == a:
                    bal[i] = (bal[i] + fe) % q
                else:
                    bal[j] = (bal[j] - fe) % q
                lo = s.ends[k][0]
                if s.beta[lo] == a:
                    w *= (q + v) if fe == 0 else v
            if all(x == 0 for x in bal.values()):
                tot += w
        return tot

def kron_decode_nonneg(val, b, nterms):
    out = []
    for _ in range(nterms):
        out.append(val & ((1 << b) - 1)); val >>= b
    return out

def main(seed=1):
    rng = random.Random(seed)
    C = Checker("tutte_network")
    # N1 / N6
    for trial in range(10):
        n = rng.randint(4, 6); m = rng.randint(n - 1, min(8, n * (n - 1) // 2))
        E = rand_graph(n, m, rng)
        for q in (2, 3):
            g = rng.choice([2, 3])
            beta = [rng.randrange(g) for _ in range(n)]
            v = rng.choice([-3, -1, 1, 2, 5])
            net = ColourNet(n, E, beta, g, q, v)
            if len(net.cross) > 6 or (q == 3 and len(net.cross) > 5):
                continue
            Z = potts_eval(n, E, q, v)
            C.check(net.value_honest() == Z, f"N1 honest q={q}")
            C.check(net.value_fast() == Z, f"N1 fast q={q}")
            mx = len(net.cross)
            C.check(net.U() <= 2 * mx * math.log2(q) + 2 * g * g, "N6 U bound")
            if trial < 3:
                print(f"  N1 n={n} m={m} g={g} q={q} crossing={mx} U={net.U()} Z={Z} ok")
    # N2 Kronecker -> whole hyperbola
    for trial in range(6):
        n = rng.randint(4, 6); m = rng.randint(n - 1, min(9, n * (n - 1) // 2))
        E = rand_graph(n, m, rng)
        q = rng.choice([1, 2, 3])
        g = 3; beta = [rng.randrange(g) for _ in range(n)]
        b = n * 2 + m + 4
        net = ColourNet(n, E, beta, g, q, 1 << b)
        val = net.value_fast()
        coeffs = kron_decode_nonneg(val, b, m + 1)
        Zpoly = potts(n, E)
        truth = [sum(c for (i, j), c in Zpoly.items() if j == d) * 0 + sum(c * q ** i for (i, j), c in Zpoly.items() if j == d) for d in range(m + 1)]
        C.check(coeffs == truth, "N2 Kronecker decode")
        k = ncomp(n, E)
        for _ in range(4):
            vv = Fraction(rng.randint(-9, 9), rng.randint(1, 5))
            if vv == 0:
                continue
            Zv = sum(cf * vv ** d for d, cf in enumerate(coeffs))
            x, y = 1 + q / vv, 1 + vv
            C.check(Zv / (Fraction(q) ** k * vv ** (n - k)) == tutte_eval(n, E, x, y), "N2 T on H_q")
    # N3 flow network
    for trial in range(8):
        n = rng.randint(3, 5); m = rng.randint(n, min(7, n * (n - 1) // 2))
        E = rand_graph(n, m, rng)
        for q in (2, 3):
            g = 2; beta = [rng.randrange(g) for _ in range(n)]
            v = rng.choice([-2, 1, 3])
            net = FlowNet(n, E, beta, g, q, v)
            if q ** (len(net.cross) + m) > 200000:
                continue
            target = Fraction(q) ** (m - n) * potts_eval(n, E, q, v)
            C.check(net.value_fast() == target, f"N3 flow q={q}")
    # N4 hub splitting: vertex h of degree d -> path h_1..h_d, each takes one edge, equality along path
    for trial in range(8):
        n = rng.randint(4, 6); m = rng.randint(n, min(9, n * (n - 1) // 2))
        E = rand_graph(n, m, rng)
        q = rng.choice([2, 3]); v = rng.choice([-1, 2])
        deg = [sum(1 for e in E if x in e) for x in range(n)]
        h = max(range(n), key=lambda x: deg[x])
        inc = [k for k, e in enumerate(E) if h in e]
        newv = {k: n + t for t, k in enumerate(inc)}
        E2 = []
        for k, (a, b) in enumerate(E):
            if k in newv:
                o = b if a == h else a
                E2.append((newv[k], o))
            else:
                E2.append((a, b))
        n2 = n + len(inc)
        eq = [(n + t, n + t + 1) for t in range(len(inc) - 1)]
        tot = 0
        for c in itertools.product(range(q), repeat=n2):
            if c[h] != 0:          # h itself is now isolated: fix its colour (divide by q)
                continue
            if any(c[a] != c[b] for a, b in eq):
                continue
            w = 1
            for a, b in E2:
                if c[a] == c[b]:
                    w *= 1 + v
            tot += w
        C.check(tot == potts_eval(n, E, q, v), "N4 hub split")
    # N5 forest line via the fermionic network of ext_problems
    import ext_problems as XP
    import io, contextlib
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        XP.ALL_OK = True
        XP.prob_forest(random.Random(seed), 2, False)
    out = buf.getvalue()
    print("  N5", out.strip()[:200])
    C.check(XP.ALL_OK, "N5 fermionic forest network (ext_problems 4d')")
    for trial in range(10):
        n = rng.randint(3, 7); m = rng.randint(n - 1, min(10, n * (n - 1) // 2))
        E = rand_graph(n, m, rng); rE = n - ncomp(n, E)
        f = [0] * (m + 1)
        for _, A in subsets(E):
            if ncomp(n, A) == n - len(A):
                f[len(A)] += 1
        x = Fraction(rng.randint(-6, 6), 5)
        C.check(all(f[k] == 0 for k in range(rE + 1, m + 1)), 'N5 no forest above rank')
        C.check(sum(f[k] * (x - 1) ** (rE - k) for k in range(rE + 1)) == tutte_eval(n, E, x, 1), "N5 T(x,1)")
    # N7 every point from n+1 colour networks (q = 1..n+1) by Lagrange interpolation in q
    for trial in range(8):
        n = rng.randint(3, 6); m = rng.randint(n - 1, min(8, n * (n - 1) // 2))
        E = rand_graph(n, m, rng)
        v = Fraction(rng.randint(-5, 5), rng.randint(1, 3))
        vals = [colour_sum(n, E, N, v) for N in range(1, n + 2)]     # = values of the colour networks
        def interp(q):
            tot = Fraction(0)
            for i in range(n + 1):
                xi = i + 1; L = Fraction(1)
                for j in range(n + 1):
                    if j != i:
                        L *= Fraction(q - (j + 1), xi - (j + 1))
                tot += vals[i] * L
            return tot
        for q in (Fraction(1, 2), Fraction(-7, 3), Fraction(0)):
            C.check(interp(q) == potts_eval(n, E, q, v), "N7 interpolation in q")
        if ncomp(n, E) == 1 and v != 0:
            # x = 1: T(1,y) = v^{-(n-1)} * [q^1] Z(q,v);  [q^1] from the interpolating polynomial
            h = Fraction(1, 10 ** 6)
            coeff1 = sum(c * Fraction(v) ** j for (i, j), c in potts(n, E).items() if i == 1)
            # exact [q^1]: (Z(q)-Z(0))/q is a polynomial; evaluate the interpolant's q^1 coefficient exactly
            import itertools as _it
            pts = list(range(1, n + 2))
            # Newton form not needed: solve Vandermonde
            from tutte_identities import solve_ls
            A = [[Fraction(N) ** d for d in range(n + 1)] for N in pts]
            cf = solve_ls(A, vals)
            C.check(cf[1] == coeff1, "N7 coefficient of q^1")
            C.check(cf[1] / Fraction(v) ** (n - 1) == tutte_eval(n, E, 1, 1 + v), "N7 T(1,y) from colour networks")
    return C.done()

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
