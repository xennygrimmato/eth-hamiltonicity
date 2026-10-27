"""Shared exact-integer library for the proof checks of research/exact-hc-theorem.md.

Everything here follows the definitions of exact-hc-theorem.md literally (Sections 2-5):
  * an exterior (Grassmann) algebra over Z with an arbitrary (randomisable) order of generators;
  * the edge pieces (alpha_l, beta_l), labels L = {N,0,1,2,3};
  * the sign eps(l), the local signs sigma_a and the interleaving form;
  * the network of Section 5: settings as fixed-length bit strings, W_a, Psi_ab, c_ab, f_ab.
No floating point is used anywhere.
"""
import itertools
import random
from math import comb

# ----------------------------------------------------------------------------------------------
# exterior algebra over Z.  An element is a dict {bitmask: nonzero int}; bit p <-> generator p,
# and the basis monomial of a set S is the product of its generators in increasing p.
# ----------------------------------------------------------------------------------------------

def mono_mul(m1, m2):
    """(basis(m1) * basis(m2)) = sign * basis(m1|m2), or 0 if they share a generator."""
    if m1 & m2:
        return None, 0
    s = 0
    x = m2
    while x:
        q = (x & -x).bit_length() - 1
        x &= x - 1
        s += bin(m1 >> (q + 1)).count("1")  # generators of m1 above q must pass q
    return m1 | m2, -1 if s & 1 else 1


def gmul(A, B):
    out = {}
    for m1, c1 in A.items():
        for m2, c2 in B.items():
            m, s = mono_mul(m1, m2)
            if m is None:
                continue
            out[m] = out.get(m, 0) + s * c1 * c2
    return {m: c for m, c in out.items() if c}


def gadd(A, B, cb=1):
    out = dict(A)
    for m, c in B.items():
        out[m] = out.get(m, 0) + cb * c
    return {m: c for m, c in out.items() if c}


def gscale(A, c):
    return {m: c * v for m, v in A.items() if c * v}


def gprod(seq):
    P = {0: 1}
    for x in seq:
        P = gmul(P, x)
        if not P:
            return {}
    return P


ONE = {0: 1}
ZERO = {}


def word(gens):
    """the element gens[0]*gens[1]*...*gens[-1] (generator indices), as a signed basis monomial."""
    P = ONE
    for p in gens:
        P = gmul(P, {1 << p: 1})
    return P


def parity_of(A):
    """0/1 if A is homogeneous even/odd, None if mixed; zero counts as homogeneous (returns 0)."""
    ps = {bin(m).count("1") & 1 for m in A}
    if len(ps) > 1:
        return None
    return ps.pop() if ps else 0


# ----------------------------------------------------------------------------------------------
# graphs
# ----------------------------------------------------------------------------------------------

def hc_count(n, edges):
    """number of Hamiltonian cycles of a simple graph (n >= 3), by DFS from vertex 0."""
    if n < 3:
        return 0
    adj = [[] for _ in range(n)]
    for i, j in edges:
        adj[i].append(j); adj[j].append(i)
    cnt = 0
    def dfs(v, seen, depth):
        nonlocal cnt
        if depth == n:
            if 0 in adj[v]:
                cnt += 1
            return
        for w in adj[v]:
            if not (seen >> w) & 1:
                dfs(w, seen | (1 << w), depth + 1)
    dfs(0, 1, 1)
    return cnt // 2


def two_factors(n, edges):
    """all 2-factors, as sorted tuples of edge indices."""
    m = len(edges)
    deg = [0] * n
    out = []
    # remaining degree available, for pruning
    rem = [0] * n
    for i, j in edges:
        rem[i] += 1; rem[j] += 1
    def rec(k, chosen):
        if k == m:
            if all(d == 2 for d in deg):
                out.append(tuple(chosen))
            return
        i, j = edges[k]
        rem[i] -= 1; rem[j] -= 1
        if deg[i] + rem[i] >= 2 and deg[j] + rem[j] >= 2:
            rec(k + 1, chosen)
        if deg[i] < 2 and deg[j] < 2:
            deg[i] += 1; deg[j] += 1; chosen.append(k)
            rec(k + 1, chosen)
            chosen.pop(); deg[i] -= 1; deg[j] -= 1
        rem[i] += 1; rem[j] += 1
    rec(0, [])
    return out


def det_bareiss(M):
    M = [list(r) for r in M]
    N = len(M)
    if N == 0:
        return 1
    sign, prev = 1, 1
    for k in range(N - 1):
        if M[k][k] == 0:
            for r in range(k + 1, N):
                if M[r][k] != 0:
                    M[k], M[r] = M[r], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, N):
            for j in range(k + 1, N):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[N - 1][N - 1]


def reduced_laplacian(n, edge_list, r):
    L = [[0] * n for _ in range(n)]
    for i, j in edge_list:
        L[i][i] += 1; L[j][j] += 1; L[i][j] -= 1; L[j][i] -= 1
    keep = [v for v in range(n) if v != r]
    return [[L[u][v] for v in keep] for u in keep]


def is_spanning_tree(n, edge_list):
    if len(edge_list) != n - 1:
        return False
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i, j in edge_list:
        a, b = find(i), find(j)
        if a == b:
            return False
        parent[a] = b
    return True


def count_spanning_trees_brute(n, edge_list):
    return sum(1 for F in itertools.combinations(edge_list, n - 1) if is_spanning_tree(n, F))


def random_graph(n, m, rng, min_deg2=False):
    allp = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for _ in range(1000):
        E = sorted(rng.sample(allp, min(m, len(allp))))
        if not min_deg2:
            return E
        deg = [0] * n
        for i, j in E:
            deg[i] += 1; deg[j] += 1
        if min(deg) >= 2:
            return E
    return E


def planted_graph(sizes, p_in, n_cross, rng, plant_hc=False, border=None):
    """blobs of the given sizes, each blob a random graph with edge prob p_in plus a Hamiltonian
    path inside it; then n_cross random crossing edges.  Returns n, edges, blob(list)."""
    blob = []
    for a, s in enumerate(sizes):
        blob += [a] * s
    n = len(blob)
    perm = list(range(n)); rng.shuffle(perm)
    blob = [blob[perm[v]] for v in range(n)]
    if plant_hc and border is not None:
        border = list(border)
    E = set()
    for a in range(len(sizes)):
        vs = [v for v in range(n) if blob[v] == a]
        rng.shuffle(vs)
        for x, y in zip(vs, vs[1:]):
            E.add((min(x, y), max(x, y)))
        for x, y in itertools.combinations(vs, 2):
            if rng.random() < p_in:
                E.add((min(x, y), max(x, y)))
    if plant_hc:
        # a Hamiltonian cycle that visits the blobs contiguously, in a random cyclic blob order
        if border is None:
            border = list(range(len(sizes))); rng.shuffle(border)
        seq = []
        for a in border:
            vs = [v for v in range(n) if blob[v] == a]
            rng.shuffle(vs)
            seq += vs
        for x, y in zip(seq, seq[1:] + seq[:1]):
            if x != y:
                E.add((min(x, y), max(x, y)))
    cross = [(i, j) for i in range(n) for j in range(i + 1, n) if blob[i] != blob[j]]
    for e in rng.sample(cross, min(n_cross, len(cross))):
        E.add(e)
    return n, sorted(E), blob


# ----------------------------------------------------------------------------------------------
# the Berezin form of tau, Section 2
# ----------------------------------------------------------------------------------------------

class Gens:
    """generator indices: psibar_v, psi_v for v != r, in a (possibly random) total order."""
    def __init__(self, n, r, rng=None):
        self.n, self.r = n, r
        names = [(t, v) for v in range(n) if v != r for t in ("bar", "psi")]
        if rng is not None:
            rng.shuffle(names)
        self.idx = {nm: p for p, nm in enumerate(names)}

    def pb(self, v):
        return ZERO if v == self.r else {1 << self.idx[("bar", v)]: 1}

    def ps(self, v):
        return ZERO if v == self.r else {1 << self.idx[("psi", v)]: 1}

    def omega(self, vertices):
        """Omega_S = prod_{v in S \\ r} (psibar_v psi_v) as an element (order irrelevant)."""
        return gprod([gmul(self.pb(v), self.ps(v)) for v in sorted(vertices) if v != self.r])

    def top(self, A, vertices):
        """[Omega_S](A): coefficient of Omega_S in A (A in the subalgebra of S's generators)."""
        Om = self.omega(vertices)
        (m, s), = Om.items()
        return A.get(m, 0) * s

    def q(self, i, j):
        return gmul(gadd(self.pb(i), self.pb(j), -1), gadd(self.ps(i), self.ps(j), -1))

    def one_plus_q(self, i, j):
        return gadd(ONE, self.q(i, j))


# ----------------------------------------------------------------------------------------------
# pieces, labels and signs, Sections 3-4
# ----------------------------------------------------------------------------------------------
LABELS = ("N", 0, 1, 2, 3)
ODD = {2, 3}


def pi_(l):
    return 1 if l in ODD else 0


def pieces(Gn, s, t, l):
    """(alpha, beta) of label l on the crossing edge with low end s and high end t."""
    if l == "N":
        return ONE, ONE
    if l == 0:
        return ONE, gadd(ONE, gmul(Gn.pb(t), Gn.ps(t)))
    if l == 1:
        return gmul(Gn.pb(s), Gn.ps(s)), ONE
    if l == 2:
        return Gn.pb(s), gscale(Gn.ps(t), -1)
    if l == 3:
        return Gn.ps(s), Gn.pb(t)
    raise ValueError(l)


def c_kl(ak, bk, al, bl):
    return sum(1 for x in (ak, bk) for y in (al, bl) if y < x)


def interleave(a, b, c, d):
    """chords {a<b},{c<d} on four distinct points of a line interleave."""
    return int(a < c < b < d or c < a < d < b)


# ----------------------------------------------------------------------------------------------
# the instance: graph, partition, root, order of crossing edges
# ----------------------------------------------------------------------------------------------

class Instance:
    def __init__(self, n, edges, blob, r, g=None, rng=None, gen_rng=None):
        self.n, self.edges, self.blob, self.r = n, list(edges), list(blob), r
        self.g = g if g is not None else max(blob) + 1
        self.Gn = Gens(n, r, gen_rng)
        cross = []
        self.internal = {a: [] for a in range(self.g)}
        for (u, v) in self.edges:
            if blob[u] == blob[v]:
                self.internal[blob[u]].append((u, v))
            else:
                s, t = (u, v) if blob[u] < blob[v] else (v, u)
                cross.append((s, t))
        if rng is not None:
            rng.shuffle(cross)          # an arbitrary total order of the crossing edges
        self.cross = cross              # e_1 < e_2 < ... in this list order
        self.m = len(cross)
        self.ak = [blob[s] for s, t in cross]
        self.bk = [blob[t] for s, t in cross]
        self.delta = {a: [k for k in range(self.m) if self.ak[k] == a or self.bk[k] == a]
                      for a in range(self.g)}
        self.Eab = {}
        for a in range(self.g):
            for b in range(a + 1, self.g):
                self.Eab[(a, b)] = [k for k in range(self.m) if (self.ak[k], self.bk[k]) == (a, b)]
        self.V = {a: [v for v in range(n) if blob[v] == a] for a in range(self.g)}

    # ------------------------------------------------------------------ global sign objects
    def eps(self, lab):
        tot = 0
        for k in range(self.m):
            if not pi_(lab[k]):
                continue
            for l in range(k + 1, self.m):
                if pi_(lab[l]):
                    tot += c_kl(self.ak[k], self.bk[k], self.ak[l], self.bk[l])
        return -1 if tot & 1 else 1

    def sigma(self, a, lab_at):
        """local sign of blob a; lab_at: dict k -> label for k in delta(a)."""
        tot = 0
        ks = self.delta[a]
        for x, k in enumerate(ks):
            if not pi_(lab_at[k]):
                continue
            for l in ks[x + 1:]:
                if not pi_(lab_at[l]):
                    continue
                shared = {self.ak[k], self.bk[k]} & {self.ak[l], self.bk[l]}
                if min(shared) == a:
                    tot += c_kl(self.ak[k], self.bk[k], self.ak[l], self.bk[l])
        return -1 if tot & 1 else 1

    def P(self, a, b, lab_at):
        a, b = min(a, b), max(a, b)
        return sum(pi_(lab_at[k]) for k in self.Eab[(a, b)]) & 1

    def Gamma(self, a, lab_at):
        """ordered product of blob a's pieces, crossing edges in increasing order."""
        seq = []
        for k in self.delta[a]:
            s, t = self.cross[k]
            al, be = pieces(self.Gn, s, t, lab_at[k])
            seq.append(al if self.ak[k] == a else be)
        return gprod(seq)

    # ------------------------------------------------------------------ the blob sum I_a
    def internal_choices(self, a):
        """list of (x as tuple of internal edges chosen, degree vector on V_a, F_x)."""
        if not hasattr(self, "_ic"):
            self._ic = {}
        if a in self._ic:
            return self._ic[a]
        ints = self.internal[a]
        out = []
        for xs in itertools.product((0, 1), repeat=len(ints)):
            dg = {v: 0 for v in self.V[a]}
            ok = True
            for x, (u, v) in zip(xs, ints):
                if x:
                    dg[u] += 1; dg[v] += 1
            if any(d > 2 for d in dg.values()):
                continue
            F = gprod([self.Gn.one_plus_q(u, v) for x, (u, v) in zip(xs, ints) if x])
            out.append((xs, dg, F))
        self._ic[a] = out
        return out

    def I(self, a, lab_at):
        dl = {v: 0 for v in self.V[a]}
        for k in self.delta[a]:
            if lab_at[k] != "N":
                s, t = self.cross[k]
                dl[s if self.ak[k] == a else t] += 1
        if any(d > 2 for d in dl.values()):
            return 0
        Gam = self.Gamma(a, lab_at)
        if not Gam:
            return 0
        tot = 0
        for xs, dg, F in self.internal_choices(a):
            if all(dg[v] + dl[v] == 2 for v in self.V[a]):
                tot += self.Gn.top(gmul(F, Gam), self.V[a])
        return tot


# ----------------------------------------------------------------------------------------------
# the network of Section 5 (settings are tuples of bits of fixed length P_a)
# ----------------------------------------------------------------------------------------------
KAPPA = {"N": 0, 0: 1, 1: 2, 2: 3, 3: 4}
KAPPA_INV = {v: k for k, v in KAPPA.items()}


def width5(e):
    """smallest w with 2^w >= 5^e."""
    w = 0
    while (1 << w) < 5 ** e:
        w += 1
    return w


def to_bits(x, w):
    return tuple((x >> i) & 1 for i in range(w))


def from_bits(bits):
    return sum(b << i for i, b in enumerate(bits))


class HCNetwork:
    def __init__(self, inst, sign_mode="full"):
        """sign_mode: 'full' (the construction), 'nointerleave', 'nolocal', 'none' (ablations)."""
        self.inst = inst
        self.g = g = inst.g
        self.sign_mode = sign_mode
        self.e = {}
        self.w = {}
        for a in range(g):
            for b in range(g):
                if a != b:
                    key = (min(a, b), max(a, b))
                    self.e[(a, b)] = len(inst.Eab[key])
                    self.w[(a, b)] = width5(self.e[(a, b)])
        self.Q = {a: [(c, d) for c in range(a + 1, g) for d in range(c + 1, g)] for a in range(g)}
        # layout of node a: blocks for b != a in increasing b, then |Q_a| copy bits
        self.layout = {}
        for a in range(g):
            pos = 0
            lay = {}
            for b in range(g):
                if b != a:
                    lay[b] = (pos, self.w[(a, b)])
                    pos += self.w[(a, b)]
            lay["Q"] = (pos, len(self.Q[a]))
            pos += len(self.Q[a])
            self.layout[a] = lay
        self.Plen = {a: sum(w for (p, w) in self.layout[a].values()) for a in range(g)}
        self.c = {}
        for a in range(g):
            for b in range(g):
                if a != b:
                    self.c[(a, b)] = self.w[(a, b)] + (g - 1 - max(a, b))
        self._Wcache = {}

    # ---- encoding
    def encode(self, a, lab_at, y):
        bits = [0] * self.Plen[a]
        for b in range(self.g):
            if b == a:
                continue
            p, w = self.layout[a][b]
            ks = self.inst.Eab[(min(a, b), max(a, b))]
            val = sum(KAPPA[lab_at[k]] * 5 ** t for t, k in enumerate(ks))
            bits[p:p + w] = to_bits(val, w)
        p, w = self.layout[a]["Q"]
        bits[p:p + w] = [y[cd] for cd in self.Q[a]]
        return tuple(bits)

    def decode(self, a, z):
        """returns (lab_at, y) or None if z is not in S_a."""
        if len(z) != self.Plen[a]:
            return None
        lab_at = {}
        for b in range(self.g):
            if b == a:
                continue
            p, w = self.layout[a][b]
            val = from_bits(z[p:p + w])
            ks = self.inst.Eab[(min(a, b), max(a, b))]
            if val >= 5 ** len(ks):
                return None
            for k in ks:
                lab_at[k] = KAPPA_INV[val % 5]
                val //= 5
        p, w = self.layout[a]["Q"]
        y = {cd: z[p + i] for i, cd in enumerate(self.Q[a])}
        return lab_at, y

    def settings(self, a):
        ks = self.inst.delta[a]
        for labs in itertools.product(LABELS, repeat=len(ks)):
            lab_at = dict(zip(ks, labs))
            for ys in itertools.product((0, 1), repeat=len(self.Q[a])):
                yield self.encode(a, lab_at, dict(zip(self.Q[a], ys)))

    def in_S(self, a, z):
        return self.decode(a, z) is not None

    # ---- node functions
    def chi(self, a, lab_at, y):
        tot = 0
        for (c, d) in self.Q[a]:
            if y[(c, d)]:
                tot += sum(self.inst.P(a, b, lab_at) for b in range(c + 1, d))
        return -1 if tot & 1 else 1

    def W(self, a, z):
        if (a, z) in self._Wcache:
            return self._Wcache[(a, z)]
        lab_at, y = self.decode(a, z)
        val = self.inst.I(a, lab_at)
        if val:
            if self.sign_mode in ("full", "nointerleave"):
                val *= self.inst.sigma(a, lab_at)
            if self.sign_mode in ("full", "nolocal"):
                val *= self.chi(a, lab_at, y)
        self._Wcache[(a, z)] = val
        return val

    # ---- edges
    def proj(self, a, b, z):
        """pi_{ab}(z_a): the c_ab-bit string that node a puts on the pair {a,b}."""
        lab_at, y = self.decode(a, z)
        p, w = self.layout[a][b]
        out = list(z[p:p + w])
        if a < b:
            out += [y[(b, d)] for d in range(b + 1, self.g)]
        else:  # a is the larger end: it sends its own parities P_{a d}, d > a
            out += [self.inst.P(a, d, lab_at) for d in range(a + 1, self.g)]
        return tuple(out)

    def f(self, a, b, z, theta):
        return 1 if self.proj(a, b, z) == tuple(theta) else 0

    def Psi(self, a, b, za, zb):
        if a > b:
            return self.Psi(b, a, zb, za)
        la, ya = self.decode(a, za)
        lb, yb = self.decode(b, zb)
        for k in self.inst.Eab[(a, b)]:
            if la[k] != lb[k]:
                return 0
        for d in range(b + 1, self.g):
            if ya[(b, d)] != self.inst.P(b, d, lb):
                return 0
        return 1

    # ---- parameters of Definition 2
    def U(self):
        return sum(self.c.values())

    def mu(self):
        deg = [0] * self.inst.n
        for i, j in self.inst.edges:
            deg[i] += 1; deg[j] += 1
        return max(sum(deg[v] for v in self.inst.V[a]) for a in range(self.g))

    def P_param(self):
        # P = ceil(log2(5) * mu) + g + g^2, computed exactly: smallest P0 with 2^P0 >= 5^mu
        return width5(self.mu()) + self.g + self.g ** 2


# ----------------------------------------------------------------------------------------------
# network evaluation, generic (uses only S_a, W_a, Psi_ab / f_ab as black boxes)
# ----------------------------------------------------------------------------------------------

def eval_network_brute(net):
    """Z = sum over all z in prod S_a of prod W_a prod_{a<b} Psi_ab, enumerated node by node; a
    partial product that is already 0 is not extended (exact)."""
    g = net.g
    S = [list(net.settings(a)) for a in range(g)]
    Wt = [{z: net.W(a, z) for z in S[a]} for a in range(g)]
    S = [[z for z in S[a] if Wt[a][z] != 0] for a in range(g)]  # terms with W_a = 0 vanish
    total = 0
    def rec(a, chosen, prod):
        nonlocal total
        if a == g:
            total += prod
            return
        for z in S[a]:
            p = prod * Wt[a][z]
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


def eval_network_grouped(net, groups):
    """Lemma 1 / Lemma 8 construction with the given grouping (list of lists of nodes): the
    tables W~_gamma(Theta) of the clique, then the clique value.  Uses only W, Psi, f; the inner
    sums over theta use that each f_{ab}(z_a, .) is supported on the single string proj(z_a)
    (checked separately: f(z, theta) = [proj(z) = theta])."""
    g = net.g
    gid = {}
    for gi, G in enumerate(groups):
        for a in G:
            gid[a] = gi
    S = [list(net.settings(a)) for a in range(g)]
    tables = []
    for gi, G in enumerate(groups):
        T = {}
        for zs in itertools.product(*[S[a] for a in G]):
            val = 1
            for a, z in zip(G, zs):
                val *= net.W(a, z)
                if not val:
                    break
            if not val:
                continue
            for x in range(len(G)):
                for y in range(x + 1, len(G)):
                    val *= net.Psi(G[x], G[y], zs[x], zs[y])
            if not val:
                continue
            key = []
            for a, z in zip(G, zs):
                for b in range(g):
                    if gid[b] != gi:
                        key.append(((min(a, b), max(a, b)), net.proj(a, b, z)))
            key = tuple(sorted(key))
            T[key] = T.get(key, 0) + val
        tables.append(T)
    # clique value: sum over one string per pair {a,b} across groups; join tables on shared keys
    def merge(T1, T2):
        out = {}
        for k1, v1 in T1.items():
            d1 = dict(k1)
            for k2, v2 in T2.items():
                d2 = dict(k2)
                if all(d1[p] == d2[p] for p in d1.keys() & d2.keys()):
                    k = tuple(sorted({**d1, **d2}.items()))
                    out[k] = out.get(k, 0) + v1 * v2
        return out
    acc = tables[0]
    for T in tables[1:]:
        acc = merge(acc, T)
    return sum(acc.values())
