"""Exact-arithmetic library for the Tutte-plane study (research/tutte-plane.md).

Graphs are (n, E) with vertices 0..n-1 and E a list of pairs (multigraphs and loops allowed
where stated).  Everything is int / Fraction; no floating point.

Contents
  * union-find, components, rank r(A) = n - k(A)
  * rank generating polynomial R(u,v) = sum_A u^{r(E)-r(A)} v^{|A|-r(A)}  (so T(x,y) = R(x-1,y-1))
  * Tutte polynomial by deletion-contraction (independent check), as {(i,j): coeff} in x^i y^j
  * FK / Potts polynomial Z(q,v) = sum_A q^{k(A)} v^{|A|} as {(i,j): coeff} in q^i v^j
  * q-colouring sum, F_q-flow sum (q prime, and q = 4 via GF(4))
  * set partitions of [b], join, refinement, Mobius function
  * exact rank over Q (Fraction Gaussian elimination) and over F_p
"""
from fractions import Fraction
import itertools, random

# ------------------------------------------------------------------ basic graph tools
def find(p, x):
    while p[x] != x:
        p[x] = p[p[x]]
        x = p[x]
    return x

def ncomp(n, A):
    p = list(range(n)); k = n
    for (a, b) in A:
        ra, rb = find(p, a), find(p, b)
        if ra != rb:
            p[ra] = rb; k -= 1
    return k

def comp_labels(n, A):
    p = list(range(n))
    for (a, b) in A:
        ra, rb = find(p, a), find(p, b)
        if ra != rb:
            p[ra] = rb
    return [find(p, x) for x in range(n)]

def subsets(E):
    m = len(E)
    for mask in range(1 << m):
        yield mask, [E[i] for i in range(m) if mask >> i & 1]

# ------------------------------------------------------------------ polynomials as dicts
def padd(P, Q, c=1):
    R = dict(P)
    for k, v in Q.items():
        R[k] = R.get(k, 0) + c * v
    return {k: v for k, v in R.items() if v}

def peval2(P, a, b):
    return sum(c * Fraction(a) ** i * Fraction(b) ** j for (i, j), c in P.items())

def rank_gen(n, E):
    """R(u,v) = sum_A u^{r(E)-r(A)} v^{|A|-r(A)}; T(x,y) = R(x-1, y-1)."""
    rE = n - ncomp(n, E)
    R = {}
    for _, A in subsets(E):
        rA = n - ncomp(n, A)
        key = (rE - rA, len(A) - rA)
        R[key] = R.get(key, 0) + 1
    return R

def shift(P, s, t):
    """P(u,v) -> P(x+s, y+t) expanded, as {(i,j)}."""
    from math import comb
    out = {}
    for (i, j), c in P.items():
        for a in range(i + 1):
            for b in range(j + 1):
                key = (a, b)
                out[key] = out.get(key, 0) + c * comb(i, a) * s ** (i - a) * comb(j, b) * t ** (j - b)
    return {k: v for k, v in out.items() if v}

def tutte_subset(n, E):
    return shift(rank_gen(n, E), -1, -1)

def tutte_dc(n, E):
    """Deletion-contraction on multigraphs with loops; returns {(i,j): coeff}."""
    E = list(E)
    # find a non-loop edge
    for idx, (a, b) in enumerate(E):
        if a != b:
            break
    else:
        return {(0, len(E)): 1}            # only loops: y^{#loops}
    rest = E[:idx] + E[idx + 1:]
    a, b = E[idx]
    # contraction: merge b into a
    con = [(a if u == b else u, a if w == b else w) for (u, w) in rest]
    # bridge?
    if ncomp(n, rest) > ncomp(n, E):
        return {(i + 1, j): c for (i, j), c in tutte_dc(n, con).items()}
    return padd(tutte_dc(n, rest), tutte_dc(n, con))

def tutte_eval(n, E, x, y):
    return peval2(rank_gen(n, E), Fraction(x) - 1, Fraction(y) - 1)

def potts(n, E):
    """Z(q,v) = sum_A q^{k(A)} v^{|A|} as {(i,j)} in q^i v^j."""
    Z = {}
    for _, A in subsets(E):
        key = (ncomp(n, A), len(A))
        Z[key] = Z.get(key, 0) + 1
    return Z

def potts_eval(n, E, q, v):
    return peval2(potts(n, E), q, v)

def colour_sum(n, E, q, v):
    """sum_{c:V->[q]} prod_{uv in E} (1 + v [c_u = c_v])."""
    tot = 0
    for c in itertools.product(range(q), repeat=n):
        w = 1
        for (a, b) in E:
            if c[a] == c[b]:
                w *= (1 + v)
        tot += w
    return tot

# GF(4) = {0,1,w,w^2} encoded 0..3 with addition = xor (char 2), so flows only need addition.
def flow_count(n, E, q):
    """#{f: E -> F_q with conservation}, F_q = Z/q (q prime) or GF(4) (q = 4, additive group Z2^2).
    Orientation: edge (a,b) carries +f out of a, into b."""
    m = len(E)
    if q == 4:
        add = lambda s, t: s ^ t; neg = lambda s: s
    else:
        add = lambda s, t: (s + t) % q; neg = lambda s: (-s) % q
    cnt = 0
    for f in itertools.product(range(q), repeat=m):
        bal = [0] * n
        for (a, b), fe in zip(E, f):
            bal[a] = add(bal[a], fe); bal[b] = add(bal[b], neg(fe))
        if all(x == 0 for x in bal):
            cnt += 1
    return cnt

def flow_sum(n, E, q, v):
    """sum_{F_q-flows f} (q+v)^{#zero edges} v^{#nonzero edges}  ( = q^{m-n} Z(q,v) )."""
    m = len(E)
    if q == 4:
        add = lambda s, t: s ^ t; neg = lambda s: s
    else:
        add = lambda s, t: (s + t) % q; neg = lambda s: (-s) % q
    tot = 0
    for f in itertools.product(range(q), repeat=m):
        bal = [0] * n
        for (a, b), fe in zip(E, f):
            bal[a] = add(bal[a], fe); bal[b] = add(bal[b], neg(fe))
        if all(x == 0 for x in bal):
            z = sum(1 for fe in f if fe == 0)
            tot += (q + v) ** z * v ** (m - z)
    return tot

# ------------------------------------------------------------------ random graphs
def rand_graph(n, m, rng, simple=True):
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    if simple:
        m = min(m, len(pairs))
        return rng.sample(pairs, m)
    return [rng.choice(pairs) for _ in range(m)]

def rand_bounded_degree(n, m, D, rng, tries=200):
    for _ in range(tries):
        deg = [0] * n; E = set()
        pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
        rng.shuffle(pairs)
        for (a, b) in pairs:
            if len(E) >= m:
                break
            if deg[a] < D and deg[b] < D:
                E.add((a, b)); deg[a] += 1; deg[b] += 1
        if len(E) == m:
            return sorted(E)
    return sorted(E)

# ------------------------------------------------------------------ set partitions
def set_partitions(b):
    """All set partitions of range(b) as canonical tuples of block labels (restricted growth)."""
    out = []
    def rec(i, cur, mx):
        if i == b:
            out.append(tuple(cur)); return
        for c in range(mx + 2):
            cur.append(c); rec(i + 1, cur, max(mx, c)); cur.pop()
    rec(0, [], -1)
    return out

def canon(lab):
    mp = {}; out = []
    for x in lab:
        if x not in mp:
            mp[x] = len(mp)
        out.append(mp[x])
    return tuple(out)

def nblocks(P):
    return len(set(P))

def join(P, Q):
    b = len(P); p = list(range(b))
    for X in (P, Q):
        first = {}
        for i, c in enumerate(X):
            if c in first:
                ra, rb = find(p, i), find(p, first[c])
                if ra != rb:
                    p[ra] = rb
            else:
                first[c] = i
    return canon([find(p, i) for i in range(b)])

def refines(P, S):
    """P <= S (every block of P inside a block of S)."""
    m = {}
    for a, s in zip(P, S):
        if a in m and m[a] != s:
            return False
        m[a] = s
    return True

def blocks(P):
    d = {}
    for i, c in enumerate(P):
        d.setdefault(c, []).append(i)
    return list(d.values())

# ------------------------------------------------------------------ exact ranks
def rank_Q(M):
    A = [[Fraction(x) for x in row] for row in M]
    if not A:
        return 0
    rows, cols = len(A), len(A[0]); r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i][c] != 0:
                piv = i; break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = 1 / A[r][c]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                f = A[i][c] * inv
                A[i] = [a - f * bb for a, bb in zip(A[i], A[r])]
        r += 1
        if r == rows:
            break
    return r

def rank_p(M, p):
    A = [[int(x) % p for x in row] for row in M]
    if not A:
        return 0
    rows, cols = len(A), len(A[0]); r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i][c]:
                piv = i; break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [(a * inv) % p for a in A[r]]
        for i in range(rows):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [(a - f * bb) % p for a, bb in zip(A[i], A[r])]
        r += 1
        if r == rows:
            break
    return r

def bell(b):
    return len(set_partitions(b))

def stirling2(b, j):
    from math import comb, factorial
    return sum((-1) ** (j - i) * comb(j, i) * i ** b for i in range(j + 1)) // factorial(j)

class Checker:
    def __init__(self, name):
        self.name = name; self.ok = 0; self.bad = 0
    def check(self, cond, msg):
        if cond:
            self.ok += 1
        else:
            self.bad += 1; print("  FAIL:", msg)
    def done(self):
        print(f"{self.name}: {self.ok} checks, {self.bad} failures -> {'PASS' if self.bad == 0 else 'FAIL'}")
        return self.bad == 0
