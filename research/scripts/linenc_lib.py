"""Library for the linear-encoding experiments (research/linear-encoding.md).

Singleton blobs (g = n, beta = position).  Exact integer arithmetic only; the exterior algebra is
proof_lib's (dict monomial -> int, randomisable generator order).

A *labelling* assigns to every edge e = {i, j} one of
    'N'            unused
    'one'          used, monomial 1
    ('D', i)       used, monomial  psibar_i psi_i
    ('A', i, j)    used, monomial -psibar_i psi_j     (an arc i -> j; "mixed")
These are the six states of 1 + q_e = 1 + D_i + D_j + A_ij + A_ji plus 'unused'.  A labelling is
*valid* if every vertex has exactly two used edges, every v != r receives exactly one psibar_v and
one psi_v, and no monomial mentions the root r (those monomials are 0).
"""
import itertools
import random
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from proof_lib import (gmul, gprod, gscale, ONE, ZERO, Gens, hc_count, random_graph, pieces,
                       c_kl)  # noqa: E402


# ------------------------------------------------------------------------------------------------
# labellings
# ------------------------------------------------------------------------------------------------

def edge_states(i, j, r):
    st = ['N', 'one']
    for a, b in ((i, j), (j, i)):
        if a != r:
            st.append(('D', a))
    if i != r and j != r:
        st += [('A', i, j), ('A', j, i)]
    return st


def gives(state):
    """(set of vertices receiving psibar, set receiving psi) from this edge state."""
    if state in ('N', 'one'):
        return (), ()
    if state[0] == 'D':
        return (state[1],), (state[1],)
    return (state[1],), (state[2],)


def valid_labellings(n, edges, r):
    m = len(edges)
    deg = [0] * n
    nb = [0] * n
    np_ = [0] * n
    rem = [0] * n
    for i, j in edges:
        rem[i] += 1; rem[j] += 1
    lab = [None] * m
    out = []

    def rec(k):
        if k == m:
            if all(d == 2 for d in deg) and all((nb[v], np_[v]) == ((0, 0) if v == r else (1, 1))
                                                for v in range(n)):
                out.append(tuple(lab))
            return
        i, j = edges[k]
        rem[i] -= 1; rem[j] -= 1
        for s in edge_states(i, j, r):
            used = s != 'N'
            if used and (deg[i] == 2 or deg[j] == 2):
                continue
            if not used and (deg[i] + rem[i] < 2 or deg[j] + rem[j] < 2):
                continue
            B, P = gives(s)
            if any(nb[v] for v in B) or any(np_[v] for v in P):
                continue
            if used:
                deg[i] += 1; deg[j] += 1
            for v in B: nb[v] += 1
            for v in P: np_[v] += 1
            lab[k] = s
            rec(k + 1)
            if used:
                deg[i] -= 1; deg[j] -= 1
            for v in B: nb[v] -= 1
            for v in P: np_[v] -= 1
        rem[i] += 1; rem[j] += 1
    rec(0)
    return out


def monomial(Gn, s):
    if s in ('N', 'one'):
        return ONE
    if s[0] == 'D':
        return gmul(Gn.pb(s[1]), Gn.ps(s[1]))
    return gscale(gmul(Gn.pb(s[1]), Gn.ps(s[2])), -1)


def koszul_sign(Gn, n, lab):
    """[Omega_V] of the product of the selected monomials, by the exterior algebra."""
    return Gn.top(gprod([monomial(Gn, s) for s in lab if s != 'N']), range(n))


# ------------------------------------------------------------------------------------------------
# combinatorial data of a labelling
# ------------------------------------------------------------------------------------------------

def arcs(lab):
    return [(s[1], s[2]) for s in lab if s not in ('N', 'one') and s[0] == 'A']


def mixed_edges(edges, lab):
    return [k for k, s in enumerate(lab) if s not in ('N', 'one') and s[0] == 'A']


def n_cycles(arc_list):
    succ = dict(arc_list)
    seen, c = set(), 0
    for v in succ:
        if v in seen:
            continue
        c += 1
        w = v
        while w not in seen:
            seen.add(w); w = succ[w]
    return c


def interleave_pos(pa, pb, pc, pd):
    a, b = sorted((pa, pb)); c, d = sorted((pc, pd))
    return int(a < c < b < d or c < a < d < b)


def cross_parity_brute(edges, pos, xs):
    """number (mod 2) of unordered pairs of active chords with 4 distinct ends that interleave."""
    act = [edges[k] for k in range(len(edges)) if xs[k]]
    t = 0
    for (i, j), (k, l) in itertools.combinations(act, 2):
        if len({i, j, k, l}) == 4:
            t += interleave_pos(pos[i], pos[j], pos[k], pos[l])
    return t & 1


def rot_local(pos, u, v, w):
    """c_v mod 2 for the turn u -> v -> w of an inscribed polygon (vertices in convex position)."""
    pu, pv, pw = pos[u], pos[v], pos[w]
    return int(pu < pw < pv or pv < pw < pu)


def rot_sum(pos, arc_list):
    pred = {b: a for a, b in arc_list}
    succ = dict(arc_list)
    return sum(rot_local(pos, pred[v], v, succ[v]) for v in succ) & 1


# ------------------------------------------------------------------------------------------------
# the paper's sign rule at singleton blobs (Prop. sign rule / sign factorisation, label 0 split)
# ------------------------------------------------------------------------------------------------

def paper_pieces(Gn, s, t, state):
    """pieces (alpha at low end s, beta at high end t) of a state, low/high by position."""
    if state == 'N' or state == 'one':
        return ONE, ONE
    if state[0] == 'D':
        if state[1] == t:
            return ONE, gmul(Gn.pb(t), Gn.ps(t))     # half of the paper's label 0
        return gmul(Gn.pb(s), Gn.ps(s)), ONE          # label 1
    if (state[1], state[2]) == (s, t):
        return Gn.pb(s), gscale(Gn.ps(t), -1)         # label 2: -psibar_s psi_t
    return Gn.ps(s), Gn.pb(t)                         # label 3: -psibar_t psi_s = psi_s psibar_t


def paper_sign(Gn, n, edges, pos, order, lab):
    """eps(eta) * prod_v [omega_v](R_v), eps = prod_v sigma_v * (-1)^{sum_{a<c<b<d} P_ab P_cd}.

    `order` is the crossing order (a permutation of edge indices).  With singleton blobs the
    blob of v is pos[v]."""
    ends = []
    for k in order:
        i, j = edges[k]
        s, t = (i, j) if pos[i] < pos[j] else (j, i)
        ends.append((k, s, t))
    par = {}
    R = {v: [] for v in range(n)}
    for k, s, t in ends:
        al, be = paper_pieces(Gn, s, t, lab[k])
        R[s].append(al); R[t].append(be)
        par[k] = 1 if (lab[k] not in ('N', 'one') and lab[k][0] == 'A') else 0
    top = 1
    for v in range(n):
        top *= Gn.top(gprod(R[v]), [v])
        if top == 0:
            return 0
    # sigma_v: pairs (k<l in crossing order) whose chords meet, charged to the min shared blob
    sig = 0
    for x in range(len(ends)):
        k, s, t = ends[x]
        if not par[k]:
            continue
        for y in range(x + 1, len(ends)):
            l, s2, t2 = ends[y]
            if not par[l]:
                continue
            if {s, t} & {s2, t2}:
                sig += c_kl(pos[s], pos[t], pos[s2], pos[t2])
    # interleaving term over disjoint chords
    cr = 0
    for x in range(len(ends)):
        k, s, t = ends[x]
        for y in range(x + 1, len(ends)):
            l, s2, t2 = ends[y]
            if par[k] and par[l] and not ({s, t} & {s2, t2}):
                cr += interleave_pos(pos[s], pos[t], pos[s2], pos[t2])
    return top * (-1 if (sig + cr) & 1 else 1)


# ------------------------------------------------------------------------------------------------
# Boolean circuits (literals: +v / -v, variable ids >= 1; constants TRUE/FALSE as None-handling)
# ------------------------------------------------------------------------------------------------
FALSE = 0   # pseudo-literal for the constant 0


class Builder:
    """allocates CNF variables, records clauses, and builds Tseitin gates.

    Every gate output is defined by an equivalence, so every assignment of the primary variables
    has at most one extension (exactly one if it satisfies the constraints)."""

    def __init__(self):
        self.nv = 0
        self.clauses = []
        self.names = {}
        self.gates = []          # (kind, out, a, b) for evaluation
        self.kind_count = {}

    def new(self, name=None):
        self.nv += 1
        if name is not None:
            self.names[name] = self.nv
        return self.nv

    def add(self, cl, tag='misc'):
        cl = [l for l in cl]
        self.clauses.append(cl)
        self.kind_count[tag] = self.kind_count.get(tag, 0) + 1

    # gates -------------------------------------------------------------------------------------
    def XOR(self, a, b, tag='xor'):
        if a == FALSE:
            return b
        if b == FALSE:
            return a
        o = self.new()
        for cl in ([-o, a, b], [-o, -a, -b], [o, -a, b], [o, a, -b]):
            self.add(cl, tag)
        self.gates.append(('xor', o, a, b))
        return o

    def AND(self, a, b, tag='and'):
        if a == FALSE or b == FALSE:
            return FALSE
        o = self.new()
        for cl in ([-o, a], [-o, b], [o, -a, -b]):
            self.add(cl, tag)
        self.gates.append(('and', o, a, b))
        return o

    def OR3def(self, s, a, x, c, tag='card'):
        """s <-> a OR (x AND c), with a, c possibly FALSE."""
        if a == FALSE and c == FALSE:
            raise ValueError
        if c == FALSE:      # s <-> a
            return a
        if a == FALSE:      # s <-> x AND c
            return self.AND(x, c, tag)
        o = self.new()
        for cl in ([-a, o], [-x, -c, o], [-o, a, x], [-o, a, c]):
            self.add(cl, tag)
        self.gates.append(('or3', o, a, (x, c)))
        return o

    def XORs(self, lits, tag='xor'):
        acc = FALSE
        for l in lits:
            acc = self.XOR(acc, l, tag)
        return acc

    # cardinality: exactly k of lits (sequential counter with defined registers) -----------------
    def exactly(self, lits, k, tag='card'):
        if k == 0:
            for l in lits:
                self.add([-l], tag)
            return
        if len(lits) < k:
            self.add([], tag)          # unsatisfiable
            return
        reg = [FALSE] * (k + 1)        # reg[j] = [at least j of the lits seen so far], j=1..k
        for idx, x in enumerate(lits):
            if reg[k] != FALSE:        # forbid exceeding k
                self.add([-x, -reg[k]], tag)
            new = [FALSE] * (k + 1)
            for j in range(1, k + 1):
                a = reg[j]
                c = reg[j - 1] if j > 1 else None
                if j == 1:
                    new[1] = x if a == FALSE else self._or2(a, x, tag)
                else:
                    if c == FALSE:
                        new[j] = a
                    else:
                        new[j] = self.OR3def(None, a, x, c, tag)
            reg = new
        self.add([reg[k]], tag)

    def _or2(self, a, b, tag):
        o = self.new()
        for cl in ([-a, o], [-b, o], [-o, a, b]):
            self.add(cl, tag)
        self.gates.append(('or', o, a, b))
        return o


def lit_val(asg, l):
    if l == FALSE:
        return 0
    return asg[l] if l > 0 else 1 - asg[-l]


def eval_gates(B, asg):
    for kind, o, a, b in B.gates:
        if kind == 'xor':
            asg[o] = lit_val(asg, a) ^ lit_val(asg, b)
        elif kind == 'and':
            asg[o] = lit_val(asg, a) & lit_val(asg, b)
        elif kind == 'or':
            asg[o] = lit_val(asg, a) | lit_val(asg, b)
        elif kind == 'or3':
            x, c = b
            asg[o] = lit_val(asg, a) | (lit_val(asg, x) & lit_val(asg, c))
    return asg


# ------------------------------------------------------------------------------------------------
# the crossing-parity circuit (Lemma C of linear-encoding.md):  Cross = Dom + (Disj + Touch)
# ------------------------------------------------------------------------------------------------

def dom_circuit(B, pts, lo, hi, tag='dom'):
    """parity of #{(e,f) : a_e < a_f, b_e < b_f} over active points; pts = [(a, b, lit)],
    every a in [lo, hi].  Divide and conquer on a, merge by b (ties: R before L)."""
    if lo >= hi or len(pts) <= 1:
        return FALSE
    mid = (lo + hi) // 2
    L = [p for p in pts if p[0] <= mid]
    R = [p for p in pts if p[0] > mid]
    res = B.XOR(dom_circuit(B, L, lo, mid, tag), dom_circuit(B, R, mid + 1, hi, tag), tag)
    if not L or not R:
        return res
    seq = sorted([(b, 0, l) for (a, b, l) in R] + [(b, 1, l) for (a, b, l) in L])
    pre, acc = FALSE, FALSE
    for b, side, l in seq:
        if side == 1:
            pre = B.XOR(pre, l, tag)
        else:
            acc = B.XOR(acc, B.AND(pre, l, tag), tag)
    return B.XOR(res, acc, tag)


def disj_touch_circuit(B, n, edges, pos, xl, tag='dt'):
    """parity of #{(e,f) : b_e <= a_f} (disjoint or touching, e before f)."""
    HE = [[] for _ in range(n)]
    LE = [[] for _ in range(n)]
    for k, (i, j) in enumerate(edges):
        if xl[k] == FALSE:
            continue
        a, b = sorted((pos[i], pos[j]))
        LE[a].append(xl[k]); HE[b].append(xl[k])
    H, DT = FALSE, FALSE
    for t in range(n):
        H = B.XOR(H, B.XORs(HE[t], tag), tag)
        DT = B.XOR(DT, B.AND(H, B.XORs(LE[t], tag), tag), tag)
    return DT


def cross_circuit(B, n, edges, pos, xl):
    pts = []
    for k, (i, j) in enumerate(edges):
        if xl[k] != FALSE:
            a, b = sorted((pos[i], pos[j]))
            pts.append((a, b, xl[k]))
    dom = dom_circuit(B, pts, 0, n - 1)
    dt = disj_touch_circuit(B, n, edges, pos, xl)
    return B.XOR(dom, dt, 'dom'), dom, dt


def naive_cross_circuit(B, n, edges, pos, xl, tag='naive'):
    """the O(m) proposal: XOR_e x_e (S(b-1) + S(a)) + spurious corrections at the ends a, b."""
    inc = [[] for _ in range(n)]          # by position
    for k, (i, j) in enumerate(edges):
        if xl[k] != FALSE:
            inc[pos[i]].append(k); inc[pos[j]].append(k)
    p = [B.XORs([xl[k] for k in inc[t]], tag) for t in range(n)]
    S = []
    acc = FALSE
    for t in range(n):
        acc = B.XOR(acc, p[t], tag); S.append(acc)
    out = FALSE
    for k, (i, j) in enumerate(edges):
        if xl[k] == FALSE:
            continue
        a, b = sorted((pos[i], pos[j]))
        inner = B.XOR(S[b - 1], S[a], tag)
        corr = []
        for end in (a, b):
            for f in inc[end]:
                if f == k:
                    continue
                o = pos[edges[f][0]] + pos[edges[f][1]] - end
                if a < o < b:
                    corr.append(xl[f])
        inner = B.XOR(inner, B.XORs(corr, tag), tag)
        out = B.XOR(out, B.AND(xl[k], inner, tag), tag)
    return out


# ------------------------------------------------------------------------------------------------
# the CNF  phi(G, r, pos)  and its designated variable z
# ------------------------------------------------------------------------------------------------

def build_cnf(n, edges, r, pos, variant='full'):
    """variant: 'full' | 'no_cross' | 'no_touch' (Dom + Disj only) | 'no_rot' | 'add_M' |
    'naive' (coordinator's O(m) prefix circuit in place of Cross).

    Returns (Builder, z, primaries, info)."""
    B = Builder()
    m = len(edges)
    U, Bb, Pp = {}, {}, {}
    prim = []
    for k, (i, j) in enumerate(edges):
        U[k] = B.new(('u', k)); prim.append(U[k])
        for v in (i, j):
            if v == r:
                Bb[(k, v)] = FALSE; Pp[(k, v)] = FALSE
            else:
                Bb[(k, v)] = B.new(('b', k, v)); Pp[(k, v)] = B.new(('p', k, v))
                prim += [Bb[(k, v)], Pp[(k, v)]]
    nprim = B.nv
    # edge constraints: the 4 half-bits encode one of the 5 monomials, and u=0 forces 'unused'
    for k, (i, j) in enumerate(edges):
        bi, bj, pi, pj = Bb[(k, i)], Bb[(k, j)], Pp[(k, i)], Pp[(k, j)]
        hb = [l for l in (bi, bj) if l != FALSE]
        hp = [l for l in (pi, pj) if l != FALSE]
        if len(hb) == 2:
            B.add([-bi, -bj], 'edge')
        if len(hp) == 2:
            B.add([-pi, -pj], 'edge')
        for l in hb:
            B.add([-l] + hp, 'edge')       # a psibar on e needs a psi on e
        for l in hp:
            B.add([-l] + hb, 'edge')
        for l in hb + hp:
            B.add([U[k], -l], 'edge')
    # vertex constraints
    inc = [[] for _ in range(n)]
    for k, (i, j) in enumerate(edges):
        inc[i].append(k); inc[j].append(k)
    for v in range(n):
        B.exactly([U[k] for k in inc[v]], 2, 'card')
        if v != r:
            B.exactly([Bb[(k, v)] for k in inc[v]], 1, 'card')
            B.exactly([Pp[(k, v)] for k in inc[v]], 1, 'card')
    ncard = B.nv
    # mixed indicators x_e = b_{e,i} xor p_{e,i}
    xl = []
    for k, (i, j) in enumerate(edges):
        if i == r or j == r:
            xl.append(FALSE)
        else:
            xl.append(B.XOR(Bb[(k, i)], Pp[(k, i)], 'mix'))
    # rotation (local) term
    Cz = FALSE
    for v in range(n):
        if v == r:
            continue
        lower, upper = [], []
        for k in inc[v]:
            w = edges[k][0] + edges[k][1] - v
            if w == r:
                continue
            I = B.AND(Pp[(k, v)], -Bb[(k, v)], 'rot')
            O = B.AND(Bb[(k, v)], -Pp[(k, v)], 'rot')
            (lower if pos[w] < pos[v] else upper).append((pos[w], I, O))
        pre = FALSE
        for _, I, O in sorted(lower):                      # [pos u < pos w < pos v]
            Cz = B.XOR(Cz, B.AND(O, pre, 'rot'), 'rot')
            pre = B.XOR(pre, I, 'rot')
        pre = FALSE
        for _, I, O in sorted(upper, reverse=True):        # [pos v < pos w < pos u]
            Cz = B.XOR(Cz, B.AND(O, pre, 'rot'), 'rot')
            pre = B.XOR(pre, I, 'rot')
    nlocal = B.nv
    if variant == 'naive':
        Xz = naive_cross_circuit(B, n, edges, pos, xl)
    elif variant == 'no_cross':
        Xz = FALSE
    elif variant == 'no_touch':
        pts = []
        for k, (i, j) in enumerate(edges):
            if xl[k] != FALSE:
                a, b = sorted((pos[i], pos[j])); pts.append((a, b, xl[k]))
        dom = dom_circuit(B, pts, 0, n - 1)
        # Disj only (strict b_e < a_f): shift the prefix by one
        HE = [[] for _ in range(n)]; LE = [[] for _ in range(n)]
        for k, (i, j) in enumerate(edges):
            if xl[k] != FALSE:
                a, b = sorted((pos[i], pos[j])); LE[a].append(xl[k]); HE[b].append(xl[k])
        H, D = FALSE, FALSE
        for t in range(n):
            D = B.XOR(D, B.AND(H, B.XORs(LE[t])))
            H = B.XOR(H, B.XORs(HE[t]))
        Xz = B.XOR(dom, D)
    else:
        Xz, _, _ = cross_circuit(B, n, edges, pos, xl)
    parts = [Xz]
    if variant != 'no_rot':
        parts.append(Cz)
    if variant == 'add_M':          # ablation: a spurious (-1)^{#mixed edges}
        parts.append(B.XORs(xl, 'M'))
    z = B.XORs(parts, 'out')
    if z == FALSE:                        # make z a variable in all cases
        zz = B.new(); B.add([-zz], 'out'); z = zz
    info = dict(nprim=nprim, ncard=ncard - nprim, nlocal=nlocal - ncard, ncross=B.nv - nlocal)
    return B, z, prim, info


# ------------------------------------------------------------------------------------------------
# a small exact #SAT counter (DPLL + unit propagation; counts 2^free at satisfied leaves)
# ------------------------------------------------------------------------------------------------

def count_models(nv, clauses, priority=(), assumptions=()):
    sys.setrecursionlimit(100000)
    cls = [list(c) for c in clauses] + [[a] for a in assumptions]
    if any(len(c) == 0 for c in cls):
        return 0
    occ = {}
    for ci, c in enumerate(cls):
        for l in c:
            occ.setdefault(l, []).append(ci)
    val = [None] * (nv + 1)
    nsat = [0] * len(cls)
    nfalse = [0] * len(cls)
    state = {'unsat_clauses': len(cls), 'nassigned': 0}
    trail = []

    def assign(l):
        v = abs(l); val[v] = 1 if l > 0 else 0
        trail.append(v); state['nassigned'] += 1
        units = []
        conflict = False
        for ci in occ.get(l, ()):
            if nsat[ci] == 0:
                state['unsat_clauses'] -= 1
            nsat[ci] += 1
        for ci in occ.get(-l, ()):
            nfalse[ci] += 1
            if nsat[ci] == 0:
                if nfalse[ci] == len(cls[ci]):
                    conflict = True
                elif nfalse[ci] == len(cls[ci]) - 1:
                    units.append(ci)
        return conflict, units

    def unassign_to(mark):
        while len(trail) > mark:
            v = trail.pop()
            l = v if val[v] == 1 else -v
            for ci in occ.get(l, ()):
                nsat[ci] -= 1
                if nsat[ci] == 0:
                    state['unsat_clauses'] += 1
            for ci in occ.get(-l, ()):
                nfalse[ci] -= 1
            val[v] = None
            state['nassigned'] -= 1

    def litval(l):
        x = val[abs(l)]
        if x is None:
            return None
        return x if l > 0 else 1 - x

    def propagate(start_lits):
        queue = list(start_lits)
        while queue:
            l = queue.pop()
            x = litval(l)
            if x == 1:
                continue
            if x == 0:
                return False
            conflict, units = assign(l)
            if conflict:
                return False
            for ci in units:
                if nsat[ci]:
                    continue
                for l2 in cls[ci]:
                    if litval(l2) is None:
                        queue.append(l2); break
        return True

    pr = [v for v in priority]

    def pick():
        for v in pr:
            if val[v] is None:
                return v
        for ci in range(len(cls)):
            if nsat[ci] == 0:
                for l in cls[ci]:
                    if val[abs(l)] is None:
                        return abs(l)
        return None

    def rec():
        if state['unsat_clauses'] == 0:
            return 1 << (nv - state['nassigned'])
        v = pick()
        if v is None:
            return 0
        tot = 0
        for l in (v, -v):
            mark = len(trail)
            if propagate([l]):
                tot += rec()
            unassign_to(mark)
        return tot

    init = [c[0] for c in cls if len(c) == 1]
    if not propagate(init):
        return 0
    return rec()
