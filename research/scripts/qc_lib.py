"""Exact Z[omega] arithmetic, Clifford+T circuits, and the integer networks of
research/quantum-circuits.md.  No floats anywhere.

Elements of Z[w], w = e^{i pi/4}, are 4-tuples (a0,a1,a2,a3) = a0 + a1 w + a2 w^2 + a3 w^3, w^4 = -1.
A "scaled" gate is (N, k): the true matrix is N / sqrt2^k with N having entries in Z[w].
Matrices are dicts/lists indexed [out][in]; for two-qubit gates on (q1,q2) the index is 2*b_q1 + b_q2.
"""
import itertools
import random

# ----------------------------------------------------------------------------- Z[w]
ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)
W1 = (0, 1, 0, 0)
SQRT2 = (0, 1, 0, -1)          # w - w^3 = sqrt 2


def zadd(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3])


def zneg(a):
    return (-a[0], -a[1], -a[2], -a[3])


def zmul(a, b):
    c = [0] * 7
    for i in range(4):
        if a[i]:
            for j in range(4):
                c[i + j] += a[i] * b[j]
    # w^4 = -1, w^5 = -w, w^6 = -w^2
    return (c[0] - c[4], c[1] - c[5], c[2] - c[6], c[3])


def zconj(a):
    # w -> w^7 = -w^3, w^2 -> w^6 = -w^2, w^3 -> w^5 = -w
    return (a[0], -a[3], -a[2], -a[1])


def zsigma(a, t):
    """Galois automorphism w -> w^t (t odd).  Used only for sanity bounds."""
    out = ZERO
    for j in range(4):
        e = (j * t) % 8
        term = [0, 0, 0, 0]
        if e < 4:
            term[e] = a[j]
        else:
            term[e - 4] = -a[j]
        out = zadd(out, tuple(term))
    return out


def zl1(a):
    return sum(abs(x) for x in a)


def zpow_sqrt2(k):
    r = ONE
    for _ in range(k):
        r = zmul(r, SQRT2)
    return r


# ----------------------------------------------------------------------------- gates
def m1(rows):
    return [list(r) for r in rows]


O, I1 = ZERO, ONE
WP = lambda j: zmul(ONE, tuple(1 if t == j % 4 else 0 for t in range(4))) if j % 8 < 4 else zneg(
    tuple(1 if t == j % 4 else 0 for t in range(4)))   # w^j

GATES1 = {
    'H': (m1([[I1, I1], [I1, zneg(I1)]]), 1),
    'T': (m1([[I1, O], [O, WP(1)]]), 0),
    'Tdg': (m1([[I1, O], [O, WP(7)]]), 0),
    'S': (m1([[I1, O], [O, WP(2)]]), 0),
    'Sdg': (m1([[I1, O], [O, WP(6)]]), 0),
    'X': (m1([[O, I1], [I1, O]]), 0),
    'Z': (m1([[I1, O], [O, zneg(I1)]]), 0),
}


def diag4(ds):
    return [[ds[r] if r == c else O for c in range(4)] for r in range(4)]


def _cnot():
    M = [[O] * 4 for _ in range(4)]
    for b1 in range(2):
        for b2 in range(2):
            M[2 * b1 + (b2 ^ b1)][2 * b1 + b2] = I1
    return M


def _swap():
    M = [[O] * 4 for _ in range(4)]
    for b1 in range(2):
        for b2 in range(2):
            M[2 * b2 + b1][2 * b1 + b2] = I1
    return M


def _ch():
    # |0><0| (x) I + |1><1| (x) H, scaled by sqrt2 (k = 1): entries sqrt2 and +-1
    M = [[O] * 4 for _ in range(4)]
    M[0][0] = SQRT2; M[1][1] = SQRT2
    M[2][2] = I1; M[2][3] = I1; M[3][2] = I1; M[3][3] = zneg(I1)
    return M


GATES2 = {
    'CNOT': (_cnot(), 0),
    'CZ': (diag4([I1, I1, I1, zneg(I1)]), 0),
    'CS': (diag4([I1, I1, I1, WP(2)]), 0),
    'SWAP': (_swap(), 0),
    'CH': (_ch(), 1),
}


def matmul(A, B):
    n = len(A)
    return [[_dot(A[r], [B[t][c] for t in range(n)]) for c in range(n)] for r in range(n)]


def _dot(u, v):
    s = ZERO
    for a, b in zip(u, v):
        if a != ZERO and b != ZERO:
            s = zadd(s, zmul(a, b))
    return s


def kron2(A, B):
    """A on the first (high) qubit, B on the second."""
    M = [[O] * 4 for _ in range(4)]
    for r1 in range(2):
        for c1 in range(2):
            for r2 in range(2):
                for c2 in range(2):
                    M[2 * r1 + r2][2 * c1 + c2] = zmul(A[r1][c1], B[r2][c2])
    return M


ID2 = m1([[I1, O], [O, I1]])


def random_circuit(rng, n, G, G1, set2=('CNOT', 'CZ', 'CS', 'SWAP', 'CH'), set1=('H', 'T', 'Tdg', 'S', 'X', 'Z')):
    """G two-qubit gates (any connectivity) interleaved with G1 single-qubit gates."""
    ops = [('2', rng.choice(set2), tuple(rng.sample(range(n), 2))) for _ in range(G)]
    ops += [('1', rng.choice(set1), (rng.randrange(n),)) for _ in range(G1)]
    rng.shuffle(ops)
    return ops


def circuit_k(ops):
    return sum((GATES2 if t == '2' else GATES1)[name][1] for t, name, _ in ops)


# ----------------------------------------------------------------------------- state vector (ground truth)
def statevector(ops, n, x):
    """Exact numerators: returns (vec, k) with |C|x> = vec / sqrt2^k.  Qubit q is bit (n-1-q) of the index."""
    vec = [ZERO] * (1 << n)
    vec[_idx(x, n)] = ONE
    k = 0
    for t, name, qs in ops:
        if t == '1':
            M, kk = GATES1[name]
            q = qs[0]; sh = n - 1 - q
            new = [ZERO] * (1 << n)
            for i, a in enumerate(vec):
                if a == ZERO:
                    continue
                b = (i >> sh) & 1
                for r in range(2):
                    e = M[r][b]
                    if e != ZERO:
                        j = (i & ~(1 << sh)) | (r << sh)
                        new[j] = zadd(new[j], zmul(e, a))
            vec = new
        else:
            M, kk = GATES2[name]
            q1, q2 = qs; s1, s2 = n - 1 - q1, n - 1 - q2
            new = [ZERO] * (1 << n)
            for i, a in enumerate(vec):
                if a == ZERO:
                    continue
                cin = 2 * ((i >> s1) & 1) + ((i >> s2) & 1)
                for r in range(4):
                    e = M[r][cin]
                    if e != ZERO:
                        j = (i & ~(1 << s1) & ~(1 << s2)) | ((r >> 1) << s1) | ((r & 1) << s2)
                        new[j] = zadd(new[j], zmul(e, a))
            vec = new
        k += kk
    return vec, k


def _idx(bits, n):
    v = 0
    for q in range(n):
        v |= bits[q] << (n - 1 - q)
    return v


# ----------------------------------------------------------------------------- circuit -> gate tensors on segments
class TensorNet:
    """Gate vertices with Z[w] numerator tensors on bit variables ('segments').
    gates[i] = (legs, table): legs = list of variable ids or ('fix', bit); table[(b_leg0,..)] = Z[w].
    value = scalar * sum_{vars} prod_i table_i ;  true quantity = value / sqrt2^k."""

    def __init__(self):
        self.gates = []
        self.nvars = 0
        self.scalar = ONE
        self.k = 0

    def newvar(self):
        self.nvars += 1
        return self.nvars - 1


def circuit_to_net(ops, n, x, y):
    """Section 2 of the note: merge single-qubit runs into the next two-qubit gate on that line
    (the trailing run into the last gate), one bit per internal segment, inputs/outputs fixed."""
    net = TensorNet()
    pend = {q: (ID2, 0) for q in range(n)}          # pending 1q product on line q (numerator, k)
    cur = {q: ('fix', x[q]) for q in range(n)}       # current open leg on line q
    last = {q: None for q in range(n)}               # (gate index, position) of last 2q gate on q
    raw = []                                          # (M, k, legs_out, legs_in)
    for t, name, qs in ops:
        if t == '1':
            M, kk = GATES1[name]
            P, pk = pend[qs[0]]
            pend[qs[0]] = (matmul2(M, P), pk + kk)
        else:
            U, kk = GATES2[name]
            q1, q2 = qs
            (R1, k1), (R2, k2) = pend[q1], pend[q2]
            M = matmul(U, kron2(R1, R2))
            pend[q1] = (ID2, 0); pend[q2] = (ID2, 0)
            o1, o2 = net.newvar(), net.newvar()
            raw.append([M, kk + k1 + k2, [o1, o2], [cur[q1], cur[q2]]])
            gi = len(raw) - 1
            cur[q1], cur[q2] = o1, o2
            last[q1], last[q2] = (gi, 0), (gi, 1)
    # trailing runs and outputs
    for q in range(n):
        R, rk = pend[q]
        if last[q] is None:                           # untouched by 2q gates: a scalar factor
            net.scalar = zmul(net.scalar, R[y[q]][x[q]])
            net.k += rk
            continue
        gi, pos = last[q]
        M = raw[gi][0]
        A = kron2(R, ID2) if pos == 0 else kron2(ID2, R)
        raw[gi][0] = matmul(A, M)
        raw[gi][1] += rk
        raw[gi][2][pos] = ('fix', y[q])               # the output leg is fixed to y_q
    # variables that ended up fixed were created but are now unused; renumber used ones
    used = sorted({v for r in raw for v in r[2] + r[3] if not isinstance(v, tuple)})
    ren = {v: i for i, v in enumerate(used)}
    net.nvars = len(used)
    for M, kk, lo, li in raw:
        legs = [ren[v] if not isinstance(v, tuple) else v for v in lo + li]
        table = {}
        for bits in itertools.product(range(2), repeat=4):
            table[bits] = M[2 * bits[0] + bits[1]][2 * bits[2] + bits[3]]
        net.gates.append((legs, table))
        net.k += kk
    return net


def matmul2(A, B):
    return [[zadd(zmul(A[r][0], B[0][c]), zmul(A[r][1], B[1][c])) for c in range(2)] for r in range(2)]


def doubled_net(ops, n, x, yS):
    """Probability / marginal network: C and conj(C) with the outputs of unmeasured qubits identified.
    yS: dict q -> bit for measured qubits.  value / 2^k = sum_{y consistent} |<y|C|x>|^2 (k = 2 k_C)."""
    # build C with symbolic outputs: use a 'free' marker then wire them
    netC = circuit_to_net_free(ops, n, x, yS)
    return netC


def circuit_to_net_free(ops, n, x, yS):
    """Doubled network.  Implemented by building both copies with output legs as shared variables."""
    net = TensorNet()
    outvar = {}
    for q in range(n):
        outvar[q] = ('fix', yS[q]) if q in yS else None
    copies = []
    for conj in (False, True):
        pend = {q: (ID2, 0) for q in range(n)}
        cur = {q: ('fix', x[q]) for q in range(n)}
        last = {q: None for q in range(n)}
        raw = []
        for t, name, qs in ops:
            if t == '1':
                M, kk = GATES1[name]
                P, pk = pend[qs[0]]
                pend[qs[0]] = (matmul2(M, P), pk + kk)
            else:
                U, kk = GATES2[name]
                q1, q2 = qs
                (R1, k1), (R2, k2) = pend[q1], pend[q2]
                M = matmul(U, kron2(R1, R2))
                pend[q1] = (ID2, 0); pend[q2] = (ID2, 0)
                o1, o2 = ('tmp', len(raw), 0), ('tmp', len(raw), 1)
                raw.append([M, kk + k1 + k2, [o1, o2], [cur[q1], cur[q2]]])
                cur[q1], cur[q2] = o1, o2
                last[q1], last[q2] = (len(raw) - 1, 0), (len(raw) - 1, 1)
        copies.append((raw, pend, last, conj))
    # shared output variables for unmeasured touched qubits
    for q in range(n):
        if q not in yS:
            outvar[q] = None
    varmap = {}

    def var_of(key):
        if key not in varmap:
            varmap[key] = net.newvar()
        return varmap[key]

    for ci, (raw, pend, last, conj) in enumerate(copies):
        for q in range(n):
            R, rk = pend[q]
            if last[q] is None:
                continue
            gi, pos = last[q]
            A = kron2(R, ID2) if pos == 0 else kron2(ID2, R)
            raw[gi][0] = matmul(A, raw[gi][0])
            raw[gi][1] += rk
            raw[gi][2][pos] = outvar[q] if q in yS else ('out', q)
        for M, kk, lo, li in raw:
            legs = []
            for v in lo + li:
                if isinstance(v, tuple) and v[0] == 'fix':
                    legs.append(v)
                elif isinstance(v, tuple) and v[0] == 'out':
                    legs.append(var_of(v))
                else:
                    legs.append(var_of((ci,) + v))
            table = {}
            for bits in itertools.product(range(2), repeat=4):
                e = M[2 * bits[0] + bits[1]][2 * bits[2] + bits[3]]
                table[bits] = zconj(e) if conj else e
            net.gates.append((legs, table))
            net.k += kk
    # untouched qubits: scalar factors
    for q in range(n):
        if copies[0][2][q] is not None:
            continue
        R, rk = copies[0][1][q]
        if q in yS:
            a = R[yS[q]][x[q]]
            net.scalar = zmul(net.scalar, zmul(a, zconj(a)))
        else:
            s = ZERO
            for yy in range(2):
                a = R[yy][x[q]]
                s = zadd(s, zmul(a, zconj(a)))
            net.scalar = zmul(net.scalar, s)
        net.k += 2 * rk
    return net


# ----------------------------------------------------------------------------- generic evaluators
def brute_value(net, ring_mul, ring_add, ring_zero, ring_one, conv):
    """sum over all variable assignments of prod of converted gate entries."""
    total = ring_zero
    for assign in itertools.product(range(2), repeat=net.nvars):
        prod = ring_one
        for legs, table in net.gates:
            key = tuple(l[1] if isinstance(l, tuple) else assign[l] for l in legs)
            e = conv(table[key])
            prod = ring_mul(prod, e)
            if prod == ring_zero:
                break
        total = ring_add(total, prod)
    return total


def ve_value(factors, nvars, ring_mul, ring_add, ring_zero, ring_one):
    """Exact variable elimination.  factors: list of (vars tuple, dict assignment-tuple -> ring)."""
    factors = [(tuple(v), dict(t)) for v, t in factors]
    remaining = set(range(nvars))
    while remaining:
        # min-degree heuristic
        best = min(remaining, key=lambda v: len(set().union(*[set(f[0]) for f in factors if v in f[0]] or [set()])))
        inv = [f for f in factors if best in f[0]]
        rest = [f for f in factors if best not in f[0]]
        scope = sorted(set().union(*[set(f[0]) for f in inv]) - {best}) if inv else []
        newt = {}
        for a in itertools.product(range(2), repeat=len(scope)):
            env = dict(zip(scope, a))
            s = ring_zero
            for bv in range(2):
                env[best] = bv
                p = ring_one
                for vs, t in inv:
                    p = ring_mul(p, t[tuple(env[u] for u in vs)])
                    if p == ring_zero:
                        break
                s = ring_add(s, p)
            newt[a] = s
        if inv:
            rest.append((tuple(scope), newt))
        else:
            # isolated variable: factor 2
            rest.append(((), {(): ring_add(ring_one, ring_one)}))
        factors = rest
        remaining.discard(best)
    out = ring_one
    for vs, t in factors:
        out = ring_mul(out, t[()])
    return out


def ve_partial(factors, elim, ring_mul, ring_add, ring_zero, ring_one):
    """eliminate (sum out) the variables in elim; return the remaining factors."""
    factors = [(tuple(v), dict(t)) for v, t in factors]
    remaining = set(elim)
    while remaining:
        best = min(remaining, key=lambda v: len(set().union(*[set(f[0]) for f in factors if v in f[0]] or [set()])))
        inv = [f for f in factors if best in f[0]]
        rest = [f for f in factors if best not in f[0]]
        scope = sorted(set().union(*[set(f[0]) for f in inv]) - {best}) if inv else []
        newt = {}
        for a in itertools.product(range(2), repeat=len(scope)):
            env = dict(zip(scope, a))
            s = ring_zero
            for bv in range(2):
                env[best] = bv
                p = ring_one
                for vs, t in inv:
                    p = ring_mul(p, t[tuple(env[u] for u in vs)])
                    if p == ring_zero:
                        break
                s = ring_add(s, p)
            newt[a] = s
        rest.append((tuple(scope), newt) if inv else ((), {(): ring_add(ring_one, ring_one)}))
        factors = rest
        remaining.discard(best)
    return factors


def gate_factors(net, conv):
    fs = []
    for legs, table in net.gates:
        vs = sorted({l for l in legs if not isinstance(l, tuple)})
        t = {}
        for a in itertools.product(range(2), repeat=len(vs)):
            env = dict(zip(vs, a))
            key = tuple(l[1] if isinstance(l, tuple) else env[l] for l in legs)
            t[a] = conv(table[key])
        fs.append((tuple(vs), t))
    return fs


ZR = dict(ring_mul=zmul, ring_add=zadd, ring_zero=ZERO, ring_one=ONE)


# ----------------------------------------------------------------------------- Anthropic-style integer network
def kron(a, b):
    return a[0] + (a[1] << b) + (a[2] << (2 * b)) + (a[3] << (3 * b))


def balanced_digits(r, b, ndig):
    """write r = sum d_j 2^{bj} with |d_j| < 2^{b-1} (balanced), j < ndig; return digits and remainder."""
    ds = []
    base = 1 << b
    for _ in range(ndig):
        d = r % base
        if d >= base // 2:
            d -= base
        ds.append(d)
        r = (r - d) >> b
    return ds, r


def decode_mod(Z, b):
    """Z = Kron(A) mod 2^{4b}+1 -> A (needs |a_j| <= 2^{b-1}-1)."""
    M = (1 << (4 * b)) + 1
    r = Z % M
    if r > M // 2:
        r -= M
    ds, rem = balanced_digits(r, b, 4)
    assert rem == 0, "decode_mod: remainder"
    return tuple(ds)


def decode_full(Z, b, deg):
    """Z = Q(2^b) for Q in Z[x] of degree <= deg -> Q (balanced digits), then reduce mod x^4+1."""
    ds, rem = balanced_digits(Z, b, deg + 1)
    assert rem == 0, "decode_full: remainder"
    a = [0, 0, 0, 0]
    for j, d in enumerate(ds):
        a[j % 4] += d if (j // 4) % 2 == 0 else -d
    return tuple(a)


class IntNetwork:
    """Definition 2 of [A] with equality-test edges: node a has settings = its boundary segment bits;
    W_a(z_a) = Kron_b( sum over internal bits of prod of its gate tensors ); Psi_ab = [copies agree]."""

    def __init__(self, net, groups, g, b):
        self.net, self.g, self.b = net, g, b
        endp = {}                               # var -> set of groups touching it
        for gi, (legs, _) in enumerate(net.gates):
            for l in legs:
                if not isinstance(l, tuple):
                    endp.setdefault(l, set()).add(groups[gi])
        self.cross = sorted(v for v, s in endp.items() if len(s) == 2)
        self.internal = {a: sorted(v for v, s in endp.items() if s == {a}) for a in range(g)}
        self.bnd = {a: sorted(v for v in self.cross if a in endp[v]) for a in range(g)}
        self.c = {}
        for v in self.cross:
            a, bb = sorted(endp[v])
            self.c[(a, bb)] = self.c.get((a, bb), 0) + 1
        self.members = {a: [gi for gi in range(len(net.gates)) if groups[gi] == a] for a in range(g)}
        self.U = 2 * len(self.cross)
        self.tables = {a: self._table(a) for a in range(g)}
        self.l1 = {a: max([zl1(v) for v in self._ztab[a].values()] + [1]) for a in range(g)}

    def _table(self, a):
        """sum over the group's internal bits by exact variable elimination, then tabulate on the boundary."""
        if not hasattr(self, '_ztab'):
            self._ztab = {}
        bvars, ivars = self.bnd[a], self.internal[a]
        sub = TensorNet()
        sub.gates = [self.net.gates[gi] for gi in self.members[a]]
        fs = gate_factors(sub, lambda e: e)
        fs = ve_partial(fs, ivars, **ZR)
        zt, it = {}, {}
        for zb in itertools.product(range(2), repeat=len(bvars)):
            env = dict(zip(bvars, zb))
            p = ONE
            for vs, t in fs:
                p = zmul(p, t[tuple(env[u] for u in vs)])
                if p == ZERO:
                    break
            zt[zb] = p
            it[zb] = kron(p, self.b)
        self._ztab[a] = zt
        return it

    def value_brute(self):
        """sum over crossing bits (= Def. 2 value: equality tests force all copies equal)."""
        tot = 0
        pos = {v: i for i, v in enumerate(self.cross)}
        for sig in itertools.product(range(2), repeat=len(self.cross)):
            p = 1
            for a in range(self.g):
                p *= self.tables[a][tuple(sig[pos[v]] for v in self.bnd[a])]
                if p == 0:
                    break
            tot += p
        return tot

    def value_def2_literal(self):
        """Literal Definition 2: settings z_a in {0,1}^{P_a}, Psi_ab = prod over shared segments [z_a(v)=z_b(v)]."""
        tot = 0
        A = range(self.g)
        for zs in itertools.product(*[list(itertools.product(range(2), repeat=len(self.bnd[a]))) for a in A]):
            psi = 1
            for (a, bb) in self.c:
                for v in self.cross:
                    if v in self.bnd[a] and v in self.bnd[bb]:
                        if zs[a][self.bnd[a].index(v)] != zs[bb][self.bnd[bb].index(v)]:
                            psi = 0
                            break
                if psi == 0:
                    break
            if psi == 0:
                continue
            p = 1
            for a in A:
                p *= self.tables[a][zs[a]]
            tot += p
        return tot

    def value_ve(self):
        fs = [(tuple(self.bnd[a]), {k: v for k, v in self.tables[a].items()}) for a in range(self.g)]
        # rename crossing vars to 0..m-1
        ren = {v: i for i, v in enumerate(self.cross)}
        fs = [(tuple(ren[v] for v in vs), t) for vs, t in fs]
        return ve_value(fs, len(self.cross), lambda p, q: p * q, lambda p, q: p + q, 0, 1)

    def params(self):
        G = len(self.net.gates)
        P = 4 * -(-G // self.g) + 1
        Pa = {a: len(self.bnd[a]) for a in range(self.g)}
        return P, Pa


def random_groups(rng, G, g, contiguous=False):
    """balanced partition of gates into g groups of size <= ceil(G/g)."""
    idx = list(range(G))
    if not contiguous:
        rng.shuffle(idx)
    groups = [0] * G
    cap = -(-G // g) if G else 1
    for pos, gi in enumerate(idx):
        groups[gi] = min(pos // cap, g - 1)
    return groups


# ----------------------------------------------------------------------------- OpenAI ring (Z/2^P0)[V]/(V^l)
def make_trunc_ring(P0, ell):
    mod = 1 << P0

    def mul(p, q):
        r = [0] * ell
        for i, a in enumerate(p):
            if a:
                for j in range(min(len(q), ell - i)):
                    r[i + j] = (r[i + j] + a * q[j]) % mod
        return tuple(r)

    def add(p, q):
        return tuple((a + b) % mod for a, b in zip(p, q))

    zero = tuple([0] * ell)
    one = tuple([1 % mod] + [0] * (ell - 1))

    def conv(a):            # Z[w] numerator -> polynomial in V of degree <= 3 (x -> V)
        r = [0] * ell
        for j in range(4):
            r[j] = a[j] % mod
        return tuple(r)

    return dict(ring_mul=mul, ring_add=add, ring_zero=zero, ring_one=one), conv, mod


def reduce_x4p1_mod(p, mod):
    a = [0, 0, 0, 0]
    for j, c in enumerate(p):
        a[j % 4] += c if (j // 4) % 2 == 0 else -c
    out = []
    for v in a:
        v %= mod
        if v >= mod // 2:
            v -= mod
        out.append(v)
    return tuple(out)
