#!/usr/bin/env python3
"""Orbit representatives of first-gate planes for the <1,2,3> matrix product over F2.

Separate from orbits.py (which is the 2x2 case and is left unchanged) and from the Rust code.
Inputs x = (a1, a2, b11, b12, b13, b21, b22, b23), bit k of an input index = x_k.
Targets c_j = a1 b1j + a2 b2j, j = 1,2,3.
Group: all maps (a, B) -> (a Q^-1, Q B R) for Q in GL2(F2), R in GL3(F2); 6 * 168 = 1008 elements.
(aQ^-1)(QBR) = (aB)R, so the targets go to linear combinations of the targets.
The script builds every element, checks that it is linear and invertible, that it maps
span(affine + targets) into itself on truth tables, and that the 1008 maps are distinct.

Writes plane_orbits_mm123.txt: one line "a b orbit_size" per orbit, representative = smallest plane
(lexicographically least (a, b) with a < b < a^b).
"""
import itertools

N = 256


def split(x):
    a = [(x >> k) & 1 for k in range(2)]
    B = [[(x >> (2 + 3 * k + j)) & 1 for j in range(3)] for k in range(2)]
    return a, B


def join(a, B):
    x = a[0] | (a[1] << 1)
    for k in range(2):
        for j in range(3):
            x |= B[k][j] << (2 + 3 * k + j)
    return x


def matmul(X, Y):
    return [[sum(X[i][l] & Y[l][j] for l in range(len(Y))) & 1 for j in range(len(Y[0]))]
            for i in range(len(X))]


def invertible_matrices(d):
    out = []
    for e in itertools.product([0, 1], repeat=d * d):
        M = [list(e[i * d:(i + 1) * d]) for i in range(d)]
        # rank over F2 by elimination
        rows = [sum(M[i][j] << j for j in range(d)) for i in range(d)]
        rank = 0
        for c in range(d):
            p = next((r for r in range(rank, d) if (rows[r] >> c) & 1), None)
            if p is None:
                continue
            rows[rank], rows[p] = rows[p], rows[rank]
            for r in range(d):
                if r != rank and (rows[r] >> c) & 1:
                    rows[r] ^= rows[rank]
            rank += 1
        if rank == d:
            out.append(M)
    return out


GL2, GL3 = invertible_matrices(2), invertible_matrices(3)
assert len(GL2) == 6 and len(GL3) == 168
I2 = [[1, 0], [0, 1]]


def inv2(Q):
    return next(X for X in GL2 if matmul(Q, X) == I2)


group = []
for Q in GL2:
    Qi = inv2(Q)
    for R in GL3:
        def g(x, Q=Q, Qi=Qi, R=R):
            a, B = split(x)
            return join(matmul([a], Qi)[0], matmul(matmul(Q, B), R))
        group.append(tuple(g(x) for x in range(N)))
assert len(set(group)) == 1008, "group elements not distinct"


def tt(f):
    return sum(1 << x for x in range(N) if f(x))


def bx(x, k):
    return (x >> k) & 1


targets = [tt(lambda x, j=j: (bx(x, 0) & bx(x, 2 + j)) ^ (bx(x, 1) & bx(x, 5 + j))) for j in range(3)]
affine = [tt(lambda x: 1)] + [tt(lambda x, k=k: bx(x, k)) for k in range(8)]


def basis_of(vs):
    piv = []  # (pivot bit, vector), fully reduced
    for b in vs:
        for p, w in piv:
            if (b >> p) & 1:
                b ^= w
        if b:
            p = (b & -b).bit_length() - 1
            piv = [(q, w ^ b if (w >> p) & 1 else w) for q, w in piv] + [(p, b)]
    return piv


def reduce(piv, v):
    for p, w in piv:
        if (v >> p) & 1:
            v ^= w
    return v


AT = basis_of(affine + targets)
assert len(AT) == 12, "targets not independent modulo the affine functions"
for gm in group:
    assert len(set(gm)) == N, "not invertible"
    for x in range(N):  # linear
        y = 0
        for k in range(8):
            if (x >> k) & 1:
                y ^= gm[1 << k]
        assert gm[x] == y
    for t in targets:
        assert reduce(AT, tt(lambda x: (t >> gm[x]) & 1)) == 0, "group does not preserve A+T"


def lin_compose(a, gm):
    """coefficient mask of x -> l_a(g(x)) (g linear)"""
    return sum(((bin(a & gm[1 << k]).count("1") & 1) << k) for k in range(8))


def canon(a, b):
    return tuple(sorted((a, b, a ^ b))[:2])


planes = sorted({canon(a, b) for a in range(1, N) for b in range(1, N) if a != b})
assert len(planes) == 10795
seen, orbits = set(), []
for p in planes:
    if p in seen:
        continue
    orb = {canon(lin_compose(p[0], gm), lin_compose(p[1], gm)) for gm in group}
    seen |= orb
    orbits.append((p, len(orb)))
assert sum(s for _, s in orbits) == 10795
with open("plane_orbits_mm123.txt", "w") as f:
    for (a, b), s in orbits:
        f.write(f"{a} {b} {s}\n")
print(len(orbits), "orbits; sizes", sorted(s for _, s in orbits))
