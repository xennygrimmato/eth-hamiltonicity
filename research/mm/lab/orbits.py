"""Orbits of planes span(l1,l2) in F2^8 (first AND gate of a 2x2 MM circuit) under the symmetry group
(A,B) -> (P A Q^-1, Q B R^-1), P,Q,R in GL2(F2), and (A,B) -> (B^T, A^T).
Linear forms l on F2^8 are 8-bit masks over vars a11 a12 a21 a22 b11 b12 b21 b22.
A linear form l(A,B) = <L_A, A> + <L_B, B> with L_A, L_B 2x2 coefficient matrices; under
A -> PAQ^-1 the coefficient matrix transforms as L_A -> P^-T L_A Q^T. We act on variable
substitution directly: l o g^-1.
"""
import itertools, numpy as np, json

def gl2():
    out = []
    for e in itertools.product([0, 1], repeat=4):
        M = np.array(e).reshape(2, 2)
        if (M[0, 0] * M[1, 1] - M[0, 1] * M[1, 0]) % 2:
            out.append(M)
    return out

def inv2(M):
    for N in gl2():
        if ((M @ N) % 2 == np.eye(2, dtype=int)).all():
            return N

def var_map(P, Q, R, tr):
    """Return 8x8 matrix G over F2 with new_vars = G old_vars (inputs map)."""
    G = np.zeros((8, 8), dtype=int)
    Qi = inv2(Q); Ri = inv2(R)
    for idx in range(8):
        X = np.zeros((2, 2), dtype=int)
        is_a = idx < 4
        X[(idx % 4) // 2, idx % 2] = 1
        if is_a:
            Y = (P @ X @ Qi) % 2; base = 0
        else:
            Y = (Q @ X @ Ri) % 2; base = 4
        for r in range(2):
            for c in range(2):
                if Y[r, c]:
                    G[base + 2 * r + c, idx] = 1
    if tr:  # (A,B) -> (B^T, A^T)
        T = np.zeros((8, 8), dtype=int)
        for r in range(2):
            for c in range(2):
                T[2 * r + c, 4 + 2 * c + r] = 1   # new a_rc = old b_cr
                T[4 + 2 * r + c, 2 * c + r] = 1   # new b_rc = old a_cr
        G = (T @ G) % 2
    return G

def form_act(G, l):
    # linear form l (row vector) in new coords: l(new) evaluated at new = G old  =>  l o G
    v = np.array([(l >> i) & 1 for i in range(8)])
    w = (v @ G) % 2
    return sum(int(w[i]) << i for i in range(8))

def plane_key(l1, l2):
    return tuple(sorted({l1, l2, l1 ^ l2}))

if __name__ == '__main__':
    group = [var_map(P, Q, R, tr) for P in gl2() for Q in gl2() for R in gl2() for tr in (0, 1)]
    planes = {}
    for l1 in range(1, 256):
        for l2 in range(l1 + 1, 256):
            planes[plane_key(l1, l2)] = None
    seen = set(); orbits = []
    for pk in planes:
        if pk in seen: continue
        orb = set()
        for G in group:
            im = plane_key(form_act(G, pk[0]), form_act(G, pk[1]))
            orb.add(im)
        seen |= orb
        orbits.append((pk, len(orb)))
    orbits.sort(key=lambda t: t[1])
    print("planes", len(planes), "orbits", len(orbits), "group", len(group))
    for pk, sz in orbits:
        print(pk, sz)
    json.dump([[list(pk), sz] for pk, sz in orbits], open('plane_orbits.json', 'w'))
