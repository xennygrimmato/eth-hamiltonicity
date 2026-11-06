"""generic_ranks.py -- column-group flattening ranks of a random row network with bonds (2,2,2) at N0 = 2 (exact over Q
via integer entries and sympy-free fraction-free check: numpy rank of an integer matrix with small entries, cross-checked
mod p).  If generic ranks are 64, a row piece with column cost < 9 lies on a proper subvariety (each column-group rank
<= product of two column bonds).  [C] for the integer instance (rank mod p lower-bounds the rank over Q)."""
import numpy as np
from d3lib import delta3, tri_net, flat_rank
cfg = delta3(); rng = np.random.default_rng(5)
def rank_mod_p(M, p=32749):
    M = (M.astype(np.int64) % p).copy(); r = 0; rows, cols = M.shape
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i, c]), None)
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]; inv = pow(int(M[r, c]), p - 2, p); M[r] = (M[r] * inv) % p
        for i in range(rows):
            if i != r and M[i, c]: M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
        if r == rows: break
    return r
for trial in range(2):
    W = [rng.integers(-3, 4, size=(64, 2, 2)) for _ in range(3)]
    R = tri_net([w.astype(float) for w in W])
    Rc = cfg.to3_col(R)
    Ri = np.rint(Rc).astype(np.int64)
    rk = [flat_rank(Rc, g) for g in range(3)]
    rp = []
    for g in range(3):
        other = [a for a in range(3) if a != g]
        M = np.transpose(Ri, [g] + other).reshape(64, -1)
        rp.append(rank_mod_p(M))
    print(f'random integer row (2,2,2) network {trial}: column-group flattening ranks (float) {rk}, mod 32749 {rp}')
