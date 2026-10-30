"""y = 1 gluing: rank of the acyclicity matrix A[P,Q] = [|P|+|Q|-|PvQ| = b] on set partitions of [b].
Exact rank over Q for b <= 6 (tutte_ranks.py R3) and rank mod p = 1000003 (a lower bound for the
rank over Q) for b <= 7.  Observed: Catalan(b).  Also checks the weighted version u^{|PvQ|} A for
u = 5/3 mod p.  Prints PASS/FAIL.  Needs numpy."""
import numpy as np
from math import comb
from tutte_lib import set_partitions, nblocks, join, Checker

def rank_mod(M, p):
    A = np.array(M, dtype=np.int64) % p; r = 0; rows, cols = A.shape
    for c in range(cols):
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        i = r + nz[0]; A[[r, i]] = A[[i, r]]
        A[r] = (A[r] * pow(int(A[r, c]), p - 2, p)) % p
        f = A[:, c].copy(); f[r] = 0
        A = (A - np.outer(f, A[r])) % p
        r += 1
        if r == rows:
            break
    return r

if __name__ == "__main__":
    p = 1000003; C = Checker("tutte_catalan")
    u = 5 * pow(3, p - 2, p) % p
    for b in range(1, 8):
        Ps = set_partitions(b)
        ac = [[1 if nblocks(P) + nblocks(Q) - nblocks(join(P, Q)) == b else 0 for Q in Ps] for P in Ps]
        r = rank_mod(ac, p)
        aw = [[ac[i][j] * pow(u, nblocks(join(P, Q)), p) % p for j, Q in enumerate(Ps)] for i, P in enumerate(Ps)]
        rw = rank_mod(aw, p)
        cat = comb(2 * b, b) // (b + 1)
        print(f"b={b} Bell={len(Ps)} rank_p(acyclic)={rw if False else r} rank_p(u^c acyclic)={rw} Catalan={cat}")
        C.check(r == cat and rw == cat, f"b={b}")
    C.done()
