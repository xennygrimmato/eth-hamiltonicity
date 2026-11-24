"""Smallest Route-2 instance: AG(2,2) = K_4 with all three parallel classes (perfect matchings) as merges, N0 = 2.
Nodes a,b,c,d (each 3 binary legs, dim 8).  Splits S1 = ab|cd, S2 = ac|bd, S3 = ad|bc.
f = K_4 graph tensor (equality on each of the 6 edges).
Test 1: can f = A + B with A rank-1 across S3 and B rank-1 across S1?  (would give a 2-type family with value
  max_x min_k <x,c_k> + log2 T possibly < 3 = half of E*m0 = 6.)  ALS, several restarts; report best residual.
Test 2: general T-type ALS with prescribed rank profile per type (rank_k(A_j) <= r_jk via a low-rank factor in ONE split,
  others measured), as a control.
"""
import numpy as np, itertools, sys
rng = np.random.default_rng(0)
# legs: for node v, legs to the other three nodes in fixed order.  Edge (u,v): leg (u->v) and (v->u) equal.
V = 'abcd'
def build_f():
    f = np.zeros((8, 8, 8, 8))
    # leg index of node u toward w: position of w among other nodes
    oth = {u: [w for w in V if w != u] for u in V}
    for bits in range(64):  # 6 edge bits
        eb = {}
        for i, (u, w) in enumerate(itertools.combinations(V, 2)):
            eb[frozenset((u, w))] = (bits >> i) & 1
        idx = []
        for u in V:
            x = 0
            for j, w in enumerate(oth[u]):
                x |= eb[frozenset((u, w))] << j
            idx.append(x)
        f[tuple(idx)] = 1
    return f
f = build_f()
def rk(T, grp):
    perm = [V.index(c) for c in grp] + [i for i in range(4) if V[i] not in grp]
    M = T.transpose(perm).reshape(64, 64)
    s = np.linalg.svd(M, compute_uv=False)
    return int((s > 1e-8 * s[0]).sum()) if s[0] > 0 else 0
print('ranks of f: S1', rk(f, 'ab'), 'S2', rk(f, 'ac'), 'S3', rk(f, 'ad'))

def als_two(trials=30, iters=3000):
    best = 1e9
    for t in range(trials):
        al = rng.normal(size=(8, 8)); be = rng.normal(size=(8, 8))   # al[a,d], be[b,c]
        ga = rng.normal(size=(8, 8)); de = rng.normal(size=(8, 8))   # ga[a,b], de[c,d]
        for it in range(iters):
            # solve for (al, ga) given (be, de): f[a,b,c,d] = al[a,d] be[b,c] + ga[a,b] de[c,d]
            # linear in unknowns x = (al (64), ga (64)); design matrix 4096 x 128
            D1 = np.einsum('bc,ap,dq->abcdpq', be, np.eye(8), np.eye(8)).reshape(4096, 64)
            D2 = np.einsum('cd,ap,bq->abcdpq', de, np.eye(8), np.eye(8)).reshape(4096, 64)
            x, *_ = np.linalg.lstsq(np.hstack([D1, D2]), f.reshape(-1), rcond=None)
            al = x[:64].reshape(8, 8); ga = x[64:].reshape(8, 8)
            D1 = np.einsum('ad,bp,cq->abcdpq', al, np.eye(8), np.eye(8)).reshape(4096, 64)
            D2 = np.einsum('ab,cp,dq->abcdpq', ga, np.eye(8), np.eye(8)).reshape(4096, 64)
            x, *_ = np.linalg.lstsq(np.hstack([D1, D2]), f.reshape(-1), rcond=None)
            be = x[:64].reshape(8, 8); de = x[64:].reshape(8, 8)
            if it % 50 == 0:
                R = f - np.einsum('ad,bc->abcd', al, be) - np.einsum('ab,cd->abcd', ga, de)
                r = np.linalg.norm(R) / np.linalg.norm(f)
                if r < 1e-10: break
        R = f - np.einsum('ad,bc->abcd', al, be) - np.einsum('ab,cd->abcd', ga, de)
        r = np.linalg.norm(R) / np.linalg.norm(f)
        best = min(best, r)
        print('trial', t, 'residual', round(r, 6), flush=True)
    return best
if __name__ == '__main__':
    print('best residual f = (rank1 across S3) + (rank1 across S1):', als_two(int(sys.argv[1]) if len(sys.argv) > 1 else 8, 300))
