"""Heuristic [C]: is a 3-party tensor T[X,Y,Z] a triangle network with bonds (dXY, dXZ, dYZ)?
T = sum_{a,b,c} A[X,a,b] B[Y,a,c] C[Z,b,c]  (a: X-Y bond, b: X-Z bond, c: Y-Z bond).  ALS over R with small ridge;
reports best relative residual over restarts.  Used on (i) the pair pieces A_i under merge 0 ({x}|{y,v}|{u}),
(ii) terms on C under a merge (groups of 4 legs)."""
import numpy as np, sys, itertools
def als(T, dXY, dXZ, dYZ, iters=400, restarts=8, seed=0, ridge=1e-9):
    rng = np.random.default_rng(seed); nX, nY, nZ = T.shape; best = 9e9; nrm = np.linalg.norm(T)
    for r in range(restarts):
        A = rng.standard_normal((nX, dXY, dXZ)); B = rng.standard_normal((nY, dXY, dYZ)); C = rng.standard_normal((nZ, dXZ, dYZ))
        for it in range(iters):
            # solve for A: T[X,Y,Z] = sum_ab A[X,ab] M[ab, YZ],  M[ab,YZ] = sum_c B[Y,a,c] C[Z,b,c]
            M = np.einsum('yac,zbc->abyz', B, C).reshape(dXY * dXZ, nY * nZ)
            A = np.linalg.solve(M @ M.T + ridge * np.eye(len(M)), M @ T.reshape(nX, -1).T).T.reshape(nX, dXY, dXZ)
            M = np.einsum('xab,zbc->acxz', A, C).reshape(dXY * dYZ, nX * nZ)
            B = np.linalg.solve(M @ M.T + ridge * np.eye(len(M)), M @ T.transpose(1, 0, 2).reshape(nY, -1).T).T.reshape(nY, dXY, dYZ)
            M = np.einsum('xab,yac->bcxy', A, B).reshape(dXZ * dYZ, nX * nY)
            C = np.linalg.solve(M @ M.T + ridge * np.eye(len(M)), M @ T.transpose(2, 0, 1).reshape(nZ, -1).T).T.reshape(nZ, dXZ, dYZ)
        res = np.linalg.norm(np.einsum('xab,yac,zbc->xyz', A, B, C) - T) / nrm
        best = min(best, res)
        if best < 1e-8: break
    return best
if __name__ == '__main__':
    from pair_game import Ai
    for m, i, dims in [(2, 1, (2, 2, 4)), (2, 1, (4, 2, 2)), (2, 1, (2, 4, 2)), (3, 2, (4, 2, 4)), (3, 2, (4, 4, 2)), (3, 2, (2, 4, 4)),
                       (3, 2, (8, 1, 4)), (3, 1, (4, 2, 4)), (3, 1, (8, 2, 4)), (3, 2, (4, 2, 8))]:
        T = Ai(m, i).astype(float)                          # legs x,y,u,v -> X = x, Y = (y,v), Z = u
        T3 = np.transpose(T, (0, 1, 3, 2)).reshape(2 ** m, 4 ** m, 2 ** m)
        r = als(T3, *dims)
        print(f"A_(m={m},i={i}) under merge 0, bonds (x-yv, x-u, yv-u) = {dims}, cost {np.log2(np.prod(dims)):.0f} bits (2m = {2*m}): best residual {r:.2e}", flush=True)
