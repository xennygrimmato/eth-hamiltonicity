"""ap_search.py [N]: alternating-projection feasibility search for identities f = sum_i A_i with prescribed cut ranks.
Usage: python3 ap_search.py CONF N0 PROFILE restarts iters seed
  CONF: rect (4 strings a,b,c,d: wires a-c, b-d? we use x,y,u,v with [x=v][y=u]; cuts row xy|uv, col xu|yv)
        b3   (6 strings a,a',b,b',c,c'; wires a-a', b-b', c-c'; cuts = the three cube coordinates)
  PROFILE: pieces separated by ';', each piece a comma list of ranks per cut, e.g. '1,16;4,4;4,4;16,1'.
Projections: affine (sum = f), then per piece truncated SVD across each cut in turn (repeated).  Score = residual of
sum of rank-projected pieces.  Heuristic: failure is not a proof of infeasibility."""
import sys, numpy as np
conf, N0, prof, restarts, iters, seed = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
R = [[int(x) for x in p.split(',')] for p in prof.split(';')]
if conf == 'rect':   # axes x,y,u,v
    I = np.eye(N0); f = np.einsum('xv,yu->xyuv', I, I); cuts = [(0, 1), (0, 2)]
elif conf == 'b3':   # axes a,a',b,b',c,c'  nodes a=000 a'=111 b=100 b'=011 c=010 c'=101
    I = np.eye(N0); f = np.einsum('ap,bq,cr->apbqcr', I, I, I)
    cuts = [(0, 3, 4), (0, 2, 5), (0, 2, 4)]
nd = f.ndim
def proj(A, cut, r):
    rest = [i for i in range(nd) if i not in cut]
    P = np.transpose(A, list(cut) + rest); sh = P.shape
    M = P.reshape(int(np.prod(sh[:len(cut)])), -1)
    if r >= min(M.shape): return A
    U, s, Vt = np.linalg.svd(M, full_matrices=False)
    M = (U[:, :r] * s[:r]) @ Vt[:r]
    return np.transpose(M.reshape(sh), np.argsort(list(cut) + rest))
rng = np.random.default_rng(seed); nf = np.linalg.norm(f); best = 9
for rs in range(restarts):
    T = len(R); A = [rng.standard_normal(f.shape) * 0.3 for _ in range(T)]
    for it in range(iters):
        D = (f - sum(A)) / T; A = [a + D for a in A]
        for i in range(T):
            for _ in range(2):
                for k, c in enumerate(cuts): A[i] = proj(A[i], c, R[i][k])
        if it % 50 == 0 or it == iters - 1:
            res = np.linalg.norm(f - sum(A)) / nf
            if res < 1e-9: break
    best = min(best, res)
    print(f'restart {rs}: residual {res:.3e}', flush=True)
print(f'SUMMARY {conf} N0={N0} profile={prof}: best residual {best:.3e}')
