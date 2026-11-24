"""Brainstorm item: pieces of the crossing from partial sums of the Weyl expansion SWAP = (1/N) sum_{a,b} W_ab (x) W_ab^dag.
The crossing f[x,y,u,v] = [x=v][y=u] is SWAP as an operator (x,y) <- (u,v) (row split); its realignment is the
column split (operator-Schmidt rank), its partial transpose the third split (both edges internal; rank 1 for f).
For S subset Z_N^2, A_S = (1/N) sum_S W (x) W^dag.  Report (rank A_S, Schmidt rank, rank A_S^Gamma) = (row, col, third)
for every subgroup H of Z_N^2 and its cosets, and for Weyl 'balls'.  Exact ranks via sympy over Q(zeta_N) would be
slow; we use numpy SVD with tolerance (entries are cyclotomic of small height; N <= 5)."""
import itertools, numpy as np
def weyl(N):
    w = np.exp(2j*np.pi/N); X = np.roll(np.eye(N), 1, axis=0); Z = np.diag(w**np.arange(N))
    return {(a,b): np.linalg.matrix_power(X,a) @ np.linalg.matrix_power(Z,b) for a in range(N) for b in range(N)}
def rk(M, tol=1e-8):
    s = np.linalg.svd(M, compute_uv=False); return int((s > tol*max(1, s[0])).sum())
def three(N, S, W):
    A = sum(np.kron(W[g], W[g].conj().T) for g in S) / N
    T = A.reshape(N,N,N,N)            # T[x,y,u,v]: out (x,y), in (u,v)
    row = rk(A)
    col = rk(T.transpose(0,2,1,3).reshape(N*N,N*N))   # (x,u)|(y,v): operator-Schmidt
    third = rk(T.transpose(0,3,1,2).reshape(N*N,N*N)) # (x,v)|(y,u): partial-transpose split
    return row, col, third
def subgroups(N):
    G = [(a,b) for a in range(N) for b in range(N)]; seen = set(); out = []
    for g1 in G:
        for g2 in G:
            H = frozenset(((i*g1[0]+j*g2[0]) % N, (i*g1[1]+j*g2[1]) % N) for i in range(N) for j in range(N))
            if H not in seen: seen.add(H); out.append(sorted(H))
    return sorted(out, key=len)
for N in (2,3,4,5):
    W = weyl(N); lam = np.log2(N)
    full = three(N, list(W), W)
    print(f'N={N}: full sum (=SWAP=f): {full}')
    for H in subgroups(N):
        prof = three(N, H, W)
        cos = set()
        for g in W:
            S = [((g[0]+h[0]) % N, (g[1]+h[1]) % N) for h in H]
            cos.add(three(N, S, W))
        c = [np.log2(x)/lam for x in prof]
        print(f'  |H|={len(H):2d} gens~{H[1] if len(H)>1 else ()}: (row,col,third)={prof} cosets {sorted(cos)}'
              f'  cost/lambda=({c[0]:.2f},{c[1]:.2f},{c[2]:.2f}) sum={sum(c):.2f} (raw row+col 4, internal third 0)')
    # balls in centred coordinates
    cen = lambda a: a if a <= N//2 else a - N
    for r in range(0, N):
        S = [g for g in W if abs(cen(g[0])) + abs(cen(g[1])) <= r]
        print(f'  ball r={r} |S|={len(S)}: {three(N, S, W)}')
