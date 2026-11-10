"""Realizable version of the finite model: column generation over actual configurations
(D distinct points on circle, multiplicities). maximise E sum m_j^2 / N s.t. E|p_k|^2 = min(k,N), k=1..K."""
import numpy as np, sys, itertools
from scipy.optimize import linprog, minimize
rng = np.random.default_rng(1)
def partitions(n, maxpart):
    if n==0: yield (); return
    for p in range(min(n,maxpart),0,-1):
        for rest in partitions(n-p, p): yield (p,)+rest
def feats(th, m, K):
    ks = np.arange(1,K+1)
    p = (m[None,:]*np.exp(2j*np.pi*np.outer(ks,th))).sum(1)
    return np.abs(p)**2
def price(y, m, K, restarts):
    ks = np.arange(1,K+1); D=len(m)
    def f(t):
        th = np.concatenate([[0.0],t])
        E = np.exp(2j*np.pi*np.outer(ks,th)); p = (m[None,:]*E).sum(1)
        val = (y*np.abs(p)**2).sum()
        # grad wrt th_j: d|p|^2 = 2 Re(conj(p) * m_j * 2pi i k e)
        g = (y[:,None]*2*np.real(np.conj(p)[:,None]*m[None,:]*2j*np.pi*ks[:,None]*E)).sum(0)
        return val, g[1:]
    best=(np.inf,None)
    for _ in range(restarts):
        t0 = rng.random(D-1)
        r = minimize(f, t0, jac=True, method='L-BFGS-B')
        if r.fun < best[0]: best=(r.fun, np.concatenate([[0.0],r.x%1]))
    return best
def solve(N, K, maxpart=3, iters=200, restarts=20, verbose=False):
    pats = [np.array(p,float) for p in partitions(N, maxpart)]
    cols=[]; G=[]
    for p in pats:
        for _ in range(5):
            th = rng.random(len(p)); cols.append(feats(th,p,K)); G.append((p**2).sum())
    target = np.array([min(k,N) for k in range(1,K+1)],float)
    BIG=1e3
    for it in range(iters):
        F = np.array(cols).T; g=np.array(G)
        nc=F.shape[1]
        # vars: lambda (nc), s+ (K), s- (K)
        A_eq = np.vstack([np.hstack([F, np.eye(K), -np.eye(K)]), np.hstack([np.ones((1,nc)), np.zeros((1,2*K))])])
        b_eq = np.concatenate([target,[1.0]])
        cost = np.concatenate([-g, BIG*np.ones(2*K)])
        r = linprog(cost, A_eq=A_eq, b_eq=b_eq, bounds=[(0,None)]*(nc+2*K), method='highs')
        duals = r.eqlin.marginals  # d obj / d b ; obj = -sum g lam
        y = -duals[:K]; y0 = -duals[K]
        art = r.x[nc:].sum()
        val = -(r.fun - BIG*art)
        # pricing: want g(C) - y.f(C) - y0 > 0
        added=0; bestred=-np.inf
        for p in pats:
            fv, th = price(y, p, K, restarts)
            red = (p**2).sum() - fv - y0
            bestred=max(bestred,red)
            if red > 1e-7:
                cols.append(feats(th,p,K)); G.append((p**2).sum()); added+=1
        if verbose: print(it, 'kappa=%.6f art=%.2e cols=%d added=%d bestred=%.2e'%(val/N, art, len(cols), added, bestred), flush=True)
        if added==0: break
    lam = r.x[:nc]
    return val/N, art, lam, cols, G
if __name__=='__main__':
    N=int(sys.argv[1]); K=int(sys.argv[2]) if len(sys.argv)>2 else N
    mp = int(sys.argv[3]) if len(sys.argv)>3 else 3
    k, art, lam, cols, G = solve(N,K,maxpart=mp,verbose=True)
    print('N=%d K=%d kappa_real=%.6f simple>=%.6f art=%.1e'%(N,K,k,2-k,art))
