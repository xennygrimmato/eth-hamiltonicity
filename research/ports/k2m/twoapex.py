"""Two-apex networks: parties u1,u2,v_1..v_m; supply only on pairs u_k v_i (capacities c1_i, c2_i) and
u1u2 (capacity c0); demand arbitrary: r_ij on v_i v_j, w on u1u2.
 f_flow : min over all pseudometrics (LP),
 f_cut  : min over cuts,
 f_book : min over m-page books  (= min over all CAT(0) configurations, notes Prop. B),
 f_pod  : min over configurations in (m-pod) x R (hubs anywhere on the singular line; forced under not-Contracting).
"""
import itertools, numpy as np
from scipy.optimize import minimize, linprog

def flow_value(n, sup, dem):
    """sup, dem: dict {(i,j): weight}, i<j, parties 0..n-1. LP: min sum c d s.t. sum r d = 1, triangle ineqs."""
    pr = list(itertools.combinations(range(n), 2)); ix = {p: k for k, p in enumerate(pr)}
    c = np.zeros(len(pr)); r = np.zeros(len(pr))
    for p, x in sup.items(): c[ix[tuple(sorted(p))]] += x
    for p, x in dem.items(): r[ix[tuple(sorted(p))]] += x
    A = []
    for i, j, k in itertools.combinations(range(n), 3):
        for (a, b), (a2, b2), (a3, b3) in (((i, j), (i, k), (j, k)), ((i, k), (i, j), (j, k)), ((j, k), (i, j), (i, k))):
            row = np.zeros(len(pr)); row[ix[(a, b)]] = 1; row[ix[(a2, b2)]] = -1; row[ix[(a3, b3)]] = -1; A.append(row)
    res = linprog(c, A_ub=np.array(A), b_ub=np.zeros(len(A)), A_eq=[r], b_eq=[1], bounds=(0, None), method='highs')
    return res.fun

def cut_value(n, sup, dem):
    best = np.inf; arg = None
    for mask in range(1, 2**(n-1)):
        X = {i for i in range(n) if mask >> i & 1}
        s = sum(x for (i, j), x in sup.items() if (i in X) != (j in X))
        d = sum(x for (i, j), x in dem.items() if (i in X) != (j in X))
        if d > 0 and s/d < best: best = s/d; arg = sorted(X)
    return best, arg

class TwoApex:
    def __init__(self, m, c1, c2, r, w, c0=0.0):
        self.m = m; self.c1 = np.array(c1, float); self.c2 = np.array(c2, float)
        self.r = {tuple(sorted(k)): v for k, v in r.items() if v > 0}; self.w = w; self.c0 = c0
    def graphs(self):
        m = self.m; sup = {}; dem = {}
        for i in range(m):
            if self.c1[i] > 0: sup[(0, 2+i)] = self.c1[i]
            if self.c2[i] > 0: sup[(1, 2+i)] = self.c2[i]
        if self.c0 > 0: sup[(0, 1)] = self.c0
        for (i, j), v in self.r.items(): dem[(2+i, 2+j)] = v
        if self.w > 0: dem[(0, 1)] = self.w
        return sup, dem
    def ratio(self, x, D, pod=False, info=False):
        m = self.m; rho = np.abs(x[:m]); a = x[m:2*m]
        S = self.c1 @ np.hypot(rho, a) + self.c2 @ np.hypot(rho, a - D) + self.c0*D
        T = self.w*D; ends = 0
        for (i, j), rij in self.r.items():
            den = rho[i] + rho[j]
            y = (a[i]*rho[j] + a[j]*rho[i])/den if den > 1e-300 else 0.5*(a[i]+a[j])
            if not pod:
                yc = min(max(y, 0.0), D)
                if yc != y: ends += 1
                y = yc
            T += rij*(np.hypot(rho[i], a[i]-y) + np.hypot(rho[j], a[j]-y))
        if info: return S/T, ends
        return S/T if T > 1e-300 else 1e9
    def minimise(self, pod=False, starts=60, seed=0):
        rng = np.random.default_rng(seed); m = self.m; best = (np.inf, None, None)
        for s in range(starts):
            D = 1.0 if s % 6 else 0.0
            scale = 10**rng.uniform(-1.5, 1.5)
            x0 = np.concatenate([scale*rng.uniform(0, 2, m), 0.5*D + scale*rng.normal(0, 1, m)])
            f = lambda x: self.ratio(x, D, pod)
            r_ = minimize(f, x0, method='Nelder-Mead', options=dict(xatol=1e-11, fatol=1e-14, maxiter=30000, maxfev=30000))
            r_ = minimize(f, r_.x, method='Powell', options=dict(xtol=1e-12, ftol=1e-15))
            if r_.fun < best[0]: best = (r_.fun, r_.x.copy(), D)
        return best
    def report(self, name, starts=60, seed=0):
        sup, dem = self.graphs(); n = self.m + 2
        fl = flow_value(n, sup, dem); ct, X = cut_value(n, sup, dem)
        bk = self.minimise(False, starts, seed); pd = self.minimise(True, starts, seed+1)
        _, ends = self.ratio(bk[1], bk[2], False, True)
        print(f"{name}: flow={fl:.6f}  book(CAT0)={bk[0]:.6f}  pod×R={pd[0]:.6f}  cut={ct:.6f} (X={X})  "
              f"[book optimum: D={bk[2]}, pairs through a spine end: {ends}]")
        m = self.m
        print("     book: rho=", np.round(np.abs(bk[1][:m]), 4), "a=", np.round(bk[1][m:], 4))
        return fl, bk[0], pd[0], ct

if __name__ == "__main__":
    K = lambda m: {(i, j): 1 for i, j in itertools.combinations(range(m), 2)}
    TwoApex(3, [1]*3, [1]*3, K(3), 1).report("K23 w=1")
    TwoApex(4, [1]*4, [1]*4, K(4), 1).report("K24 w=1")
    C5 = {(i, (i+1) % 5): 1 for i in range(5)}
    TwoApex(5, [1]*5, [1]*5, C5, 1).report("K25 + C5 demand, w=1", starts=120)
    octa = {(i, j): 1 for i, j in itertools.combinations(range(6), 2) if j != i + 3}
    TwoApex(6, [1]*6, [1]*6, octa, 1).report("K26 + octahedron demand, w=1", starts=80)
    TwoApex(3, [2, 2, 1], [1, 1, 1], {(0, 1): 2, (0, 2): 1, (1, 2): 1}, 1).report("scan #2 (u1v1,u1v2 doubled; v1v2 doubled)")
    TwoApex(3, [1]*3, [1]*3, {(0, 1): 2, (0, 2): 1, (1, 2): 1}, 1).report("K23, demand v1v2 x2")
    TwoApex(3, [1]*3, [1]*3, {(0, 1): 1, (0, 2): 1}, 1).report("K23, demand path v2-v1-v3 + u1u2")
    TwoApex(3, [2, 1, 1], [2, 1, 1], {(0, 1): 1, (0, 2): 1, (1, 2): 1}, 1).report("K23, v1 edges doubled")
    TwoApex(3, [1]*3, [1]*3, K(3), 1, c0=0.5).report("K23 + supply u1u2 x0.5")
