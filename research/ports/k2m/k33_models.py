"""[N] K_{3,3} (and any instance): minimise the ratio over configurations in (star)^k x R^d, each point on its own
leg of each star factor: d_ij^2 = sum_f (r_fi + r_fj)^2 + |h_i - h_j|^2.  These are finite subsets of products of
pods and flats (CAT(0)); a subclass of products of trees."""
import itertools, numpy as np, sys
from scipy.optimize import minimize
def make(n, sup, dem, k, d):
    pr = list(itertools.combinations(range(n), 2))
    I = np.array([p[0] for p in pr]); J = np.array([p[1] for p in pr])
    c = np.array([sup.get(p, 0.0) for p in pr]); r = np.array([dem.get(p, 0.0) for p in pr])
    def ratio(x):
        R = np.abs(x[:k*n]).reshape(k, n); H = x[k*n:].reshape(d, n) if d else np.zeros((0, n))
        D2 = ((R[:, I] + R[:, J])**2).sum(0) + ((H[:, I] - H[:, J])**2).sum(0)
        D = np.sqrt(D2 + 1e-300)
        return (c @ D)/(r @ D)
    return ratio
def run(n, sup, dem, k, d, starts=300, seed=0):
    rng = np.random.default_rng(seed); f = make(n, sup, dem, k, d); best = (np.inf, None)
    for s in range(starts):
        x0 = np.concatenate([rng.exponential(1.0, k*n)*(rng.random(k*n) < 0.6), rng.normal(0, 1, d*n)])
        res = minimize(f, x0, method='L-BFGS-B'); res = minimize(f, res.x, method='Powell', options=dict(xtol=1e-10, ftol=1e-13))
        if res.fun < best[0]: best = (res.fun, res.x)
    return best
if __name__ == "__main__":
    n = 6; sup = {(i, j): 1.0 for i in (0, 1, 2) for j in (3, 4, 5)}
    dem = {p: 1.0 for p in itertools.combinations(range(n), 2) if p not in sup}
    for k, d in ((1, 1), (2, 0), (2, 1), (3, 1), (2, 2)):
        v, x = run(n, sup, dem, k, d, starts=150)
        print(f"K33 in (star)^{k} x R^{d}: min ratio = {v:.6f}", flush=True)
    # control: K_{2,3} must give 3/sqrt(10) in star x R
    sup = {(i, j): 1.0 for i in (0, 1) for j in (2, 3, 4)}
    dem = {p: 1.0 for p in itertools.combinations(range(5), 2) if p not in sup}
    print("control K23 in star x R:", run(5, sup, dem, 1, 1, starts=60)[0])
