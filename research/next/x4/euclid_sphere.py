"""euclid_sphere.py [N, heuristic optimisation]: Euclidean far-leg prices (valid under FH; planar ones under PH).
Maximise |b|^2, b_k = sum_e <u_e, Delta^k_e>, |u_e| = 1, hub distances <= 1 within each merge, b >= 0.
Compare with the Pythagorean-sphere radius^2 E^2."""
import sys, itertools, numpy as np
from scipy.optimize import minimize
exec(open(__file__.replace('euclid_sphere.py','lineprice_sphere.py')).read().split('def run')[0])
def confs():
    B3 = [((0,0,0),(1,1,1)), ((1,0,0),(0,1,1)), ((0,1,0),(1,0,1))]
    D3 = []
    for a in range(3):
        for b in range(3):
            c = (-a-b) % 3; n = (a,b,c); D3.append((n, tuple((x+1) % 3 for x in n)))
    return {'B3': (B3, 2), 'Delta3': (D3, 3)}
def opt(edges, G, p, m, trials, seed):
    rng = np.random.default_rng(seed); E = len(edges); nh = p*G*m
    def unpack(z):
        h = z[:nh].reshape(p, G, m); U = z[nh:].reshape(E, m)
        U = U / np.linalg.norm(U, axis=1, keepdims=True)
        D = np.array([[h[k, hd[k]] - h[k, tl[k]] for k in range(p)] for (tl, hd) in edges])  # E,p,m
        b = np.einsum('em,ekm->k', U, D); return h, b
    cons = [{'type': 'ineq', 'fun': (lambda z, k=k, g=g, g2=g2: 1 - ((z[:nh].reshape(p,G,m)[k,g] - z[:nh].reshape(p,G,m)[k,g2])**2).sum())}
            for k in range(p) for g, g2 in itertools.combinations(range(G), 2)]
    cons += [{'type': 'ineq', 'fun': (lambda z, k=k: unpack(z)[1][k])} for k in range(p)]
    best = (0, None)
    for t in range(trials):
        z = rng.normal(size=nh + E*m)
        r = minimize(lambda z: -(unpack(z)[1]**2).sum(), z, constraints=cons, method='SLSQP', options={'maxiter': 2000})
        h, b = unpack(r.x)
        dmax = max(np.linalg.norm(h[k,g]-h[k,g2]) for k in range(p) for g, g2 in itertools.combinations(range(G), 2))
        if (b >= -1e-6).all() and dmax <= 1 + 1e-6:
            v = float(b @ b)
            if v > best[0]: best = (v, b)
    return best
for name, (edges, G) in confs().items():
    for m in (2, 4, 6):
        v, b = opt(edges, G, 3, m, int(sys.argv[1]) if len(sys.argv) > 1 else 30, m)
        print(f'{name} m={m}: max |b|^2 = {v:.4f} at b = {np.round(b, 4)}; sphere E^2 = {len(edges)**2}', flush=True)
