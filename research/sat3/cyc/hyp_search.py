"""One-factor ratio Gamma of Delta_3 in the hyperbolic plane H^2 (curvature -1), far legs.

Hubs: 9 points of the Poincare disc, labelled by AG(2,3) (hub (u,v) -> 3u+v, class u).
Edge (n,n'), legs to the ends xi+, xi- of a geodesic line:
   sum of savings = sum_{h in n} log P(h,xi+) + sum_{h' in n'} log P(h',xi-) + 6 log(|xi+ - xi-|/2),
   P(z,xi) = (1-|z|^2)/|z-xi|^2   (Busemann functions; the last term is -2*3*(Gromov product at 0)).
Gamma = sum_e c_e^2 / mean same-class d^2.  Records: flat 27, trees 36, cap 40.5.
Small configurations are Euclidean (27), large ones tree-like (-> 36 from below for the tripod).
The maximum over (xi+,xi-) is taken on a grid (a lower bound for c_e).
"""
import numpy as np, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
G = int(sys.argv[2]) if len(sys.argv) > 2 else 180
ITERS = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
th = np.linspace(0, 2*np.pi, G, endpoint=False)
xi = np.exp(1j*th)
LG = 6*np.log(np.maximum(np.abs(xi[:, None]-xi[None, :])/2, 1e-300))
nodes = [[3*u + (i + t*u) % 3 for u in range(3)] for t in range(3) for i in range(3)]
edges = [(3*t+i, 3*t+(i+1) % 3) for t in range(3) for i in range(3)]
pairs = [(3*u+v, 3*u+w) for u in range(3) for v in range(3) for w in range(v+1, 3)]

def hubs_of(par):               # par: 9 x 2 = (radius R >= 0 hyperbolic, angle)
    R = np.abs(par[:, 0]); return np.tanh(R/2)*np.exp(1j*par[:, 1])
def dist(z, w):
    return np.arccosh(1 + 2*abs(z-w)**2/((1-abs(z)**2)*(1-abs(w)**2)))
def gamma(par):
    z = hubs_of(par)
    logP = np.log((1-np.abs(z)**2)[:, None]/np.abs(z[:, None]-xi[None, :])**2)   # 9 x G
    S = 0.0
    for (a, b) in edges:
        Fp = logP[nodes[a]].sum(0); Fm = logP[nodes[b]].sum(0)
        c = (Fp[:, None] + Fm[None, :] + LG).max()
        if c > 0: S += c*c
    D = np.mean([dist(z[a], z[b])**2 for a, b in pairs])
    return S/D if D > 1e-12 else 0.0

# calibration: tripod-like configuration at scale R
for R in (0.01, 1.0, 5.0, 20.0, 80.0):
    par = np.zeros((9, 2)); 
    for u in range(3): par[3*u] = (R, 2*np.pi*u/3)
    print("tripod-like, R =", R, "Gamma =", round(gamma(par), 4))
best = 0; 
for rep in range(6):
    scale = [0.1, 1.0, 3.0, 10.0, 30.0, 100.0][rep]
    par = np.column_stack([scale*rng.random(9), 2*np.pi*rng.random(9)])
    cur = gamma(par); T0 = 1.0
    for it in range(ITERS):
        T = T0*(1e-3)**(it/ITERS)
        new = par.copy(); h = rng.integers(9)
        if rng.random() < 0.5: new[h, 0] = abs(new[h, 0]*np.exp(0.2*rng.normal()) + 0.02*scale*rng.normal())
        else: new[h, 1] += rng.normal()*0.3
        if rng.random() < 0.05: new[h, 0] = 0
        g = gamma(new)
        if g >= cur or rng.random() < np.exp((g-cur)/T): par, cur = new, g
    print("start scale", scale, "final Gamma", round(cur, 4), "radii", np.round(np.abs(par[:, 0]), 2))
    best = max(best, cur)
print("BEST", best)
