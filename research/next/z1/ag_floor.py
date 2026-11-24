"""Route 2: floors for a level on AG(2,g) with p parallel classes as merges, ALL edges of K_{g^2} as one configuration,
including edges internal to a merge (edge of class c costs 0 under merge c).

Price method (b2 notebook, (*) and far-leg reduction): a price with hubs h^k_G (merge k, group G), |h^k_G-h^k_G'| <= 1,
legs of edge e at +-M u_e gives one piece with c_k >= lambda * b_k, b_k = sum_e <u_e, Delta^k_e>, Delta^k_e = h^k(G_k(u)) -
h^k(G_k(v)) (0 if e is internal to merge k).  PGammaL(2,g) acts transitively on any p-set of classes for g <= 5 (3-transitive
on the projective line; p-sets for p >= g-1 are complements of <= 2-sets), so averaging gives V >= (sum_k b_k)/p and
rho >= sum_k b_k / (p E),  sum_k b_k <= sum_e |sum_k Delta^k_e| (= with optimal u_e).

Outputs per (g,p):
 orth   : orthogonal regular-simplex construction, closed form [R|FH]
 cs     : Cauchy-Schwarz upper bound on what the far-leg Euclidean method can certify (cross terms vanish, see notebook)
 euclid : numerical optimum of the far-leg Euclidean method (SLSQP, restarts)  [N, heuristic]
 line   : best far-leg LINE price (hubs binary, exhaustive or local search)  [unconditional: R1 subsets are prices]
 star   : pigeonhole / star price g/((g+1)p)  [unconditional, every field]
 sep    : flat floor if merge-class edges are separate raw configurations (Route 2 as first stated)
"""
import itertools, sys, numpy as np
from scipy.optimize import minimize

def field(g):
    if g in (2, 3, 5):
        add = lambda a, b: (a + b) % g; mul = lambda a, b: (a * b) % g; neg = lambda a: (-a) % g
        return add, mul, neg
    if g == 4:  # GF(4) = {0,1,w,w^2} as 0,1,2,3; addition = xor
        M = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
        return (lambda a, b: a ^ b), (lambda a, b: M[a][b]), (lambda a: a)
    raise ValueError

def plane(g):
    add, mul, neg = field(g)
    pts = [(x, y) for x in range(g) for y in range(g)]
    classes = []   # class = function point -> line label
    for s in range(g):
        classes.append(lambda P, s=s: add(P[1], neg(mul(s, P[0]))))
    classes.append(lambda P: P[0])
    lab = np.array([[cl(P) for P in pts] for cl in classes])  # (g+1) x g^2
    E = [(i, j) for i in range(len(pts)) for j in range(i + 1, len(pts))]
    ecls = []
    for (i, j) in E:
        cs = [c for c in range(g + 1) if lab[c, i] == lab[c, j]]
        assert len(cs) == 1
        ecls.append(cs[0])
    return pts, lab, E, np.array(ecls)

def orth_closed(g, p):
    return (np.sqrt(p - 1) + (g + 1 - p) / np.sqrt(p)) / (g + 1)

def cs_bound(g, p):
    return np.sqrt(g / (p * (g + 1)))

def sep_floor(g, p):
    return ((p - 1) + (g + 1 - p) / np.sqrt(p)) / (g + 1)

def far_value(h, lab, E, ks):
    # h: list over merges of (g, m) arrays
    tot = 0.0
    for (i, j) in E:
        s = sum(h[a][lab[k, i]] - h[a][lab[k, j]] for a, k in enumerate(ks))
        tot += np.linalg.norm(s)
    return tot

def euclid_opt(g, p, lab, E, m, trials, seed=0):
    ks = list(range(p)); rng = np.random.default_rng(seed)
    I = np.array([e[0] for e in E]); J = np.array([e[1] for e in E])
    def F(z):
        H = z.reshape(p, g, m)
        s = np.zeros((len(E), m))
        for a, k in enumerate(ks):
            s += H[a][lab[k, I]] - H[a][lab[k, J]]
        return -np.sqrt((s * s).sum(1) + 1e-12).sum()
    cons = []
    for a in range(p):
        for G, G2 in itertools.combinations(range(g), 2):
            cons.append({'type': 'ineq', 'fun': (lambda z, a=a, G=G, G2=G2:
                         1 - ((z.reshape(p, g, m)[a, G] - z.reshape(p, g, m)[a, G2]) ** 2).sum())})
    best = 0
    for t in range(trials):
        z = rng.normal(size=p * g * m) * 0.5
        r = minimize(F, z, constraints=cons, method='SLSQP', options={'maxiter': 500})
        H = r.x.reshape(p, g, m)
        dmax = max(np.linalg.norm(H[a, G] - H[a, G2]) for a in range(p) for G, G2 in itertools.combinations(range(g), 2))
        val = -F(r.x) / dmax
        best = max(best, val)
    return best

def line_value(s, lab, E, ks):
    # s: p x g binary; S(u) = sum_k s[k][lab[k,u]]
    S = sum(s[a][lab[k]] for a, k in enumerate(ks))
    vals, cnt = np.unique(S, return_counts=True)
    # sum over unordered pairs |S_u - S_v|
    tot = 0
    for x in range(len(vals)):
        for y in range(x + 1, len(vals)):
            tot += cnt[x] * cnt[y] * abs(vals[x] - vals[y])
    return tot

def line_opt(g, p, lab, E, seed=0):
    ks = list(range(p)); nb = g * p
    if nb <= 20:
        best = 0
        for bits in range(1 << nb):
            s = np.array([(bits >> b) & 1 for b in range(nb)]).reshape(p, g)
            best = max(best, line_value(s, lab, E, ks))
        return best, 'exh'
    rng = np.random.default_rng(seed); best = 0
    for t in range(400):
        s = rng.integers(2, size=(p, g)); cur = line_value(s, lab, E, ks)
        improved = True
        while improved:
            improved = False
            for a in range(p):
                for G in range(g):
                    s[a, G] ^= 1; v = line_value(s, lab, E, ks)
                    if v > cur: cur = v; improved = True
                    else: s[a, G] ^= 1
        best = max(best, cur)
    return best, 'ls400'

if __name__ == '__main__':
    gs = [int(x) for x in sys.argv[1:]] or [2, 3, 4, 5]
    print('g p  E   orth[R|FH]  cs(method cap)  euclid[N]  line[uncond]  star[uncond]  sep  1/sqrt(p)  alpha_orth')
    for g in gs:
        pts, lab, E, ecls = plane(g)
        nE = len(E)
        for p in range(2, g + 2):
            o = orth_closed(g, p); c = cs_bound(g, p)
            m = min(p * (g - 1), 8)
            eu = euclid_opt(g, p, lab, E, m, trials=6 if g >= 4 else 12) / (p * nE)
            lv, how = line_opt(g, p, lab, E)
            ln = lv / (p * nE)
            st = g / ((g + 1) * p)
            print(f'{g} {p} {nE:3d}  {o:.4f}      {c:.4f}          {eu:.4f}     {ln:.4f}({how})  {st:.4f}  '
                  f'{sep_floor(g,p):.4f}  {1/np.sqrt(p):.4f}  {np.log2(1/o):.3f}', flush=True)
