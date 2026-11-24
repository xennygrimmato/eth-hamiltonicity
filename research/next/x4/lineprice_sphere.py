"""lineprice_sphere.py [N]: 1D (segment) prices, far-leg limit, b_k = sum_e u_e (h_k(head)-h_k(tail)), hubs in [0,1].
Segments are prices over every field (b2 §3 (ii)), so every b found is an UNCONDITIONAL lower bound: some piece has
c_k >= lambda*b_k for all k at once.  We report max |b|^2 and compare with E^2 = p*(E/sqrt p)^2, the squared radius of
the 'Pythagorean sphere' sum_k c_k^2 = const on which a floor-matching (1/sqrt p) Fock-type family would have to lie."""
import itertools, numpy as np
def run(name, edges, ngroups, p):
    # edges: list of tuples (tail groups per merge, head groups per merge)
    best = (-1, None); bestsum = (-1, None)
    hub_choices = [list(itertools.product([0.0, 1.0], repeat=ngroups[k])) for k in range(p)]
    for H in itertools.product(*hub_choices):
        D = np.array([[H[k][hd[k]] - H[k][tl[k]] for k in range(p)] for (tl, hd) in edges])  # E x p
        for u in itertools.product([1, -1], repeat=len(edges)):
            b = (np.array(u)[:, None] * D).sum(0)
            if (b < 0).any(): continue
            n2 = float(b @ b)
            if n2 > best[0]: best = (n2, b.copy())
            if b.sum() > bestsum[0]: bestsum = (b.sum(), b.copy())
    E = len(edges)
    print(f'{name}: E={E}, p={p}: max |b|^2 = {best[0]} at b={best[1]}; sphere radius^2 E^2 = {E*E}; '
          f'max sum b = {bestsum[0]} at {bestsum[1]} (floor-matching needs sum {E*np.sqrt(p):.3f})')
# B3: three of the four long diagonals of the cube, plane merges (2 groups each)
B3 = [((0,0,0),(1,1,1)), ((1,0,0),(0,1,1)), ((0,1,0),(1,0,1))]
run('B3 (three-wire cube)', B3, [2,2,2], 3)
BOX = B3 + [((0,0,1),(1,1,0))]
run('box (four wires)', BOX, [2,2,2], 3)
RECT = [((0,0),(1,1)), ((0,1),(1,0))]
run('rectangle', RECT, [2,2], 2)
# Delta_3: nodes (a,b,c) in Z3^3 with a+b+c=0, edge n -> n+(1,1,1); merge k = coordinate k
D3 = []
for a in range(3):
    for b in range(3):
        c = (-a-b) % 3; n = (a,b,c); m = tuple((x+1) % 3 for x in n); D3.append((n, m))
run('Delta3 (rows/cols/diags)', D3, [3,3,3], 3)
