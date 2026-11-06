"""cu3m.py -- Cohn-Umans / CKSU Fourier pieces on Delta_3 at N0 = 2 (from ../engine3-cu/fourier_pieces.py, copied as fp_lib.py)
charged under THREE merges.  fp_lib conventions: node (l,s) = grid node (r,c) = (l, s-l); row = l, column = s-l,
diagonal r - c = 2l - s (mod 3).  For each piece: flattening ranks of the three groups of each merge, D1 cut lower bounds
(c_k >= max(max_g log rk, 1/2 sum log rk)), and the q-game value of the family (+ 1.5 log2 T naming at N0 = 2).  [C exact ranks]"""
import numpy as np, itertools, time
from scipy.optimize import linprog
import fp_lib as F
def axes_diag(d):
    return [F.AXI[((l, s), sl)] for l in range(3) for s in range(3) if (2 * l - s) % 3 == d for sl in range(2)]
assert sorted(sum([axes_diag(d) for d in range(3)], [])) == list(range(18))
def cut3(T):
    out = []
    for axf in (F.axes_row, F.axes_col, axes_diag):
        rk = [F.frank(T, axf(g)) for g in range(3)]
        lr = np.log2(np.maximum(rk, 1)); out.append((rk, max(lr.max(), lr.sum() / 2)))
    return out
def game(vecs):
    V = np.array(vecs, float); n = len(V)
    r = linprog(np.r_[np.zeros(3), 1], A_ub=np.hstack([V, -np.ones((n, 1))]), b_ub=np.zeros(n),
                A_eq=[[1, 1, 1, 0]], b_eq=[1], bounds=[(0, None)] * 3 + [(None, None)], method='highs')
    return r.fun, np.round(r.x[:3], 3)
t0 = time.time()
f = F.f_delta(); print('f_Delta three-merge ranks:', [c[0] for c in cut3(f)])
print('\n(P) S_3^3 product pieces (one TPP <2,2,2> per triangle):')
vec = []
for names in itertools.product(F.S3_IRR, repeat=3):
    A = F.product_piece(names); c = cut3(A); vec.append([x[1] for x in c])
    if names in [('triv',) * 3, ('std', 'triv', 'triv'), ('std', 'std', 'triv'), ('std',) * 3]:
        print(f'  {str(names):28s} ranks r/c/d {[x[0] for x in c]}  cut bounds {[round(x[1], 3) for x in c]}')
v, q = game(vec); print(f'  27 product pieces: game value (cut bounds) {v:.4f} at q {q}; V_tot >= {v + 1.5*np.log2(27):.3f} (trade needs < 9)')
print('\n(C) CKSU G = (Cyc_3^3)^2 x| Cyc_2, coordinatewise identification, 405 Fourier pieces (row networks of cost <= 3 log2 d):')
MT = F.build_mult_table(); S, T_, U = F.cksu_subset(0), F.cksu_subset(1), F.cksu_subset(2)
w = F.row_words(MT, S, T_, U, list(range(8)), list(range(8)), list(range(8)))
acc = 0; vec2 = {1: [], 2: []}; rk_hist = {1: {}, 2: {}}
for (lab, d, chi) in F.chars_G():
    A = (d / 1458) * chi[w]; acc = acc + A
    if np.abs(A).max() < 1e-12: continue
    c = cut3(A); vec2[d].append([x[1] for x in c])
    key = tuple(tuple(x[0]) for x in c); rk_hist[d][key] = rk_hist[d].get(key, 0) + 1
print('  sum == f_Delta:', np.allclose(acc, f), f'({time.time()-t0:.0f}s)')
for d in (1, 2):
    V = np.array(vec2[d])
    print(f'  degree {d}: {len(V)} pieces; cut bounds c_r in [{V[:,0].min():.2f},{V[:,0].max():.2f}] c_c in [{V[:,1].min():.2f},{V[:,1].max():.2f}] '
          f'c_d in [{V[:,2].min():.2f},{V[:,2].max():.2f}]; sum c_r+c_c+c_d in [{V.sum(1).min():.2f},{V.sum(1).max():.2f}]')
    for key, n in sorted(rk_hist[d].items(), key=lambda t: -t[1])[:6]:
        print(f'     {n:4d} pieces with ranks rows {key[0]} cols {key[1]} diags {key[2]}')
allv = vec2[1] + vec2[2]
# the row network bound (3 log2 d) is an upper bound on c_r; use max(cut, ...) lower bounds for the game
v, q = game(allv)
print(f'  family game value with cut lower bounds: {v:.4f} at q {q};  T = 405 types: V_tot >= {v + 1.5*np.log2(405):.3f} (trade needs < 9)')
v2, q2 = game(vec2[2]); print(f'  degree-2 pieces alone: game (lower) {v2:.4f} at q {q2}')
print(f'done {time.time()-t0:.0f}s')
