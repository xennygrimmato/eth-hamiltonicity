"""Task B, asymptotics through the merge-1 pairing.  f_C = prod_j F_j (F_j a crossing per pair, see cpieces.py), and
per pair the three merges see the groupings  m1: {x,y}|{u,v} (2 groups),  m0: {x}|{y,v}|{u},  m2: {x,u}|{v}|{y}.
A product identity (one block identity per pair and block, Majdoddin (L2)) gives per-piece cost vectors; a term
is charged min_k sum over its pieces, so rho = max_{mixture p} min_k E_p[c_k] / (2m)  (m bits per block, 2 edges).
Pieces: A_i (m bits, i = #bits taking P=[x=u][y=v], rest B), the rank-counted single-bit identity.
c_flat (lower bound for any network):  c1 = log r_row,  c0 = LP{x},{yv},{u},  c2 = LP{xu},{v},{y}.
c_net upper bound (explicit network: route the single leg x to u's group, then one bond across {x,u}|{y,v}):
          c0 <= min(2m, m + log r_col)  (and 2m by routing both single legs to the middle group)."""
import numpy as np, itertools, math
from scipy.optimize import linprog
from lib import rank_modp, lp_cost
from cpieces import single_bit_pieces
F1, P1, B1 = single_bit_pieces()
def kron4(A, B):
    n = A.shape[0] * B.shape[0]
    return np.einsum('abcd,efgh->aebfcgdh', A, B).reshape(n, n, n, n)
def Ai(m, i):
    S = None
    for Q in itertools.combinations(range(m), i):
        T = None
        for s in range(m):
            f = P1 if s in Q else B1
            T = f if T is None else kron4(T, f)
        S = T if S is None else S + T
    return S
def fl(T, left):  # legs order x,y,u,v = 0,1,2,3
    right = [a for a in range(4) if a not in left]
    return np.transpose(T, list(left) + right).reshape(int(np.prod([T.shape[a] for a in left])), -1)
def costs(T):
    lg = lambda left: math.log2(max(rank_modp(fl(T, left)), 1))
    rx, ry, ru, rv = lg([0]), lg([1]), lg([2]), lg([3]); rrow = lg([0, 1]); rcol = lg([0, 2])
    c0 = max(rx, ru, rcol, (rx + ru + rcol) / 2); c2 = max(ry, rv, rcol, (ry + rv + rcol) / 2)
    return dict(rx=rx, ry=ry, ru=ru, rv=rv, row=rrow, col=rcol, c0=c0, c1=rrow, c2=c2)
def game(vecs):
    """max_p min_k sum_i p_i c_k(i) (LP)"""
    n = len(vecs); K = len(vecs[0])
    A = [[-v[k] for v in vecs] + [1] for k in range(K)]
    res = linprog([0] * n + [-1], A_ub=A, b_ub=[0] * K, A_eq=[[1] * n + [0]], b_eq=[1], bounds=[(0, None)] * (n + 1), method='highs')
    return -res.fun, res.x[:n]
f1 = lambda t, i: sum(math.comb(t, z) * 3 ** z for z in range(i + 1))
for m in range(1, 5):
    vf, vn = [], []
    for i in range(m + 1):
        c = costs(Ai(m, i))
        assert c['row'] == math.log2(f1(m, i)) and abs(c['col'] - math.log2(f1(m, m - i))) < 1e-9 and c['rx'] == m == c['ru'] == c['ry'] == c['rv']
        vf.append((c['c0'], c['c1'], c['c2'])); cn0 = min(2 * m, m + c['col']); vn.append((cn0, c['c1'], cn0))
        print(f"m={m} i={i}: ranks(bits) x,y,u,v={c['rx']:.0f},{c['ry']:.0f},{c['ru']:.0f},{c['rv']:.0f} row={c['row']:.3f} col={c['col']:.3f} | c_flat=(%.3f,%.3f,%.3f) c_net<=(%.3f,%.3f,%.3f)" % (vf[-1] + vn[-1]))
    g1, _ = game(vf); g2, _ = game(vn)
    print(f"  m={m}: rho(c_flat) = {g1/(2*m):.4f}   rho(c_net upper bound) = {g2/(2*m):.4f}", flush=True)
# asymptotics from the verified formulas: r_single = m, row = R(a) m, col = R(1-a) m, R(a) = max_{b<=a} H(b)+b log 3
H = lambda a: 0 if a <= 0 or a >= 1 else -a * math.log2(a) - (1 - a) * math.log2(1 - a)
R = lambda a: H(min(a, .75)) + min(a, .75) * math.log2(3)
grid = [k / 2000 for k in range(2001)]
vf = [(1 + R(1 - a) / 2, R(a), 1 + R(1 - a) / 2) for a in grid]
vn = [(min(2, 1 + R(1 - a)), R(a), min(2, 1 + R(1 - a))) for a in grid]
gf, pf = game(vf); gn, pn = game(vn)
print(f"m->inf (single-bit pieces, rank count): rho(c_flat) = {gf/2:.4f} (support a = {[round(grid[i],3) for i in np.nonzero(pf > 1e-6)[0]]})")
print(f"                                         rho(c_net upper bound) = {gn/2:.4f}")
# ideal per-pair pieces: P-like (row 2m, col 0, single legs m) and B-like (row 0, col 2m)
gi, _ = game([(1, 2, 1), (2, 0, 2)]); print(f"ideal pieces (P-like (m,2m,m), B-like (2m,0,2m)): rho = {gi/2:.4f}")
# App. B pieces: row c_r, col c_c with c_r + c_c = 2 sqrt2 m, both <= 2m, single legs m
vb = [(min(2, 1 + (2 * 2 ** .5 - cr) / 2), cr, min(2, 1 + (2 * 2 ** .5 - cr) / 2)) for cr in [2 * 2 ** .5 - 2 + k * (4 - 2 * 2 ** .5) / 1000 for k in range(1001)]]
gb, _ = game(vb); print(f"App. B-shaped pieces (c_row + c_col = 2 sqrt2 m), c_flat: rho = {gb/2:.4f}")

# ---- rigorous network upper bound with crossing pieces of known (c_row, c_col):
# under merge 0 route x to u's group (bond m bits), then one bond across {x,u}|{y,v} of c_col bits;
# under merge 2 route v to y's group likewise; under merge 1 the pair is a bundle: c_row.
def cnet_game(fam):
    return game([(min(2, 1 + cc), cr, min(2, 1 + cc)) for cr, cc in fam])[0] / 2
seg = [(2 * 2 ** .5 - 2 + k * (4 - 2 * 2 ** .5) / 2000, None) for k in range(2001)]
seg = [(cr, 2 * 2 ** .5 - cr) for cr, _ in seg]
circ = [(min(2, (2 + s) ** .5), min(2, (2 - s) ** .5)) for s in [-2 + 4 * k / 2000 for k in range(2001)]]
print(f"crossing pieces with c_row + c_col <= 2 sqrt2 (Def. 7, rho=1/sqrt2), whole segment, explicit networks: rho_C <= {cnet_game(seg):.4f}")
print(f"App. B profile c_row^2 + c_col^2 = 4 (units lam), explicit networks: rho_C <= {cnet_game(circ):.4f}")
print(f"  same profile, c_flat lower estimate: rho = {game([(1 + cc / 2, cr, 1 + cc / 2) for cr, cc in circ])[0] / 2:.4f}")
seg11 = [(cr, 11 / 3 - cr) for cr in [5 / 3 + k * (1 / 3) / 1000 for k in range(1001)]]
print(f"Lemma 2 (eight-square, c_row + c_col <= 11/3 lam), explicit networks: rho_C <= {cnet_game(seg11):.4f}")
for rx in (0.5, 0.75, 0.8536, 0.9):
    fam = [(cr, 4 * rx - cr) for cr in [max(0, 4 * rx - 2) + k * (2 - max(0, 4 * rx - 2)) / 1000 for k in range(1001)]]
    print(f"  generic crossing pieces with parameter rho_x={rx}: rho_C <= {cnet_game(fam):.4f}")
