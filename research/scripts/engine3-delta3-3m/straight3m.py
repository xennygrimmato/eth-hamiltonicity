"""straight3m.py -- the straightened-edge family of engine3-delta3-proof.md Sec. 5 charged under THREE merges, at N0 = 2 [C exact
ranks], plus its two other orientations (straighten a row pair into vertical edges, or a diagonal-class... see below).
R = (u_0 x u_1 x u_2) (x) I^{(x)6}, u_r = I on the two gamma-legs of row r (gamma = a column pair), i.e. the graph tensor of Delta_3
with the three gamma-edges replaced by horizontal edges (r,c)-(r,c');  C = f - R.
For every piece and merge: the three group flattening ranks, the D1 cut lower bound max(max_g log rk, 1/2 sum log rk), and
the construction upper bound.  Then the q-game value of {R, C} (min_q max_i <q, c_i>) with lower / upper cost vectors, and the
fixed-alphabet V_tot = game + 1.5 log2 T (T = 2)."""
import numpy as np, itertools
from scipy.optimize import linprog
from d3lib import delta3, flat_rank, to3
cfg = delta3(); f = cfg.target()
S = cfg.S
def graph_tensor(pairs):
    """pairs: list of (string a, string b) perfect matching of the 18 strings -> tensor with [x_a = x_b] for each pair."""
    T = np.zeros((2,) * S)
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        idx = [0] * S
        for (a, b), x in zip(pairs, bits): idx[a] = x; idx[b] = x
        T[tuple(idx)] = 1
    return T
orig = []
for i, (u, v) in enumerate(cfg.edges):
    orig.append((cfg.sidx[(u, i)], cfg.sidx[(v, i)]))
def straighten(kind, pair):
    """reroute the three edges whose endpoints lie in the given pair of groups of `kind` so that each new edge joins the two
    endpoints lying in the same group of a DIFFERENT merge `tgt` (rows for a column pair, etc.).  Returns new matching."""
    fn = {'row': lambda v: v[0], 'col': lambda v: v[1], 'diag': lambda v: (v[0] - v[1]) % 3}
    tgt = {'col': 'row', 'row': 'col', 'diag': 'row'}[kind]
    sel = [i for i, (u, v) in enumerate(cfg.edges) if {fn[kind](u), fn[kind](v)} == set(pair)]
    assert len(sel) == 3
    keep = [orig[i] for i in range(9) if i not in sel]
    # strings of the selected edges: side A = endpoint in group pair[0], side B = in pair[1]
    A = {}; B = {}
    for i in sel:
        u, v = cfg.edges[i]
        a, b = (u, v) if fn[kind](u) == pair[0] else (v, u)
        A[fn[tgt](a)] = cfg.sidx[(a, i)]; B[fn[tgt](b)] = cfg.sidx[(b, i)]
    new = [(A[g], B[g]) for g in range(3)]
    return keep + new, sel
def costs(T):
    out = {}
    for k in ('row', 'col', 'diag'):
        T3 = to3(cfg, T.reshape(cfg.gdims_row), k)
        rk = [int(flat_rank(T3, i)) for i in range(3)]
        lr = np.log2(rk)
        out[k] = (rk, max(lr.max(), lr.sum() / 2))
    return out
def game(vecs):
    V = np.array(vecs, float); n = len(V)
    r = linprog(np.r_[np.zeros(3), 1], A_ub=np.hstack([V, -np.ones((n, 1))]), b_ub=np.zeros(n),
                A_eq=[[1, 1, 1, 0]], b_eq=[1], bounds=[(0, None)] * 3 + [(None, None)], method='highs')
    return r.fun, r.x[:3]
if __name__ == '__main__':
    print('f_Delta:', costs(f))
    for kind, pair in (('col', (0, 1)), ('row', (0, 1)), ('diag', (0, 1))):
        m, sel = straighten(kind, pair)
        R = graph_tensor(m); C = f - R
        cR, cC = costs(R), costs(C)
        print(f'\nstraighten the {kind}-pair {pair} edges {sel}:')
        for nm, cc in (('R', cR), ('C = f - R', cC)):
            print(f'  {nm:10s} ' + '  '.join(f'{k}: ranks {cc[k][0]} cut>= {cc[k][1]:.3f}' for k in cc))
        lo = [[cR[k][1] for k in cR], [cC[k][1] for k in cC]]
        # construction upper bounds at N = 2: R is a graph tensor (exact cost = crossing edges); C = (Pi - I) (x) I^6:
        #   under the merge of the pair: 6 + log2 rank(Pi - I) (one bond);  other merges: R-part + I-part summed bonds.
        v, q = game(lo)
        print(f'  game value with cut lower bounds: {v:.4f} at q = {np.round(q, 3)};  V_tot (T = 2) >= {v + 1.5:.4f}  (trade needs < 9)')
        print(f'  cost-vector sums: R {sum(lo[0]):.3f}, C {sum(lo[1]):.3f}  (uniform-q rho<1/2 needs every sum < 13.5 - 4.5 log2 T)')
    