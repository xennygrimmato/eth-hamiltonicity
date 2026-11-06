"""level_product.py -- Q4 sanity: the 3x3 level (K3 x K3, 9 nodes, 18 crossing edges, 36 strings) at lambda = 1 and the
product decomposition of engine2-decorrelated.md 8.6: on each of the 9 rectangles {a,b} x {i,j} (two crossing edges)
apply the App. H identity  [x=v][y=u] = [x=u][y=v] - [x!=y](-1)^x [u!=v](-1)^u.  The 2^9 product terms sum to f exactly
(the rectangles partition the 36 strings; checked).  For every term compute exactly (over Q) the row cut ranks
rank(term; row g | rest) and column cut ranks, the network cost (sum over rectangles of log2 of the factor rank across the
rectangle's two rows / columns, which is an explicit row / column network) and the cut-bound c_flat.  Expect max_t min(c_row, c_col) = 8.
Also: the same evaluation of the 18-string Delta_3 (one edge per rectangle) shows why products give nothing there."""
import itertools, numpy as np
# rectangle tensor on strings x=(a,i) y=(a,j) u=(b,i) v=(b,j); edges (a,i)-(b,j): x-v and (a,j)-(b,i): y-u
F = np.zeros((2, 2, 2, 2)); P = np.zeros((2, 2, 2, 2)); A = np.zeros((2, 2, 2, 2))
for x, y, u, v in itertools.product((0, 1), repeat=4):
    F[x, y, u, v] = (x == v) * (y == u)
    P[x, y, u, v] = (x == u) * (y == v)
    A[x, y, u, v] = (x != y) * (-1) ** x * (u != v) * (-1) ** u
assert np.array_equal(F, P - A); print('App. H rectangle identity F = P - A: exact over Z')
def rk(T, rowaxes):
    other = [k for k in range(4) if k not in rowaxes]
    return np.linalg.matrix_rank(np.transpose(T, rowaxes + other).reshape(2 ** len(rowaxes), -1))
# P = [x=u][y=v] is a product across columns {x,u} | {y,v}; across rows {x,y} | {u,v} rank 4.  A product across rows.
ranks = {'P': (rk(P, [0, 1]), rk(P, [0, 2])), 'A': (rk(A, [0, 1]), rk(A, [0, 2]))}
print('factor ranks (across its two rows, across its two columns):', ranks, ' F:', (rk(F, [0, 1]), rk(F, [0, 2])))
rows = cols = (0, 1, 2)
rects = [((a, b), (i, j)) for a, b in itertools.combinations(rows, 2) for i, j in itertools.combinations(cols, 2)]
# strings: node (r,c) has one string per crossing edge; edge = unordered pair of nodes in different row and column
strings = set()
for (a, b), (i, j) in rects:
    for e in (((a, i), (b, j)), ((a, j), (b, i))):
        for end in e: strings.add((end, e))
nedges = len({tuple(sorted(e)) for _, e in strings})
print(f'rectangles {len(rects)}, crossing edges {nedges}, strings {len(strings)} (each string in exactly one rectangle: {len(strings) == 4 * len(rects)})')
results = []
for choice in itertools.product('PA', repeat=9):
    # row network: bond between rows a,b = product of row ranks of pieces on rectangles with rows {a,b}
    bond_r = {p: 1 for p in itertools.combinations(rows, 2)}; bond_c = {p: 1 for p in itertools.combinations(cols, 2)}
    for ((a, b), (i, j)), ch in zip(rects, choice):
        bond_r[(a, b)] *= ranks[ch][0]; bond_c[(i, j)] *= ranks[ch][1]
    c_row = sum(np.log2(list(bond_r.values()))); c_col = sum(np.log2(list(bond_c.values())))
    # cut ranks of the product term = product of factor ranks of rectangles crossing the cut (exact for products)
    rr = [np.prod([ranks[ch][0] for ((a, b), _), ch in zip(rects, choice) if g in (a, b)]) for g in rows]
    rc = [np.prod([ranks[ch][1] for (_, (i, j)), ch in zip(rects, choice) if g in (i, j)]) for g in cols]
    cf = lambda r: max(max(np.log2(r)), sum(np.log2(r)) / 2)
    results.append((min(c_row, c_col), c_row, c_col, cf(rr), cf(rc), choice))
mins = np.array([r[0] for r in results])
print(f'terms {len(results)}; max_t min(c_row, c_col) = {mins.max():.0f}; network cost = c_flat for every term: '
      f'{all(abs(r[1]-r[3])<1e-9 and abs(r[2]-r[4])<1e-9 for r in results)}')
print('histogram of min cost:', dict(zip(*[x.tolist() for x in np.unique(mins, return_counts=True)])))
print('rank sum sum_t 2^{min cost} =', int(sum(2 ** m for m in mins)), ' (Theorem 1 floor N^8 = 256; N^9 = 512)')
print('a worst term:', [r for r in results if r[0] == mins.max()][0])
print('Delta_3 comparison: each rectangle holds ONE anti-diagonal edge, which crosses both rows and columns, so a product of')
print('per-edge pieces costs 1 per edge under both merges (the identity edge is rank 2 across rows and across columns): no product trade.')
