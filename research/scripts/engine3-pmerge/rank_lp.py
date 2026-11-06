"""rank_lp.py -- what do flattening-RANK inequalities (subadditivity over all cuts, complement symmetry, leg-dimension
bounds, and the four-party inequality rk(BC|AD) <= rk(AB|CD) rk(AC|BD) [Song-Chen-Sun-Hu as read by Majdoddin, Prop. 4.22]
applied to every 4-party coarsening of the 9 nodes) say about the OTHER costs of the row-full piece of Delta_3 under
three merges (rows r, columns c, diagonals r-c)?
Variables h(S) = log2 rank(A; S | V\S) / lambda for all S subset of the 9 nodes.  The CVZ-selected row-full piece has
h(R_r) >= 6 for r = 0,1,2 (Theorem 1 of engine3-delta3-proof.md: product of the three row cuts >= N^18 / T^3).
Cut bound: c_k >= max(max_G h(G), (1/2) sum_G h(G)) over the groups G of merge k.
LP: minimise c_c + c_d (and variants) subject to the inequalities.  Also the two-merge sanity check (min c_c alone -> 0)."""
import itertools, numpy as np, sys
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix
nodes = [(r, c) for r in range(3) for c in range(3)]
n = len(nodes); FULL = (1 << n) - 1
def mask(vs): return sum(1 << nodes.index(v) for v in vs)
rows = [mask([(r, c) for c in range(3)]) for r in range(3)]
cols = [mask([(r, c) for r in range(3)]) for c in range(3)]
diags = [mask([(r, c) for r in range(3) for c in range(3) if (r - c) % 3 == d]) for d in range(3)]
tri = [mask([(r, c) for r in range(3) for c in range(3) if (r + c) % 3 == s]) for s in range(3)]
pop = [bin(S).count('1') for S in range(1 << n)]
NV = (1 << n) + 2   # h(S) for all S, then c_c, c_d
IC, ID = 1 << n, (1 << n) + 1

def build(use_scsh=True):
    rows_A = []; b = []
    def add(coefs, rhs):   # sum coefs <= rhs
        rows_A.append(coefs); b.append(rhs)
    # subadditivity h(S|T) <= h(S) + h(T), S,T disjoint nonempty
    for S in range(1, 1 << n):
        rest = FULL & ~S; T = rest
        while T:
            if T > S: add({S | T: 1, S: -1, T: -1}, 0)
            T = (T - 1) & rest
    if use_scsh:
        # 4-party coarsening (A,B,C,D), blocks may be empty: h(B|C) <= h(A|B) + h(A|C)
        seen = set()
        for assign in itertools.product(range(4), repeat=n):
            A = B = C = D = 0
            for i, a in enumerate(assign):
                if a == 0: A |= 1 << i
                elif a == 1: B |= 1 << i
                elif a == 2: C |= 1 << i
                else: D |= 1 << i
            if not B or not C or not A: continue
            key = (A, min(B, C), max(B, C))
            if key in seen: continue
            seen.add(key)
            co = {}
            co[B | C] = co.get(B | C, 0) + 1; co[A | B] = co.get(A | B, 0) - 1; co[A | C] = co.get(A | C, 0) - 1
            add(co, 0)
    # cost definitions
    for G in cols: add({G: 1, IC: -1}, 0)
    add({**{G: 0.5 for G in cols}, IC: -1}, 0)
    for G in diags: add({G: 1, ID: -1}, 0)
    add({**{G: 0.5 for G in diags}, ID: -1}, 0)
    M = lil_matrix((len(rows_A), NV))
    for i, co in enumerate(rows_A):
        for k, v in co.items(): M[i, k] = v
    # equalities: h(S) = h(~S), h(0)=0
    E = lil_matrix((1 << (n - 1) + 1, NV)); be = np.zeros(E.shape[0]); j = 0
    for S in range(1 << n):
        if S < (FULL & ~S): E[j, S] = 1; E[j, FULL & ~S] = -1; j += 1
    E[j, 0] = 1; j += 1
    return csr_matrix(M), np.array(b), csr_matrix(E[:j]), be[:j]

def solve(M, b, E, be, obj, lower, upper=None):
    bounds = [(lower.get(S, 0.0), 2.0 * pop[S] if upper is None else min(2.0 * pop[S], upper.get(S, 99))) for S in range(1 << n)]
    bounds += [(0, None), (0, None)]
    r = linprog(obj, A_ub=M, b_ub=b, A_eq=E, b_eq=be, bounds=bounds, method='highs')
    return r

if __name__ == '__main__':
    for use_scsh in (False, True):
        M, b, E, be = build(use_scsh)
        print(f'\n=== inequalities: subadditivity + complement symmetry + leg bounds' + (' + SCSH (4-party)' if use_scsh else '') + f'; {M.shape[0]} inequalities', flush=True)
        obj = np.zeros(NV); obj[IC] = 1; obj[ID] = 1
        lower = {R: 6.0 for R in rows}
        r = solve(M, b, E, be, obj, lower)
        print(f'row-full piece (h(R_r) >= 6, r=0,1,2): min c_c + c_d = {r.fun:.4f}  (c_c = {r.x[IC]:.4f}, c_d = {r.x[ID]:.4f})')
        print('   column cuts', [round(r.x[G], 3) for G in cols], ' diagonal cuts', [round(r.x[G], 3) for G in diags],
              ' triangle cuts', [round(r.x[G], 3) for G in tri], ' node cuts', [round(r.x[1 << i], 3) for i in range(n)])
        obj2 = np.zeros(NV); obj2[IC] = 1
        r2 = solve(M, b, E, be, obj2, lower)
        print(f'two-merge sanity (row-full, minimise c_c alone): {r2.fun:.4f}  [Example 4.10 predicts 0]')
        # symmetric target: minimise c_c + c_d with c_c = c_d forced? and the max of h(R_0) given c_c <= a, c_d <= a
        for a in (0.0, 0.5, 1.0, 1.5, 2.0, 2.25, 3.0):
            obj3 = np.zeros(NV); obj3[rows[0]] = -1
            M2 = M; # add c_c <= a, c_d <= a via bounds on IC, ID
            bounds = [(0.0, 2.0 * pop[S]) for S in range(1 << n)] + [(0, a), (0, a)]
            r3 = linprog(obj3, A_ub=M, b_ub=b, A_eq=E, b_eq=be, bounds=bounds, method='highs')
            print(f'   c_c, c_d <= {a}: max h(R_0) = {-r3.fun:.4f}')
