"""entropy_lp.py -- Shannon-type test of the 'quantitative Lemma 7.2' on Delta_3 with three orthogonal merges.
For a tensor whose flattening ranks are support mutual informations (code tensors [x in L], graph tensors, every
diagonal piece r(x)[x=y] in the edge basis), h(S) = I(X_S : X_{S^c}) for the uniform distribution on the support.
Question: is  2 I(R_0 : R_0^c) <= sum_c I(col_c : col_c^c) + sum_d I(diag_d : diag_d^c)   a Shannon inequality on 9 variables
(one variable per node, H(v) <= 2 lambda for two legs)?  And the weaker form needed for rho >= 1/2 on Delta_3:
   row-full (I(R_r : R_r^c) >= 6 for r = 0,1,2)  ==>  c_c + c_d >= 4.5,   c_k >= max(max_G I(G), (1/2) sum_G I(G)).
LP over the 2^9 entropy values with all elemental Shannon inequalities (monotonicity + conditional MI >= 0) [Yeung].
Also: the Ingleton-free check for the 2x2 case (SCSH's entropy version) and the 2-merge sanity (min c_c alone)."""
import itertools, numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix
nodes = [(r, c) for r in range(3) for c in range(3)]
n = len(nodes); FULL = (1 << n) - 1
def mask(vs): return sum(1 << nodes.index(v) for v in vs)
rows = [mask([(r, c) for c in range(3)]) for r in range(3)]
cols = [mask([(r, c) for r in range(3)]) for c in range(3)]
diags = [mask([(r, c) for r in range(3) for c in range(3) if (r - c) % 3 == d]) for d in range(3)]
NV = (1 << n) + 2; IC, ID = 1 << n, (1 << n) + 1

def elemental():
    rows_A = []
    def add(co): rows_A.append(co)
    # monotonicity: H(V) - H(V \ i) >= 0  ->  H(V\i) - H(V) <= 0
    for i in range(n): add({FULL & ~(1 << i): 1, FULL: -1})
    # I(i;j|K) >= 0: H(iK) + H(jK) - H(ijK) - H(K) >= 0 -> -H(iK) - H(jK) + H(ijK) + H(K) <= 0
    for i in range(n):
        for j in range(i + 1, n):
            rest = FULL & ~(1 << i) & ~(1 << j); K = rest
            while True:
                co = {}
                for S, v in (((1 << i) | K, -1), ((1 << j) | K, -1), ((1 << i) | (1 << j) | K, 1), (K, 1)):
                    co[S] = co.get(S, 0) + v
                add(co)
                if K == 0: break
                K = (K - 1) & rest
    return rows_A

def MI(S):   # coefficients of I(S : S^c) = H(S) + H(S^c) - H(V)
    return {S: 1, FULL & ~S: 1, FULL: -1}

def build(extra):
    rows_A = elemental()
    for G in cols:
        co = {k: v for k, v in MI(G).items()}; co[IC] = co.get(IC, 0) - 1; rows_A.append(co)
    co = {}
    for G in cols:
        for k, v in MI(G).items(): co[k] = co.get(k, 0) + 0.5 * v
    co[IC] = -1; rows_A.append(co)
    for G in diags:
        co = {k: v for k, v in MI(G).items()}; co[ID] = co.get(ID, 0) - 1; rows_A.append(co)
    co = {}
    for G in diags:
        for k, v in MI(G).items(): co[k] = co.get(k, 0) + 0.5 * v
    co[ID] = -1; rows_A.append(co)
    rows_A += extra
    M = lil_matrix((len(rows_A), NV)); b = np.zeros(len(rows_A))
    for i, co in enumerate(rows_A):
        for k, v in co.items(): M[i, k] += v
    return csr_matrix(M), b

def run(obj, extra=(), legs=2.0, eq=None):
    M, b = build(list(extra))
    bounds = [(0, legs * bin(S).count('1')) for S in range(1 << n)] + [(0, None), (0, None)]
    bounds[0] = (0, 0)
    A_eq = None; b_eq = None
    if eq:
        A_eq = lil_matrix((len(eq), NV)); b_eq = []
        for i, (co, rhs) in enumerate(eq):
            for k, v in co.items(): A_eq[i, k] += v
            b_eq.append(rhs)
        A_eq = csr_matrix(A_eq)
    r = linprog(obj, A_ub=M, b_ub=b, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
    return r

if __name__ == '__main__':
    # (1) Q*: max of 2 I(R_0) - sum_c I(col) - sum_d I(diag) over the Shannon cone (with H(v) <= 2): 0 means Q* is Shannon-type
    obj = np.zeros(NV)
    for k, v in MI(rows[0]).items(): obj[k] -= 2 * v
    for G in cols + diags:
        for k, v in MI(G).items(): obj[k] += v
    r = run(obj)
    print(f'(1) max [2 I(R_0:rest) - sum_c I(col_c) - sum_d I(diag_d)] over Shannon cone = {-r.fun:.6f}   (0 <=> Q* is a Shannon inequality)')
    # (2) row-full code tensor: min c_c + c_d
    extra = []
    for R in rows:
        co = {k: -v for k, v in MI(R).items()}; extra.append(co)   # -I(R) <= -6
    M, b = build(extra); b[-3:] = -6.0
    obj2 = np.zeros(NV); obj2[IC] = 1; obj2[ID] = 1
    bounds = [(0, 2.0 * bin(S).count('1')) for S in range(1 << n)] + [(0, None), (0, None)]; bounds[0] = (0, 0)
    r2 = linprog(obj2, A_ub=M, b_ub=b, bounds=bounds, method='highs')
    print(f'(2) row-full (I(R_r) >= 6, r = 0,1,2): min c_c + c_d = {r2.fun:.4f} (c_c = {r2.x[IC]:.4f}, c_d = {r2.x[ID]:.4f});'
          f' column MIs {[round(sum(v*r2.x[k] for k,v in MI(G).items()),3) for G in cols]} diagonal MIs {[round(sum(v*r2.x[k] for k,v in MI(G).items()),3) for G in diags]}')
    obj3 = np.zeros(NV); obj3[IC] = 1
    r3 = linprog(obj3, A_ub=M, b_ub=b, bounds=bounds, method='highs')
    print(f'(3) two-merge sanity: row-full, min c_c alone = {r3.fun:.4f}  [expect 0: column 3-cycles]')
    # (4) the exact trade-off: max I(R_0) given c_c + c_d <= s  (bounds on IC, ID via extra rows)
    for s in (0, 1, 2, 3, 4, 4.5, 6):
        obj4 = np.zeros(NV)
        for k, v in MI(rows[0]).items(): obj4[k] -= v
        M4, b4 = build([{IC: 1, ID: 1}]); b4[-1] = s
        r4 = linprog(obj4, A_ub=M4, b_ub=b4, bounds=bounds, method='highs')
        print(f'(4) c_c + c_d <= {s}: max I(R_0 : rest) = {-r4.fun:.4f}')
    # (5) the symmetric-mixture question: row-full, minimise q_c c_c + q_d c_d for a few (q_c, q_d)
    for qc, qd in ((0.5, 0.5), (1, 0), (0.75, 0.25)):
        obj5 = np.zeros(NV); obj5[IC] = qc; obj5[ID] = qd
        r5 = linprog(obj5, A_ub=M, b_ub=b, bounds=bounds, method='highs')
        print(f'(5) row-full: min {qc} c_c + {qd} c_d = {r5.fun:.4f}')
