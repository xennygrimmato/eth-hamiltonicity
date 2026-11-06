"""fourier_pieces.py -- Cohn-Umans / Fourier pieces on Delta_3 at N0 = 2.

Index array x_{l,s} in [N], (l,s) in Z_3^2.  Node (l,s) holds (x_{l,s}, x_{l+1,s}); it is node (r,c) = (l, s-l) of the grid.
Row l = nodes (l,0),(l,1),(l,2) (holds X_l = (x_{l,.}) in slot 0 and X_{l+1} in slot 1).
Column c = nodes (l, l+c), l = 0,1,2.   Triangle s = nodes (0,s),(1,s),(2,s).
f_Delta = prod_{(l,s)} [slot1 of (l,s) = slot0 of (l+1,s)].  Axis order: node (l,s) lexicographic, slots 0,1 -> 18 axes.

Two families of Fourier pieces (both exact decompositions of f_Delta):
 (P) product group G = S_3^3, one TPP <2,2,2> per triangle (S_3 through its three subgroups of order 2, CU03 Sec. 3):
     A_rho = tensor_s A^{(s)}_{rho_s},  A^{(s)}_rho(i,j;j',k;k',i') = (d/6) chi_rho(s_i^-1 t_j t_j'^-1 u_k u_k'^-1 s_i').
 (C) single group G = (Cyc_3^3)^2 x| Cyc_2 (CKSU05 Sec. 2, n = 3, |G| = 1458, degrees <= 2) realising <12,12,12> >= <8,8,8>
     under the ROW structure: row l embeds via (X_l, X_{l+1}) -> sigma(X_l)^-1 tau(X_{l+1}) etc.
For every piece: flattening ranks across each row, column, node (cut bounds on the D1 costs), and the network bound 3 log2 d.
"""
import itertools, sys, time
import numpy as np

N = 2
AX = [((l, s), sl) for l in range(3) for s in range(3) for sl in range(2)]       # 18 axes
AXI = {a: k for k, a in enumerate(AX)}
IDX = np.indices((N,) * 18).reshape(18, -1)                                      # 18 x 2^18

def axes_row(l):  return [AXI[((l, s), sl)] for s in range(3) for sl in range(2)]
def axes_col(c):  return [AXI[((l, (l + c) % 3), sl)] for l in range(3) for sl in range(2)]
def axes_node(v): return [AXI[(v, 0)], AXI[(v, 1)]]

def frank(T, axes, tol=1e-9):
    """rank of the flattening (axes | rest)."""
    T = T.reshape((N,) * 18)
    rest = [k for k in range(18) if k not in axes]
    M = np.transpose(T, axes + rest).reshape(N ** len(axes), -1)
    s = np.linalg.svd(M, compute_uv=False)
    return int((s > tol * max(1.0, s[0])).sum())

def ranks(T):
    return dict(rows=[frank(T, axes_row(l)) for l in range(3)],
                cols=[frank(T, axes_col(c)) for c in range(3)],
                nodes=[frank(T, axes_node((l, s))) for l in range(3) for s in range(3)])

def cutbounds(rk):
    """D1 cut bounds: c_k >= max_group log rk, c_k >= 1/2 sum_group log rk."""
    lr = [np.log2(r) for r in rk['rows']]; lc = [np.log2(r) for r in rk['cols']]
    return dict(row=max(max(lr), sum(lr) / 2), col=max(max(lc), sum(lc) / 2))

def f_delta():
    ok = np.ones(IDX.shape[1], bool)
    for l in range(3):
        for s in range(3):
            ok &= IDX[AXI[((l, s), 1)]] == IDX[AXI[(((l + 1) % 3, s), 0)]]
    return ok.astype(float)

# ---------------------------------------------------------------- S_3 (permutations of {0,1,2}) -------------------
S3 = list(itertools.permutations(range(3)))
def pmul(p, q): return tuple(p[q[i]] for i in range(3))        # (pq)(i) = p(q(i))
def pinv(p):
    r = [0] * 3
    for i in range(3): r[p[i]] = i
    return tuple(r)
def sign(p):
    s = 1
    for i in range(3):
        for j in range(i + 1, 3):
            if p[i] > p[j]: s = -s
    return s
def chi_std(p):  return sum(1 for i in range(3) if p[i] == i) - 1
S3_IRR = {'triv': (1, lambda p: 1), 'sgn': (1, sign), 'std': (2, chi_std)}
# TPP triple of S_3: the three subgroups of order 2 (CU03 Section 3).
S3_S = [(0, 1, 2), (1, 0, 2)]; S3_T = [(0, 1, 2), (0, 2, 1)]; S3_U = [(0, 1, 2), (2, 1, 0)]

def triangle_piece_S3(name):
    """A_rho on one triangle: 6 axes (i,j | j',k | k',i') each in [2]; returns 2^6 array."""
    d, chi = S3_IRR[name]
    A = np.zeros((2,) * 6)
    for i, j, jp, k, kp, ip in itertools.product(range(2), repeat=6):
        w = pmul(pmul(pmul(pmul(pmul(pinv(S3_S[i]), S3_T[j]), pinv(S3_T[jp])), S3_U[k]), pinv(S3_U[kp])), S3_S[ip])
        A[i, j, jp, k, kp, ip] = d / 6 * chi(w)
    return A

def product_piece(names):
    """tensor over triangles s of A^{(s)}_{names[s]}, placed into the 18-axis layout."""
    T = np.ones((1,))
    order = []
    for s in range(3):
        A = triangle_piece_S3(names[s])           # axes: (0,s)0 (0,s)1 (1,s)0 (1,s)1 (2,s)0 (2,s)1
        order += [AXI[((0, s), 0)], AXI[((0, s), 1)], AXI[((1, s), 0)], AXI[((1, s), 1)], AXI[((2, s), 0)], AXI[((2, s), 1)]]
        T = np.multiply.outer(T, A)
    T = T.reshape((2,) * 18)
    return np.transpose(T, np.argsort(order)).reshape(-1)

# ---------------------------------------------------------------- G = (Cyc_3^3)^2 x| Cyc_2 ------------------------
# element = (a, b, j), a, b in Z_3^3 encoded as ints 0..26 (base 3), j in {0,1}.  z(a,b)z = (b,a).
def dec(v): return np.array([v % 3, (v // 3) % 3, (v // 9) % 3])
def enc(t): return int(t[0] + 3 * t[1] + 9 * t[2])
def gmul(g, h):
    a, b, j = g; a2, b2, j2 = h
    if j == 1: a2, b2 = b2, a2
    return (enc((dec(a) + dec(a2)) % 3), enc((dec(b) + dec(b2)) % 3), (j + j2) % 2)
def ginv(g):
    a, b, j = g
    na, nb = enc((-dec(a)) % 3), enc((-dec(b)) % 3)
    if j == 1: na, nb = nb, na
    return (na, nb, j)
G = [(a, b, j) for a in range(27) for b in range(27) for j in range(2)]
GI = {g: i for i, g in enumerate(G)}
def build_mult_table():
    M = np.zeros((1458, 1458), np.int32)
    for i, g in enumerate(G):
        for k, h in enumerate(G):
            M[i, k] = GI[gmul(g, h)]
    return M
W = np.exp(2j * np.pi / 3)
def chars_G():
    """list of (label, d, chi array over G)."""
    out = []
    A = np.array([dec(g[0]) for g in G]); B = np.array([dec(g[1]) for g in G]); J = np.array([g[2] for g in G])
    for al in range(27):
        alv = dec(al)
        ph = W ** ((A @ alv + B @ alv) % 3)
        out.append((('1+', al), 1, ph)); out.append((('1-', al), 1, ph * np.where(J == 1, -1, 1)))
    for al in range(27):
        for be in range(al + 1, 27):
            alv, bev = dec(al), dec(be)
            ch = (W ** ((A @ alv + B @ bev) % 3) + W ** ((A @ bev + B @ alv) % 3)) * (J == 0)
            out.append((('2', al, be), 2, ch))
    assert sum(d * d for _, d, _ in out) == 1458 and len(out) == 405
    return out
# CKSU Sec. 2 subsets: S_i = {(a,b)z^j : a in H_i\{0}, b in H_{i+1}, j in {0,1}}  (H_i = i-th coordinate).  |S_i| = 12.
def cksu_subset(i, full=False):
    els = []
    for av in (1, 2):
        for bv in (range(3) if full else (0, 1)):
            for j in (0, 1):
                a = [0, 0, 0]; a[i] = av; b = [0, 0, 0]; b[(i + 1) % 3] = bv
                els.append((enc(a), enc(b), j))
    return els                                 # 8 elements (coordinatewise order: av-1, bv, j) or 12

def check_tpp(S, T, U):
    """TPP (CU03 Def. 2.1, CKSU Def. 1.3) with RIGHT quotient sets Q(S) = {s1 s2^-1}: q1 q2 q3 = 1 only trivially."""
    e = GI[(0, 0, 0)]
    QS = {GI[gmul(a, ginv(b))] for a in S for b in S}; QT = {GI[gmul(a, ginv(b))] for a in T for b in T}
    QU = {GI[gmul(a, ginv(b))] for a in U for b in U}
    for q1 in QS:
        for q2 in QT:
            q12 = GI[gmul(G[q1], G[q2])]
            for q3 in QU:
                if GI[gmul(G[q12], G[q3])] == e and not (q1 == e and q2 == e and q3 == e):
                    return False
    return True

def row_words(MT, S, T, U, sig, tau, ups):
    """index of the group word sigma(X0)^-1 tau(X1) tau(X1')^-1 ups(X2) ups(X2')^-1 sigma(X0') for all 2^18 entries.
    X0 = slot-0 triple of row 0 (x_{0,s}); X1 = slot-1 triple of row 0; X1' = slot-0 of row 1; X2 = slot-1 of row 1;
    X2' = slot-0 of row 2; X0' = slot-1 of row 2.  Triple -> integer i_0 + 2 i_1 + 4 i_2."""
    def trip(l, sl): return IDX[AXI[((l, 0), sl)]] + 2 * IDX[AXI[((l, 1), sl)]] + 4 * IDX[AXI[((l, 2), sl)]]
    X0, X1, X1p, X2, X2p, X0p = trip(0, 0), trip(0, 1), trip(1, 0), trip(1, 1), trip(2, 0), trip(2, 1)
    s_inv = np.array([GI[ginv(S[sig[i]])] for i in range(8)]); t_ = np.array([GI[T[tau[i]]] for i in range(8)])
    t_inv = np.array([GI[ginv(T[tau[i]])] for i in range(8)]); u_ = np.array([GI[U[ups[i]]] for i in range(8)])
    u_inv = np.array([GI[ginv(U[ups[i]])] for i in range(8)]); s_ = np.array([GI[S[sig[i]]] for i in range(8)])
    w = MT[s_inv[X0], t_[X1]]
    w = MT[w, MT[t_inv[X1p], u_[X2]]]
    w = MT[w, MT[u_inv[X2p], s_[X0p]]]
    return w

def summarize(tag, T, extra=''):
    rk = ranks(T); cb = cutbounds(rk)
    print(f"  {tag:28s} rows {rk['rows']} cols {rk['cols']} nodes {rk['nodes']}  cut: c_row>={cb['row']:.2f} c_col>={cb['col']:.2f} {extra}")
    return rk, cb

if __name__ == '__main__':
    t0 = time.time()
    f = f_delta()
    print("f_Delta:", summarize('f_Delta', f)[0])

    # ---------------- (P) product family S_3^3 -------------------------------------------------------------
    print("\n(P) product group S_3^3, coordinatewise identification; TPP of S_3 via order-2 subgroups")
    tri = {nm: triangle_piece_S3(nm) for nm in S3_IRR}
    tot = sum(tri.values()); tgt = np.zeros((2,) * 6)
    for i, j, k in itertools.product(range(2), repeat=3): tgt[i, j, j, k, k, i] = 1
    print("  one triangle: sum of 3 Fourier pieces == <2,2,2>:", np.allclose(tot, tgt))
    acc = np.zeros_like(f); byw = {}
    for names in itertools.product(S3_IRR, repeat=3):
        A = product_piece(names); acc += A
        m = sum(1 for n_ in names if n_ == 'std'); byw.setdefault(m, []).append(A)
        if names in [('triv',) * 3, ('std', 'triv', 'triv'), ('std', 'std', 'triv'), ('std',) * 3]:
            summarize(str(names), A, extra=f"network bound 3log2 d = {3 * m}")
    print("  sum of 27 product pieces == f_Delta:", np.allclose(acc, f))
    print("  non-product blocks B_m = sum of pieces with m std factors (construction bound 3 log2 D(B_m)):")
    for m in sorted(byw):
        B = sum(byw[m]); D = sum(2 ** m for _ in byw[m])
        summarize(f"B_{m} ({len(byw[m])} pieces)", B, extra=f"D={D}, 3log2 D={3 * np.log2(D):.2f}")

    # ---------------- (C) single group (Cyc_3^3)^2 x| Cyc_2 ---------------------------------------------------
    print("\n(C) single group G = (Cyc_3^3)^2 x| Cyc_2, |G| = 1458, realising <8,8,8> under the ROW structure")
    MT = build_mult_table(); print("  mult table built", f"{time.time() - t0:.1f}s")
    S, T_, U = cksu_subset(0), cksu_subset(1), cksu_subset(2)
    print("  TPP of the three 8-subsets:", check_tpp(S, T_, U), " (12-subsets:", check_tpp(cksu_subset(0, 1), cksu_subset(1, 1), cksu_subset(2, 1)), ")")
    CH = chars_G()
    rng = np.random.default_rng(1)
    idents = [('coordinatewise', list(range(8)), list(range(8)), list(range(8)))]
    for r in range(3):
        idents.append((f'random#{r}', list(rng.permutation(8)), list(rng.permutation(8)), list(rng.permutation(8))))
    for label, sig, tau, ups in idents:
        w = row_words(MT, S, T_, U, sig, tau, ups)
        acc = np.zeros(IDX.shape[1], complex)
        stats = {1: [], 2: []}
        for (lab, d, chi) in CH:
            A = (d / 1458) * chi[w]
            acc += A
            if np.abs(A).max() < 1e-12:
                stats[d].append(None); continue
            Ar = A if np.allclose(A.imag, 0) else A
            rk = ranks(Ar); cb = cutbounds(rk)
            stats[d].append((rk, cb))
        print(f"  [{label}] sum of 405 pieces == f_Delta: {np.allclose(acc, f)}")
        for d in (1, 2):
            st = [x for x in stats[d] if x is not None]
            nz = len(st)
            rows = np.array([x[0]['rows'] for x in st]); cols = np.array([x[0]['cols'] for x in st]); nodes = np.array([x[0]['nodes'] for x in st])
            crow = np.array([x[1]['row'] for x in st]); ccol = np.array([x[1]['col'] for x in st])
            print(f"    degree {d}: {nz} nonzero pieces (of {sum(1 for c in CH if c[1] == d)});  network bound c_row <= {3 * np.log2(d):.0f}")
            print(f"      row ranks: min {rows.min()} max {rows.max()} | col ranks: min {cols.min()} max {cols.max()} "
                  f"hist {dict(zip(*np.unique(cols, return_counts=True)))} | node ranks min {nodes.min()} max {nodes.max()}")
            print(f"      cut bounds: c_row>= in [{crow.min():.2f},{crow.max():.2f}]  c_col>= in [{ccol.min():.2f},{ccol.max():.2f}]  "
                  f"c_row+c_col >= max {(crow + ccol).max():.2f}, min {(crow + ccol).min():.2f}")
        print(f"    ({time.time() - t0:.0f}s)")

    # ---------------- control: generic row-local images of f_Delta --------------------------------------------
    print("\ncontrol: f_Delta under random invertible row-local maps (64x64 per row): column ranks")
    F3 = f.reshape(64, 64, 64)
    for r in range(2):
        Ms = [rng.standard_normal((64, 64)) for _ in range(3)]
        Tg = np.einsum('abc,ia,jb,kc->ijk', F3, *Ms, optimize=True).reshape(-1)
        summarize(f'generic row-local #{r}', Tg)
    print(f"done {time.time() - t0:.0f}s")
