"""(diagonality needs <a,a'> = <a,al'><al,a'>; parameters chosen accordingly)
Three wires on one d=2 multinomial (SO(2,1)-type) Meixner bond, 1D wires.
Pairing generating function for wires u,v:
  G_uv(t,s) = 1/[(1+b_u t)(1+b'_v s) - y * sum_m (al_um + a_um t)(al'_vm + a'_vm s)]
(times (y-1) if v is a pole wire). Checks: G_uu diagonal = c*(q y ts)^i; G_uv (u!=v) polynomial in y; vanishing at y=1
for the upper blocks. Also prints shell ranks of Phi for a pole wire (effective bond dimension per energy shell)."""
import sympy as sp
y, t, s, c = sp.symbols('y t s c')
def V(*a): return sp.Matrix(a)
W = {  # wire: (alpha, a, alpha', a', pole)
 1: (V(0, 0), V(1, 0), V(0, 0), V(1, 0), False),
 2: (V(1, 0), V(1, c), V(1, 0), V(1, 0), True),
 3: (V(0, 1), V(c, 1), V(0, 1), V(0, 1), True)}
def b(u):  # b_u = y <a_u, al'_u>, b'_u = y <al_u, a'_u>
    al, a, alp, ap, _ = W[u]
    return y * (a.T * alp)[0], y * (al.T * ap)[0]
N = 4
for u in W:
    for v in W:
        al, a, _, _, _ = W[u]
        _, _, alp, ap, pole = W[v]
        bu = b(u)[0]; bv = b(v)[1]
        Q = (1 + bu * t) * (1 + bv * s) - y * sum((al[m] + a[m] * t) * (alp[m] + ap[m] * s) for m in range(2))
        G = sp.series(sp.series(1 / Q, t, 0, N).removeO(), s, 0, N).removeO()
        G = sp.expand(G * ((y - 1) if pole else 1))
        M = sp.Matrix(N, N, lambda i, j: sp.factor(sp.simplify(G.coeff(t, i).coeff(s, j))))
        poly = all(sp.simplify(x).is_polynomial(y) for x in M)
        at1 = M.subs(y, 1).applyfunc(sp.simplify)
        print('J_%d%d: polynomial in y: %s, zero at y=1: %s' % (u, v, poly, at1 == sp.zeros(N, N)))
        if u == v:
            print('   diagonal entries:', [M[i, i] for i in range(N)], ' offdiag zero:', all(M[i, j] == 0 for i in range(N) for j in range(N) if i != j))
# effective bond dimension: shell m rows r=(r1, m-r1) of Phi_2(r, i) = [t^i](1+t)^{r1}(c t)^{r2}/(1+y t)^{m+1}
for m in range(1, 6):
    rows = []
    for r1 in range(m + 1):
        f = sp.series((1 + t) ** r1 * (c * t) ** (m - r1) / (1 + y * t) ** (m + 1), t, 0, 2 * m + 2).removeO()
        rows.append([f.coeff(t, i) for i in range(2 * m + 2)])
    print('shell', m, 'rank of Phi_2 block =', sp.Matrix(rows).rank(), 'of', m + 1)
