"""SU(2) recoupling pieces on K4 (Task 3b).

Four parties a,b,c,d each V_j (n = 2j+1). Pieces P_J = projector onto total spin J of V_a (x) V_b, viewed as a
4-party tensor (a,b inputs; c,d outputs). sum_J P_J = Id = wires a-c, b-d (the class-2 crossing X_2 of z1).
Ranks: rk(ab|cd) [row], rk(ac|bd) [operator-Schmidt / realignment; the split in which both wires are internal],
rk(ad|bc) [partial transpose].
Part 1: brute-force numerical ranks of P_J and of interval sums.
Part 2: the 6j-matrix uncertainty principle: ratio U[J,J']/U[J,0] is a polynomial of degree J' in J(J+1).
"""
import numpy as np
from fractions import Fraction
from sympy.physics.wigner import wigner_6j, clebsch_gordan
from sympy import S, Rational
import itertools

def spin_ops(j):
    m = np.arange(j, -j - 1, -1)
    n = len(m)
    Jz = np.diag(m)
    Jp = np.zeros((n, n))
    for i in range(1, n):
        Jp[i - 1, i] = np.sqrt(j * (j + 1) - m[i] * (m[i] + 1))
    Jx = (Jp + Jp.T) / 2; Jy = (Jp - Jp.T) / (2j)
    return Jx, Jy, Jz

def projectors(j):
    Jx, Jy, Jz = spin_ops(j)
    n = Jx.shape[0]
    I = np.eye(n)
    Tot2 = sum(np.kron(A, I) @ np.kron(A, I) + np.kron(I, A) @ np.kron(I, A) + 2 * np.kron(A, A) for A in (Jx, Jy, Jz))
    w, V = np.linalg.eigh(Tot2)
    Ps = {}
    for J2 in range(0, int(round(4 * j)) + 1, 2):
        J = J2 / 2
        sel = np.abs(w - J * (J + 1)) < 1e-6
        Ps[J] = V[:, sel] @ V[:, sel].conj().T
    return Ps, n

def ranks(P, n):
    T = P.reshape(n, n, n, n)  # indices c,d,a,b (output c,d ; input a,b)
    r_row = np.linalg.matrix_rank(T.reshape(n * n, n * n), tol=1e-8)                  # cd | ab
    r_ac = np.linalg.matrix_rank(T.transpose(0, 2, 1, 3).reshape(n * n, n * n), tol=1e-8)  # ca | db
    r_ad = np.linalg.matrix_rank(T.transpose(0, 3, 1, 2).reshape(n * n, n * n), tol=1e-8)  # cb | da  (= ad|bc)
    return r_row, r_ac, r_ad

print('Part 1: ranks (ab|cd, ac|bd [wires internal], ad|bc) of P_J and of interval sums')
for j in [0.5, 1, 1.5, 2, 2.5, 3]:
    Ps, n = projectors(j)
    Js = sorted(Ps)
    print(' j =', j, 'n =', n, ' P_J:', [(J, ranks(Ps[J], n)) for J in Js])
    best = None
    for a in range(len(Js)):
        for b in range(a, len(Js)):
            Q = sum(Ps[J] for J in Js[a:b + 1])
            r = ranks(Q, n)
            if b - a < len(Js) - 1 and (best is None or r[1] < best[1][1]):
                best = ((Js[a], Js[b]), r)
    print('    interval sum with smallest ac|bd rank (excluding the full sum):', best)

print()
print('Part 2: U[J,Jp] = sqrt((2J+1)(2Jp+1)) {j j J; j j Jp}; check U[.,Jp]/U[.,0] = poly of degree Jp in J(J+1)')
for j2 in range(1, 13):
    j = Rational(j2, 2)
    n = j2 + 1
    Js = list(range(n))
    U = np.array([[float(((2 * J + 1) * (2 * Jp + 1)) ** S.Half * wigner_6j(j, j, J, j, j, Jp)) for Jp in Js] for J in Js])
    assert np.allclose(U @ U.T, np.eye(n), atol=1e-9), 'not orthogonal'
    lam = np.array([J * (J + 1) for J in Js], dtype=float)
    maxres = 0; mindeg_ok = True
    for Jp in Js:
        ratio = U[:, Jp] / U[:, 0]
        # exact degree check: fit polynomial degree Jp through all n points; residual must vanish
        V = np.vander(lam / lam.max(), Jp + 1)
        coef, *_ = np.linalg.lstsq(V, ratio, rcond=None)
        res = np.max(np.abs(V @ coef - ratio))
        maxres = max(maxres, res)
        if Jp >= 1:
            V2 = np.vander(lam / lam.max(), Jp)
            coef2, *_ = np.linalg.lstsq(V2, ratio, rcond=None)
            if np.max(np.abs(V2 @ coef2 - ratio)) < 1e-6:
                mindeg_ok = False
    print(' j = %-4s n = %2d  orthogonal: yes  max residual deg-Jp fit = %.1e  degree exactly Jp: %s  min|U[J,0]| = %.3f'
          % (j, n, maxres, mindeg_ok, np.min(np.abs(U[:, 0]))))
    # uncertainty test: random y supported on Jp <= J0, count nonzeros of x = U y
    rng = np.random.default_rng(j2)
    worst = {}
    for J0 in range(n):
        mn = n
        for _ in range(200):
            y = np.zeros(n)
            k = rng.integers(1, J0 + 2)
            sup = rng.choice(J0 + 1, size=k, replace=False)
            y[sup] = rng.integers(-3, 4, size=k)
            if not y.any():
                continue
            x = U @ y
            mn = min(mn, int(np.sum(np.abs(x) > 1e-9)))
        worst[J0] = mn
    print('     min ab-support over random y with ac-support in [0,J0]:', worst, '(bound n - J0)')
