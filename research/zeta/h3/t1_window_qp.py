#!/usr/bin/env python3
"""T1 (h3): window extremal problem of Alpoge-Furman, reproduced and extended.

R_F(psi) = [ int psi^2 + iint k_F(u-v) psi(u) psi(v) ] / (int psi)^2 ,  psi on [-c/2, c/2],
where k_F is the "form factor kernel": with F(alpha) = delta(alpha) + f(|alpha|) on [-c,c],
the pair sum is  r(0) + int r f  with r = psi*psi, and int r(a) f(|a|) da = iint f(|u-v|) psi psi.
 model 'diag' : f(a) = a            (Montgomery diagonal; the paper's case for c<=1)
 model 'gue'  : f(a) = min(a, 1)    (GUE / Hardy-Littlewood prediction for c>1)
Simple-on-line certificate: 2 - R ; distinct certificate: (3 - R)/2.
Discretisation: midpoint rule with n nodes; minimiser of psi^T A psi / (w^T psi)^2 is psi = A^{-1} w
(if A is PD), else a nonnegativity-constrained version via NNLS-type active set.
"""
import numpy as np
from scipy.optimize import minimize, nnls

def build(c, n, model):
    h = c / n
    u = -c/2 + h*(np.arange(n)+0.5)
    D = np.abs(u[:, None]-u[None, :])
    if model == 'diag': f = D
    elif model == 'gue': f = np.minimum(D, 1.0)
    else: f = np.where(D <= 1.0, D, float(model))   # model = B : F(alpha) <= B on 1<|alpha|<c
    # int psi^2 ~ h sum psi_i^2 ; iint f psi psi ~ h^2 psi^T f psi ; int psi ~ h sum psi
    A = h*np.eye(n) + h*h*f
    w = h*np.ones(n)
    return u, A, w

def best_unconstrained(c, n=2000, model='diag'):
    u, A, w = build(c, n, model)
    ev = np.linalg.eigvalsh(A).min()
    x = np.linalg.solve(A, w)
    R = 1.0/(w @ x)
    return R, u, x/x.max(), ev

def best_nonneg(c, n=600, model='diag'):
    # min x^T A x s.t. w^T x = 1, x >= 0 : solve via NNLS on Cholesky factor with a penalty row
    u, A, w = build(c, n, model)
    Lc = np.linalg.cholesky(A + 1e-15*np.eye(n))
    M = 1e4
    Aug = np.vstack([Lc.T, M*w[None, :]])
    b = np.concatenate([np.zeros(n), [M]])
    x, _ = nnls(Aug, b, maxiter=50*n)
    x = x/(w @ x)
    return x @ A @ x, u, x/x.max()

def R_diag_closed(c):
    return c/2 + np.cos(c/np.sqrt(2))/np.sin(c/np.sqrt(2))/np.sqrt(2)

if __name__ == '__main__':
    cMTinv = 0.5 + 1/np.sqrt(2)/np.tan(1/np.sqrt(2))
    print("c_MT^{-1} = %.10f ; simple 2-R = %.10f ; distinct (3-R)/2 = %.10f" % (cMTinv, 2-cMTinv, (3-cMTinv)/2))
    print("indicator R=4/3 -> %.6f , %.6f" % (2-4/3, (3-4/3)/2))
    R, u, x, ev = best_unconstrained(1.0, 1500, "diag")
    err = np.max(np.abs(x - np.cos(np.sqrt(2)*u)/np.cos(np.sqrt(2)*u).max()))
    print("QP c=1 diag: R=%.8f (closed %.8f), max|psi - cos(sqrt2 u)| = %.2e, min eig A = %.2e" % (R, cMTinv, err, ev))
    Rn, _, _ = best_nonneg(1.0, 400, 'diag')
    print("QP c=1 diag with psi>=0: R=%.6f" % Rn)
    print("\n c   | diag: R  simple distinct (closed-form simple) | gue: R simple distinct  psi>=0? (min psi/max)  R_nonneg")
    for c in [0.5, 0.75, 1.0, 1.1, 1.2, 1.25, 1.3, 1.4, 1.5, 1.6, 1.7, 1.75, 1.8, 1.9, 2.0]:
        Rd, ud, xd, _ = best_unconstrained(c, 700, "diag")
        Rg, ug, xg, evg = best_unconstrained(c, 700, "gue")
        Rgn, _, _ = best_nonneg(c, 300, "gue") if xg.min() < 0 else (Rg, None, None)
        print("%.2f | %.5f %.5f %.5f (%.5f) | %.5f %.5f %.5f  min=%.3f  %.5f" % (
            c, Rd, 2-Rd, (3-Rd)/2, 2-R_diag_closed(c), Rg, 2-Rg, (3-Rg)/2, xg.min(), Rgn))

    print("\n If only an upper bound F(alpha)<=B on 1<|alpha|<c were known: best simple-on-line 2-R over c (psi>=0 checked)")
    for B in [1.0, 1.5, 2.0, 3.0, 5.0, 10.0, 100.0]:
        best = (0, 1.0)
        for c in np.arange(1.0, 2.001, 0.02):
            Rb, ub, xb, _ = best_unconstrained(c, 500, B)
            if xb.min() < 0: Rb, _, _ = best_nonneg(c, 250, B)
            if 2-Rb > best[0]: best = (2-Rb, c)
        print("  B=%6.1f : best simple %.5f at c=%.2f ; distinct %.5f" % (B, best[0], best[1], (1+best[0])/2))
