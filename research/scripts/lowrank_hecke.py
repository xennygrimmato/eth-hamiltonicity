"""Q-rank of the non-bipartite matchings-connectivity matrix H_t (perfect matchings on 2t points,
entry [P u Q is one cycle]) via the Hecke algebra of the Gelfand pair (S_2t, B_t), so that t=6
(10395 matchings) is feasible.

A_mu := 0/1 matrix [coset type of (P,Q) = mu]; these span a commutative algebra of dim p(t).
M_{kappa,mu} := (A_(t) A_mu)(P0, R) for any R of type kappa (multiplication by A_(t) in the
A-basis).  Its eigenvalues are the eigenvalues of H_t = A_(t) on the isotypic components.  The
multiplicity of each distinct eigenvalue in H_t is recovered from trace(H_t^k) = N (H_t^k)(P0,P0).
"""
import itertools, math, sys
import numpy as np
from fractions import Fraction
import sympy as sp

def matchings(points):
    if not points:
        yield []
        return
    a = points[0]
    for i in range(1, len(points)):
        rest = points[1:i] + points[i + 1:]
        for m in matchings(rest):
            yield [(a, points[i])] + m

def as_inv(m, n2):
    p = np.zeros(n2, dtype=np.int64)
    for a, b in m:
        p[a] = b; p[b] = a
    return p

def types_batch(Q, R, t):
    """Q: (q,2t), R: (r,2t) involutions. return coset type codes for all pairs (q*r,)
    coset type = cycle type of sigma = Q o R restricted (each union cycle of length 2l gives two
    sigma-cycles of length l).  code = sorted tuple of point return times, encoded as int."""
    q, n2 = Q.shape; r = R.shape[0]
    sig = Q[:, None, :][np.zeros((1,), dtype=int)]  # placeholder
    # sigma[i,j,x] = Q[i, R[j,x]]
    sig = np.take_along_axis(np.broadcast_to(Q[:, None, :], (q, r, n2)),
                             np.broadcast_to(R[None, :, :], (q, r, n2)), axis=2)
    cur = sig.copy(); ret = np.zeros((q, r, n2), dtype=np.int64)
    ident = np.arange(n2)
    for k in range(1, t + 1):
        hit = (cur == ident) & (ret == 0)
        ret[hit] = k
        cur = np.take_along_axis(sig, cur, axis=2)
    # multiset of return times -> counts of each length l: cnt_l = #points with return l / l, union
    # cycles of length 2l = cnt_l / 2
    code = np.zeros((q, r), dtype=np.int64)
    for l in range(1, t + 1):
        c = (ret == l).sum(axis=2) // (2 * l)
        code = code * (t + 1) + c
    return code.reshape(-1)

def code_to_part(c, t):
    parts = []
    for l in range(t, 0, -1):
        parts += [l] * (c % (t + 1)); c //= (t + 1)
    return tuple(sorted(parts, reverse=True))

def run(t):
    pts = list(range(2 * t))
    ms = [as_inv(m, 2 * t) for m in matchings(pts)]
    A = np.array(ms); N = len(A)
    P0 = A[0:1]
    tp0 = types_batch(P0, A, t)  # type of (P0, R) for all R
    parts = sorted({code_to_part(c, t) for c in tp0})
    pidx = {p: i for i, p in enumerate(parts)}
    typ = np.array([pidx[code_to_part(c, t)] for c in tp0])
    full = pidx[(t,)]; idn = pidx[tuple([1] * t)]
    Qs = A[typ == full]          # Q with type(P0,Q) = (t)
    # M[kappa, mu] = #{Q: type(P0,Q)=(t), type(Q,R)=mu} for a representative R of type kappa
    reps = [np.nonzero(typ == k)[0][0] for k in range(len(parts))]
    Rr = A[reps]
    T = types_batch(Qs, Rr, t).reshape(len(Qs), len(reps))
    p = len(parts)
    M = np.zeros((p, p), dtype=np.int64)
    for k in range(p):
        for c in T[:, k]:
            M[k, pidx[code_to_part(c, t)]] += 1
    # H = A_(t) acts on the coefficient vector of A_mu: (A_(t) X)(P0,R_kappa) = sum_mu M[kappa,mu] X_mu
    Ms = sp.Matrix(M.tolist())
    ev = Ms.eigenvals()  # exact
    # traces: (H^k)(P0,P0): start X = e_id, apply M
    X = sp.zeros(p, 1); X[idn] = 1
    tr = []
    for k in range(len(ev)):
        tr.append(N * X[idn]); X = Ms * X
    vals = list(ev.keys())
    V = sp.Matrix([[v ** k for v in vals] for k in range(len(vals))])
    mult = V.solve(sp.Matrix(tr))
    zero_mult = sum(m for v, m in zip(vals, mult) if v == 0)
    return N, N - zero_mult, dict(zip([sp.nsimplify(v) for v in vals], [int(m) for m in mult]))

if __name__ == '__main__':
    for t in range(2, 7):
        N, rk, em = run(t)
        print(f"t={t}: #PM={N}  rank_Q(H_t)={rk}  4^t={4**t}  eigenvalue:multiplicity {em}", flush=True)
