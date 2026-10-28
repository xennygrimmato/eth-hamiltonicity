"""Single terms of a piece are not two-order.  For the middle piece s = 0 and each i, the term
    T_{0,i}(x,y,u,v) = (-1)^i [t^{mu(u)}] a^<i>_{mu(x)}[i-h] b_{mu(v)}[h-i] t^{mu(y)}
has, by construction, column rank <= p(2h-i) (it passes through V_{2h-i} with b acting first) and,
by Lemma 9(a) applied to the whole sum only, no cheap row factorization: we print both true ranks.
A single term would cost log p(i) + log p(2h-i) <= 2 lambda (rho = 1/2) IF it had the row
factorization of the exchanged order; the table shows its row rank is instead ~ N^2 (capped) or
much larger than p(i).
"""
import sys, math
sys.path.insert(0, '.')
from rho_fock_lib import partitions, p, a_fam, b_fam, angle, op_poly
from flint import nmod_mat

PR = (1 << 61) - 1


def rank_mod(rows, ncols):
    if not rows:
        return 0
    M = [[0] * ncols for _ in rows]
    for i, r in enumerate(rows):
        for j, v in r.items():
            M[i][j] = v % PR
    return nmod_mat(M, PR).rank()


def term_tensor(h, s, i):
    parts = partitions(h)
    idx = {q: k for k, q in enumerate(parts)}
    N = len(parts)
    T = {}
    w = 2 * h - s - i
    if w < 0:
        return N, T
    first = {}
    for v, nu in enumerate(parts):
        bv = b_fam(nu)
        for y, eta in enumerate(parts):
            g = op_poly(bv, h - s - i, {eta: 1})
            if g:
                first[(y, v)] = g
    needed = set()
    for g in first.values():
        needed |= set(g)
    second = {}
    for x, mu in enumerate(parts):
        ai = angle(a_fam(mu), h, i)
        for sg in needed:
            for upart, d in op_poly(ai, s - h + i, {sg: 1}).items():
                if upart in idx:
                    second.setdefault(sg, []).append((x, idx[upart], d))
    sign = (-1) ** i
    for (y, v), g in first.items():
        for sg, c1 in g.items():
            for (x, u, d) in second.get(sg, []):
                T[(x, y, u, v)] = T.get((x, y, u, v), 0) + sign * c1 * d
    return N, {k: v for k, v in T.items() if v}


def main():
    for h in [int(a) for a in sys.argv[1:]] or [4, 5, 6]:
        N = len(partitions(h))
        print(f"h={h}  N={N}  N^2={N*N}   (piece s=0; term i passes through V_{{2h-i}} column-wise)")
        for i in range(0, 2 * h + 1):
            N, T = term_tensor(h, 0, i)
            if not T:
                print(f"  i={i:2d}: term = 0")
                continue
            Mr, Mc = {}, {}
            for (x, y, u, v), val in T.items():
                Mr.setdefault(x * N + y, {})[u * N + v] = val
                Mc.setdefault(x * N + u, {})[y * N + v] = val
            rr = rank_mod([Mr[k] for k in sorted(Mr)], N * N)
            rc = rank_mod([Mc[k] for k in sorted(Mc)], N * N)
            print(f"  i={i:2d}: rank_col={rc:5d} (<= p(2h-i)={p(2*h-i):5d})   rank_row={rr:5d}  (p(i)={p(i):4d}; the exchanged order would give <= p(i))")
        print()


if __name__ == "__main__":
    main()
