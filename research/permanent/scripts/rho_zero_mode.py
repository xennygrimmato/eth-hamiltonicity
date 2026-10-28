"""The zero-mode loophole, first precondition: is Id_{V_h} in the span of the zero modes
o(c) = c[0] |_{V_h}, c in V_w, of the Heisenberg vertex algebra?  (If a family a_x, b_v in V_h
were local of order H = 2h - w < 2h, then sum_s Q^H_s(a_x, b_v) = o(a_{x,(H-1)} b_v) with
a_{x,(H-1)} b_v in V_w, and the pieces would need o(...) = d [x=v] Id on V_h.)
Also records dim span{o(c) : c in V_w} inside End(V_h) (dimension p(h)^2).
"""
import sys, math
sys.path.insert(0, '.')
from rho_fock_lib import partitions, p, op_mono
from flint import nmod_mat

PR = (1 << 61) - 1


def zero_mode_matrix(mu, h):
    """o(t^mu) on V_h as a p(h) x p(h) integer matrix (rows: output partition, cols: input)."""
    parts = partitions(h)
    idx = {q: i for i, q in enumerate(parts)}
    n = len(parts)
    M = [[0] * n for _ in range(n)]
    for j, sg in enumerate(parts):
        for tau, c in op_mono(mu, 0, sg).items():
            M[idx[tau]][j] = c
    return M


def main():
    for h in [2, 3, 4, 5, 6]:
        parts = partitions(h)
        n = len(parts)
        for w in range(1, 9):
            vecs = []
            for mu in partitions(w):
                M = zero_mode_matrix(mu, h)
                vecs.append([M[i][j] % PR for i in range(n) for j in range(n)])
            ident = [1 if i == j else 0 for i in range(n) for j in range(n)]
            r0 = nmod_mat(vecs, PR).rank() if vecs else 0
            r1 = nmod_mat(vecs + [ident], PR).rank()
            print(f"h={h} (dim V_h={n:3d}, dim End={n*n:4d})  w={w}: dim o(V_w)|V_h = {r0:4d}   Id in span: {r1 == r0}")
        print()


if __name__ == "__main__":
    main()
