"""Generalized locality is impossible for sparse mode sets (sparse-fock.md, Theorem 3.1).

Setting: a(z) = sum_n a_n z^{-n-1}, b(w) formal distributions, C(z,w) = [a(z), b(w)] != 0, and a nonzero
Laurent polynomial P(z,w) with P(z,w) C(z,w) = 0 (ordinary locality: P = (z-w)^H; twisted: (z^a - w^a)^H).
Writing P = sum_j p_j z^j w^{d-j} (after restricting to a homogeneous component, which still kills C
because C is homogeneous for the grading), the coefficient of z^{-m-1} w^{-(t-m)-1} in P C gives the
constant-coefficient linear recurrence  sum_j p_j C_{m+j, t-m-j+d} = 0  along every anti-diagonal t.
If a_n = 0 for deg P consecutive n (a "gap" of length deg P in the set of nonzero modes), the recurrence
forces every anti-diagonal to vanish, i.e. C = 0.  Hence {n : a_n != 0} has all gaps < deg P.

This script checks the arithmetic content on the sparse Heisenberg current phi_S(z) = sum_{k in S} nabla_k z^{-k-1}:
[phi_S(z), phi_S(w)] = sum_{k in S} k z^{-k-1} w^{k-1} =: z^{-1} w^{-1} F_S(w/z), F_S(q) = sum_{k in S} k q^k.
A homogeneous P kills it iff the sequence c_k = k [k in S] satisfies a linear recurrence with constant
coefficients of order deg P on all of Z, iff the Hankel matrices of (c_k) have bounded rank.
  S = N:          (z-w)^2 works (rank of Hankel = 2):  PASS expected
  S = squares, powers of 2, cubes:  Hankel rank grows without bound (no recurrence of any order <= 40)
Exact arithmetic over Q (fractions) via sympy / flint.
"""
import sys
from flint import fmpq_mat

def hankel_rank(seq, order):
    """rank of the (order+1) x (len-order) Hankel matrix of seq; < order+1 iff a recurrence of order <= order exists on this window."""
    n = len(seq) - order
    M = fmpq_mat(order + 1, n, [seq[i + j] for i in range(order + 1) for j in range(n)])
    return M.rank()

def main():
    L = 400
    fams = {
        "N (all k)": lambda k: k >= 1,
        "squares": lambda k: k >= 1 and int(round(k ** .5)) ** 2 == k,
        "cubes": lambda k: k >= 1 and round(k ** (1/3)) ** 3 == k,
        "powers of 2": lambda k: k >= 1 and (k & (k - 1)) == 0,
        "|k| = +-1 mod 3 (periodic, dense)": lambda k: k >= 1 and k % 3 != 0,
        "k = 1 mod 3 only (S u -S not periodic)": lambda k: k >= 1 and k % 3 == 1,
    }
    ok = True
    for name, ind in fams.items():
        # two-sided: c_k = k for k in S, c_{-k} = -k (from [nabla_{-k}, nabla_k] = -k), window [-L, L] of Z
        seq = [k if ind(abs(k)) else 0 for k in range(-L, L + 1)]
        ranks = [hankel_rank(seq, d) for d in (1, 2, 3, 5, 10, 20, 40)]
        rec = [d for d, r in zip((1, 2, 3, 5, 10, 20, 40), ranks) if r <= d]
        minorder = rec[0] if rec else None
        print(f"{name:42s} Hankel ranks at orders 1,2,3,5,10,20,40: {ranks}   minimal recurrence order: {minorder}")
        expect_rec = name.startswith("N") or name.startswith("|k|")  # S = {1 mod 3} alone: S u -S = {1 mod 3 on k>0, 2 mod 3 on k<0} is not a recurrence set
        if expect_rec != (minorder is not None):
            ok = False
    print("Dense sets (N, arithmetic progressions) admit a polynomial annihilator P(z,w) (ordinary or twisted locality);")
    print("squares, cubes, powers of 2 admit none of order <= 40 (and none at all, by the gap argument).")
    print("PASS" if ok else "FAIL")

if __name__ == "__main__":
    main()
