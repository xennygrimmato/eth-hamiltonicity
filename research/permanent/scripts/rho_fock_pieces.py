"""True ranks of the Appendix-B pieces A_s versus the paper's counts, and the structure of the family.

For each h: builds A_s exactly (labels x, v = all partitions of h, so N = p(h)), checks
  (1) sum_s A_s = h! [x=v][y=u]                                   (Lemma 9(c) + Lemma 10),
  (2) Lemma 9(a) numerically for a few s (both orders give the same tensor),
  (3) the row rank (x,y)|(u,v) and column rank (x,u)|(y,v) of every A_s, mod a 61-bit prime
      (a rank mod p is <= the rank over Q; equality is generic), against R^row_s, R^col_s
      and against p(2h+s), p(2h-s),
  (4) the linear independence of the 4h+1 tensors A_s (so no proper sub-family, with any
      coefficients, is a multiple of the crossing),
  (5) the exact rho(h) = max_s (log2 r_s + log2 o_s) / (4 log2 N), the counted version, and
      the "general law" value log2 p(2h) / (2 log2 p(h)).
Usage: python3 rho_fock_pieces.py 3 4 5 6 7 8
"""
import sys, math, time
sys.path.insert(0, '.')
from rho_fock_lib import partitions, p, piece_tensor, count_bounds
from flint import nmod_mat

PR = (1 << 61) - 1


def rank_mod(rows, ncols):
    """rows: list of dicts col->int.  Rank mod PR."""
    if not rows:
        return 0
    M = [[0] * ncols for _ in rows]
    for i, r in enumerate(rows):
        for j, v in r.items():
            M[i][j] = v % PR
    return nmod_mat(M, PR).rank()


def run(h, check_lemma9a=True):
    parts = partitions(h)
    N = len(parts)
    hf = math.factorial(h)
    lam = math.log2(N)
    total = {}
    pieces = {}
    t0 = time.time()
    for s in range(-2 * h, 2 * h + 1):
        _, _, T = piece_tensor(h, s)
        if check_lemma9a and abs(s) <= 1:
            _, _, T2 = piece_tensor(h, s, order="col" if s <= 0 else "row")
            assert T == T2, f"Lemma 9(a) fails numerically at h={h}, s={s}"
        pieces[s] = T
        for k, v in T.items():
            total[k] = total.get(k, 0) + v
    ok = all(total.get((x, y, u, v), 0) == (hf if (x == v and y == u) else 0)
             for x in range(N) for y in range(N) for u in range(N) for v in range(N))
    print(f"h={h}  N=p(h)={N}  lam=log2 N={lam:.3f}  identity sum_s A_s = h![x=v][y=u]: {ok}"
          f"   (build {time.time()-t0:.1f}s)")
    worst = 0.0
    worst_cnt = 0.0
    rows_for_indep = []
    for s in range(-2 * h, 2 * h + 1):
        T = pieces[s]
        if not T:
            print(f"  s={s:3d}  A_s = 0")
            continue
        Mr = {}
        Mc = {}
        for (x, y, u, v), val in T.items():
            Mr.setdefault(x * N + y, {})[u * N + v] = val
            Mc.setdefault(x * N + u, {})[y * N + v] = val
        rr = rank_mod([Mr[k] for k in sorted(Mr)], N * N)
        rc = rank_mod([Mc[k] for k in sorted(Mc)], N * N)
        Rrow, Rcol = count_bounds(h, s)
        bits = math.log2(rr) + math.log2(rc)
        cbits = math.log2(min(Rrow, N * N)) + math.log2(min(Rcol, N * N))
        worst = max(worst, bits)
        worst_cnt = max(worst_cnt, cbits)
        print(f"  s={s:3d}  rank_row={rr:6d} [count {Rrow:7d}, p(2h+s)={p(2*h+s):6d}]"
              f"  rank_col={rc:6d} [count {Rcol:7d}, p(2h-s)={p(2*h-s):6d}]"
              f"  bits={bits:6.2f}  count-bits={cbits:6.2f}")
        row = {}
        for (x, y, u, v), val in T.items():
            row[((x * N + y) * N + u) * N + v] = val
        rows_for_indep.append(row)
    rk = rank_mod(rows_for_indep, N ** 4)
    print(f"  number of nonzero pieces = {len(rows_for_indep)}; rank of the family = {rk}"
          f" -> linearly independent: {rk == len(rows_for_indep)}")
    law = math.log2(p(2 * h)) / (2 * math.log2(p(h)))
    print(f"  rho_true(h) = {worst/(4*lam):.4f}   rho_count(h) = {worst_cnt/(4*lam):.4f}"
          f"   law f(2h)/(2f(h)) = {law:.4f}   1/sqrt2 = {1/math.sqrt(2):.4f}   4lam = {4*lam:.2f}")
    return worst / (4 * lam), worst_cnt / (4 * lam)


if __name__ == "__main__":
    for h in [int(a) for a in sys.argv[1:]]:
        run(h)
