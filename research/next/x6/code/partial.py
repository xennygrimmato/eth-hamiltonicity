"""Partial-sum (two-term splitting) ranks of the Prop. B.2 pieces, d = 1 (paper) or d-dim product kernel (x5).
A_K = sum_{N<=K} Psi_N, B_K = sum_{N>K} Psi_N.  Reports rk_{ad|bc}(A_K), rk_{ab|cd}(B_K) over Q and F_p,
and piece ranks, to test whether cancellation in partial sums beats the per-piece bounds (mechanism b).
Usage: python3 partial.py d n e     (equal wires, class (n,e) on both)"""
import sys, itertools, math
sys.path.insert(0, '/home/user/eth-hamiltonicity/research/next/x5/code')
from crossing import Bv, Cv, det_int, interpolate, rank_modp, rank_Q
import crossing, crossing_d

def coeffs_for(d, n, e):
    if d == 1:
        S = crossing.symbols(n, e); mat = lambda X, *s: crossing.matrix(X, *s)
    else:
        S = crossing_d.symbols(d, n, e); mat = lambda X, *s: crossing_d.matrix(d, X, *s)
    Th = 4 * e
    co = {}
    for sa in S:
        for sc in S:
            for sb in S:
                for sd in S:
                    vals = [det_int(mat(X, sa, sb, sc, sd)) for X in range(Th + 1)]
                    co[(sa, sb, sc, sd)] = interpolate(vals)
    return S, Th, co

def flat(S, tensor, rp, cp):
    rows = []
    for r in itertools.product(S, S):
        row = []
        for c in itertools.product(S, S):
            s = {rp[0]: r[0], rp[1]: r[1], cp[0]: c[0], cp[1]: c[1]}
            row.append(tensor[(s['a'], s['b'], s['c'], s['d'])])
        rows.append(row)
    return rows

if __name__ == '__main__':
    d, n, e = map(int, sys.argv[1:4])
    S, Th, co = coeffs_for(d, n, e)
    Q = len(S); lq = math.log(Q)
    print(f"d={d} class=({n},{e}) Q={Q} Theta={Th}")
    primes = [0, 2, 3, 5]
    def rk(rows, p):
        return rank_Q(rows) if p == 0 else rank_modp(rows, p)
    keys = list(co)
    Ns = [N for N in range(Th + 1) if any(co[k][N] for k in keys)]
    for p in primes:
        print(f"--- field {'Q' if p == 0 else 'F_%d' % p}")
        print("  K | piece rk ad|bc  ab|cd | partial rk(A_K) ad|bc  rk(B_K) ab|cd | sum of piece rks (bound)")
        best = None; cum_a = 0
        pa = {}; pb = {}
        for N in Ns:
            T = {k: co[k][N] for k in keys}
            pa[N] = rk(flat(S, T, 'ad', 'bc'), p); pb[N] = rk(flat(S, T, 'ab', 'cd'), p)
        for K in Ns:
            A = {k: sum(co[k][N] for N in range(K + 1)) for k in keys}
            B = {k: sum(co[k][N] for N in range(K + 1, Th + 1)) for k in keys}
            ra = rk(flat(S, A, 'ad', 'bc'), p); rb = rk(flat(S, B, 'ab', 'cd'), p)
            sa_ = sum(pa[N] for N in Ns if N <= K); sb_ = sum(pb[N] for N in Ns if N > K)
            m = max(ra, rb, 1)
            if best is None or m < best[0]: best = (m, K, ra, rb)
            print(f"{K:4d} | {pa[K]:5d} {pb[K]:5d} | {ra:8d} {rb:8d} | {sa_:6d} {sb_:6d}")
        m, K, ra, rb = best
        print(f"  balanced split: K={K} max rank {m} = Q^{math.log(m)/lq:.3f};  "
              f"max piece rank sum exp: {max(math.log(max(pa[N],1)*max(pb[N],1)) for N in Ns)/(4*lq):.3f}")
