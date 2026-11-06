"""ansatz_shape.py -- exact restriction-flattening tests [C, every field] for three-merge ansaetze f_Delta = sum of pieces, each
piece a triangle network with a GIVEN bond shape under its own merge (bound: network min-cut at every bit orientation), and
optionally a total-cost cap b under the two other merges (best shape per orientation, real bonds: a relaxation, so refutations
are exact for every other-merge shape).  Bit orientations: N0 = 2 (3^9) and N0 = 4 (6^9).
Shapes are log2-bonds on the group pairs (01, 02, 12) of the piece's own merge; all placements are tried.
For an ansatz passing with other merges free, the least symmetric other-merge cap b that still passes is reported, with the
uniform-q criterion  V_tot <= (a + 2b)/3 + 1.5 log2 T  (a = own cost) to compare with 4.5 m0 (rho < 1/2) and 9 m0 (any trade)."""
import numpy as np, itertools, sys
from lib3m import *
from ansatz_cost import Phi

def keys(m0):
    idx, X, Y, rk = enumerate_orients(m0)
    L = {k: legs8(X[k], Y[k]) for k in 'rcd'}
    K = np.concatenate([rk[:, None]] + [L[k] for k in 'rcd'], 1).astype(np.int16)
    K = np.unique(K, axis=0)
    rk = K[:, 0].astype(float); L = {k: K[:, 1 + 8 * i: 9 + 8 * i].astype(float) for i, k in enumerate('rcd')}
    M = {k: Mg(L[k]) for k in 'rcd'}
    return rk, L, M

def placements(shape):
    return sorted(set(itertools.permutations(shape)))

def run(m0, rk, L, M, pieces, label, phicache):
    """pieces: list of (merge, logshape, cap) with cap = None (free) or total cost of each other merge."""
    best = None
    for combo in itertools.product(*[placements(s) for (_, s, _) in pieces]):
        tot = np.zeros_like(rk)
        for (k, _, cap), sh in zip(pieces, combo):
            b = logbound(L[k], sh)
            if cap is not None:
                for k2 in 'rcd':
                    if k2 != k:
                        key = (k2, cap)
                        if key not in phicache: phicache[key] = Phi(M[k2], rk, cap)
                        b = np.minimum(b, phicache[key])
            tot += 2.0 ** b
        sl = (np.log2(tot) - rk).min()
        if best is None or sl > best[0]: best = (sl, combo)
        if sl >= -1e-9: break
    return best

if __name__ == '__main__':
    for m0 in (1, 2):
        rk, L, M = keys(m0); pc = {}
        print(f'\nN0 = {2**m0}: {len(rk)} distinct orientation keys; rho<1/2 needs V_tot < {4.5*m0}, any trade < {9*m0}', flush=True)
        if m0 == 1:
            shapes = [(1, 1, 1), (1, 1, 2), (1, 2, 2), (2, 2, 2), (1.585, 1.585, 1.585), (1, 1, 3), (1, 2, 3)]
        else:
            shapes = [(2, 2, 2), (2, 2, 3), (2, 3, 3), (3, 3, 3), (2, 2, 4), (2, 4, 4), (4, 4, 4)]
        for reps in (1, 2):
            for sh in shapes:
                pcs = [(k, sh, None) for k in 'rcd'] * reps
                sl, combo = run(m0, rk, L, M, pcs, '', pc)
                a = sum(sh); T = 3 * reps
                line = (f'  {reps}x(R+C+D), own log-bonds {sh} (cost {a:.3f}), other merges free: best placement slack '
                        f'{sl:+.4f} (log2) {"PASSES" if sl >= -1e-9 else "REFUTED (all placements)"}')
                if sl >= -1e-9:
                    lo, hi = 0.0, 12.0 * m0
                    for _ in range(14):
                        mid = (lo + hi) / 2
                        s2, _ = run(m0, rk, L, M, [(k, sh, round(mid, 4)) for k in 'rcd'] * reps, '', pc)
                        if s2 >= -1e-9: hi = mid
                        else: lo = mid
                    Vt = (a + 2 * hi) / 3 + 1.5 * np.log2(T)
                    line += (f'; least symmetric other-merge cap b = {hi:.3f} -> V_tot (uniform q) >= {Vt:.3f} '
                             f'[rho<1/2 {"refuted" if Vt >= 4.5*m0 else "open"}, trade {"refuted" if Vt >= 9*m0 else "open"}]')
                print(line, flush=True)
