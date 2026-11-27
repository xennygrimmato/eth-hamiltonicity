#!/usr/bin/env python3
"""Example H of research/sat3/loglog.md ("guarded bundles"), small exact experiments.

H(G, Y, Delta): guards x_1..x_G, variables y_1..y_Y, and for each guard i a bundle of Delta clauses
(x_i v u v w) with u, w random literals of two distinct y-variables.  A solution is a pair (S, y):
S = set of false guards, and y satisfies every 2-clause (u v w) of the bundles of S.

For the chain Phi_t = first Delta_t = 2^t clauses of every bundle, t = 0..T, the script computes exactly
  f_t  = max number of false guards in a solution of Phi_t,
  N_t  = max { |V_{t+1}(xi)| : xi |= Phi_t }   (violated clauses of the next level; the number of marks
         the level identity of loglog.md needs at level t),
and the counts #SAT(Phi_t).  Claim tested: N_t does not decay with t (it stays a constant fraction of
the number of variables), although f_t falls like 1/Delta_t.

Second table: the three costs per variable for H at large n (formulas of loglog.md, section 6):
  plain clause network   Delta/2 * e          (one bit per clause, e = (log2 n)^(-1/2))
  marks                  (1/2) log2(2 e_ Delta) * e      (n/2 active clauses, address log2(2 e_ Delta) bits)
  publish S              (1/(2 Delta)) log2(2 e_ Delta)  (entropy of the set of false guards)
"""
import numpy as np, sys
from math import log2, e as E_

def build(G, Y, Delta, rng):
    u = rng.integers(0, Y, size=(G, Delta)); w = rng.integers(0, Y - 1, size=(G, Delta))
    w = np.where(w >= u, w + 1, w)
    su = rng.integers(0, 2, size=(G, Delta)); sw = rng.integers(0, 2, size=(G, Delta))
    return u, w, su, sw

def run(G, Y, T, seed):
    rng = np.random.default_rng(seed)
    Delta = 1 << T
    u, w, su, sw = build(G, Y, Delta, rng)
    ys = np.arange(1 << Y, dtype=np.int64)
    # dng[i][j] = array over y: clause j of bundle i has both y-literals false
    pref_ok = np.ones((G, 1 << Y), dtype=bool)        # bundle prefix satisfied so far
    out = []
    viol_prev = None
    start = 0
    for t in range(T + 1):
        end = 1 << t
        newviol = np.zeros((G, 1 << Y), dtype=np.int16)
        for i in range(G):
            for j in range(start, end):
                lu = ((ys >> u[i, j]) & 1) == su[i, j]      # literal u true
                lw = ((ys >> w[i, j]) & 1) == sw[i, j]
                newviol[i] += (~(lu | lw)).astype(np.int16)
        if t > 0:
            # N_{t-1}: xi |= Phi_{t-1}: guards false only where prefix (before adding level t) ok
            Nprev = int((newviol * pref_ok).sum(axis=0).max())
        pref_ok &= (newviol == 0)
        nsat_guards = pref_ok.sum(axis=0)                  # number of bundles satisfied by y
        f_t = int(nsat_guards.max())
        # #SAT(Phi_t) = sum_y 2^{#satisfied bundles}
        cnt = int(np.sum(np.left_shift(np.int64(1), nsat_guards.astype(np.int64))))
        out.append((t, end, f_t, cnt, Nprev if t > 0 else None))
        start = end
    return out

if __name__ == "__main__":
    G, Y, T = 20, 20, 4
    print(f"H with G={G} guards, Y={Y} y-variables, Delta up to {1 << T}; n = {G + Y}")
    print("  seed  level t  Delta_t  f_t (max false guards)  log2 #SAT(Phi_t)   N_{t-1} (marks at previous level)")
    for seed in (1, 2, 3):
        for (t, d, f, cnt, N) in run(G, Y, T, seed):
            print(f"  {seed:4d}  {t:7d}  {d:7d}  {f:22d}  {log2(cnt):16.2f}   {'' if N is None else N}")
    print()
    print("costs per variable for H(Delta), divided by e = (log2 n)^(-1/2) where they are engine bits:")
    print("  Delta   plain = Delta/2   marks = 0.5 log2(2e Delta)   publish/e at log2 n = 2^20   publish/e at 2^40")
    for D in (2, 4, 8, 16, 32, 64, 256, 1024, 4096, 2 ** 20):
        mk = 0.5 * log2(2 * E_ * D)
        pub = (1 / (2 * D)) * log2(2 * E_ * D)
        print(f"  {D:7d}   {D / 2:10.1f}   {mk:10.2f}   {pub * 2 ** 10:14.2f}   {pub * 2 ** 20:14.2f}")
    print("  (publish is O(1) in these units only when Delta >~ sqrt(log n) log log n; marks grow like log Delta)")
    sys.exit(0)
