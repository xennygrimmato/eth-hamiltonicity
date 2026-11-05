# Supplementary numbers: (a) p_t per level for the near-minimal uniform profile; (b) hypothetical total degree
# D = c*lam needed to reach exponents 4, 23/6, 3.5 (D.1 kernel's Smith profiles, D.1's 14-node grid, A=3);
# (c) packet size A=4 (L=16): D.1 taper and best profile (set K4A=4).
import math, os
import k4_cost as kc
from k4lib import *
A = kc.A; L = kc.L
lp = 4
PROF = kc.profiles(lp)
print(f"A={A}, L={L}; nodes {len(kc.NODES)}")
for k in (1, 4, 16):
    lam = lp * k; M = 6 * lam; deg = M * (2 * L - 1); nn = len(kc.NODES)
    q = -(-(deg + 1) // nn)
    w, det, Q = kc.evaluate(PROF, k, lam, {i: q for i in range(3)}, 1)
    print(f" lam={lam}: uniform q={q} (Sum={Q} > deg {deg}): worst log_N R = {w:.4f}; per level (t, q_t, v2E_t(0), p_t, log_N R_t, max total valuation):")
    for i in sorted(det): print("    level", i, det[i][:3])
    wt, dt, Qt = kc.evaluate(PROF, k, lam, {0: 3 * M, 1: 2 * M, 2: M}, 1)
    print(f"    D.1 taper: worst log_N R = {wt:.4f}")
if A == 3:
    k = 16; lam = 64
    cum = {t: kc.cumul(PROF[t], k) for t in kc.NODES}
    def best_for(deg):
        best = (9e9, None); rng = range(0, deg // 4 + 2, 2)
        for q0 in rng:
            for q1 in rng:
                rem = deg + 1 - 8 * q0 - 4 * q1; q2 = max(0, -(-rem // 2))
                hp, Q = hermite_precisions(A, {0: q0, 1: q1, 2: q2}, 1); w = 0
                for t, (i, qt, vE, pt) in hp.items():
                    R = kc.R_at(cum[t], pt); w = max(w, math.log2(R) / lam if R else 0)
                    if w >= best[0]: break
                if w < best[0]: best = (w, (q0, q1, q2))
        return best
    for c in (22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 10):
        b = best_for(c * lam); print(f"  hypothetical D = {c}*lam: best worst exponent {b[0]:.4f} at {b[1]}")
