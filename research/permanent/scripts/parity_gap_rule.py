#!/usr/bin/env python3
"""Consequence of the observed rule (parity_general_interface.out, 69/69 level sets, Q<=5):
in the GENERAL interface with eigen-level measurements, a level set J is admissible at degree
R-1 iff every run of consecutive levels in J has length <= R.  Best such J: delete one level
every R+1 levels (optimal offset).  We compare the R needed at fixed eps with
  LB  : the lower bound for every M0 in the TEMPLATE (Pr[Bin(2Q,1/2) >= Q+R] <= eps),
  WIN : OpenAI's window,
  GAP : the gap rule (general interface, conjectural extrapolation of the rule to large Q).
p = 1/2 (r -> infinity) and p = 1/4 (r = 2)."""
from math import lgamma, log, exp, sqrt
def pmf(Q, p):
    return [exp(lgamma(Q+1)-lgamma(j+1)-lgamma(Q-j+1)+j*log(p)+(Q-j)*log(1-p)) for j in range(Q+1)]
def gap_eps(Q, R, pm):
    best = 1.0
    for off in range(R + 1):
        best = min(best, sum(pm[j] for j in range(off, Q + 1, R + 1)))
    return best
def win_eps(Q, R, pm):
    return max(0.0, 1 - max(sum(pm[a:a+R]) for a in range(Q - R + 2)))
def lb_eps(Q, R):
    N = 2*Q
    return sum(exp(lgamma(N+1)-lgamma(k+1)-lgamma(N-k+1)-N*log(2)) for k in range(Q+R, N+1))
def first(fn, Q, eps):
    for R in range(1, Q + 2):
        if fn(R) <= eps: return R
for p in (0.5, 0.25):
    for eps in (1e-1, 1e-2, 1e-3, 1e-5):
        print(f"-- p={p} eps={eps}:   Q  R_LB(template, all M0)  R_win  R_gap(general, conj.)")
        for Q in (16, 64, 256, 1024, 4096):
            pm = pmf(Q, p)
            print(f"   {Q:5d} {first(lambda R: lb_eps(Q,R), Q, eps):8d} {first(lambda R: win_eps(Q,R,pm), Q, eps):8d} {first(lambda R: gap_eps(Q,R,pm), Q, eps):8d}")
