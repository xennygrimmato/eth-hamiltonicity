"""Tripod with arms a1, a2, a3 inside (tripod x Hilbert space), spine through the centre.

Upper bound (OpenAI, HC paper, Lemma "Diagonal price in a ball", last display of the proof; = the book bound):
     delta(tips) <= U(a) = min_t sqrt(2 pi) ( t + sum_i E (a_i G - t)_+ )
Lower bound (OpenAI, omega paper, Proposition "Tripod principle"):
     delta(tips) >= D*(a) = a1 + a2 + a3 - 1/(1/a1 + 1/a2 + 1/a3)
A point with U(a) < D*(a) would show that tripod x l_2 is not a price geometry (given both quoted statements).
"""
import math, numpy as np
from scipy import optimize, stats
def tail(x): return stats.norm.pdf(x) - x*(1 - stats.norm.cdf(x))          # E (G - x)_+
def U(a):
    f = lambda t: math.sqrt(2*math.pi)*(t + sum(ai*tail(t/ai) for ai in a if ai > 0))
    res = optimize.minimize_scalar(f, bounds=(0, 3*max(a)), method="bounded", options={"xatol": 1e-10})
    return res.fun
def Dstar(a): return sum(a) - 1/sum(1/ai for ai in a)
best = (9, None)
grid = np.concatenate([np.linspace(0.02, 1, 50), np.linspace(1.1, 6, 50)])
for a1 in grid:
    for a2 in grid:
        if a2 < a1: continue
        a = (a1, a2, 1.0); r = U(a)/Dstar(a)
        if r < best[0]: best = (r, a)
print("min over arms of U/D* = %.5f at arms %s" % (best[0], tuple(round(x, 3) for x in best[1])))
for a in ((1, 1, 1), (1, 1, 0.5), (1, 1, 0.1), (1, 0.5, 0.5), (1, 1, 3), (1, 1, 10), (1, 3, 3)):
    print("arms %-14s U = %.5f  D* = %.5f  ratio %.5f  perimeter/U = %.5f" % (a, U(a), Dstar(a), U(a)/Dstar(a), 2*sum(a)/U(a)))
