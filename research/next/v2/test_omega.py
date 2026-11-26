# The same linear programme with one more valid inequality: for any three sites,
#   perimeter <= (9/4) * delta(triple)       (price form of omega <= 9/4: three wires are a restriction of a shared label of rank n^omega)
import math, itertools
from cone import *
from scipy.stats import norm
pi = math.pi
def add_omega(lp):
    n = lp.n
    for i, j, k in itertools.combinations(range(n), 3):
        per = lp.D[i, j] + lp.D[j, k] + lp.D[i, k]
        lp._add([(lp.mask([i, j, k]), -9/4)], -per, "omega")
X = Cone(3*pi); legs = [0, pi, 2*pi]
pts = [(1.0, t) for t in legs] + [(0.0, 0.0)] + [(0.5, t) for t in legs]
lp = RateLP(X, pts, convex_k=3); add_omega(lp)
print("tripod, unit arms, with the omega inequality: delta(tips) in", tuple(round(v, 4) for v in lp.range_of(lp.mask([0, 1, 2]))), " (8/3 = %.4f)" % (8/3))
n = 3; print("OpenAI's ball lemma (three sites at radius 1, space multiplied by l_2): delta <= sqrt(2 pi) n phi(Phi^-1(1 - 1/n)) = %.4f" % (math.sqrt(2*pi)*n*norm.pdf(norm.ppf(1 - 1/n))))
for L, lab in [(3*pi, "3 pi"), (4*pi, "4 pi")]:
    X = Cone(L); pts = [(1.0, i*L/6) for i in range(6)] + [(0.0, 0.0)]
    lp = RateLP(X, pts, convex_k=3); add_omega(lp)
    r = lp.range_of(lp.mask(range(6)))
    print("cone over a circle of length %s, six unit sites + tip: %s" % (lab, "delta(all six) in (%.4f, %.4f): consistent" % r if r else "INFEASIBLE"))
