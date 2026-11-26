"""Where do pieces of rho_2 live?  Checks of isometric embeddings into products of tripods and lines.

A point of a tripod T is (leg, radius); d = |r - s| on one leg, r + s across legs.  Products carry the l_2 metric.
  (a) {0} u {nine rank-one matrices}  ->  T x T x R      (apex over the 3 x 3 grid of diagonal directions)
  (b) H_8 = {0, I, six rank-one W with rk(I - W) = 1}  ->  T x T x R
  (c) the full 16-point rho_2 does NOT extend (b) inside T x T x R (the other invertible matrices have no place)
  (d) X_4(theta) = {m, P1, P3, P4}: m midpoint of P1P3 and of P1P4, |P3P4| = 2 sin(theta/2)  ->  T x R
"""
import itertools, math, numpy as np
from rank2 import mats, rk, add, cell, inv, I, Z, R1, R2, sig

def dT(p, q):
    (a, r), (b, s) = p, q
    return abs(r - s) if (a == b or r == 0 or s == 0) else r + s
def dTTR(p, q): return math.sqrt(dT(p[0], q[0])**2 + dT(p[1], q[1])**2 + (p[2] - q[2])**2)

h = 1/math.sqrt(2)
emb = {Z: ((0, 0.0), (0, 0.0), -h)}
for (i, j), W in cell.items(): emb[W] = ((i, 0.5), (j, 0.5), 0.0)
err = max(abs(dTTR(emb[A], emb[B])**2 - rk[add(A, B)]) for A in emb for B in emb)
print("(a) 0 and the nine rank-one matrices in T x T x R: max error in squared distance %.1e" % err)
H8 = [Z, I] + [W for W in R1 if rk[add(I, W)] == 1]
emb8 = {A: emb[A] for A in H8 if A != I}; emb8[I] = ((0, 0.0), (0, 0.0), +h)
err = max(abs(dTTR(emb8[A], emb8[B])**2 - rk[add(A, B)]) for A in H8 for B in H8)
print("(b) H_8 in T x T x R: max error %.1e" % err)
# H_8 is not Euclidean: Gram test
D2 = np.array([[rk[add(A, B)] for B in H8] for A in H8], float); n = len(H8)
J = np.eye(n) - np.ones((n, n))/n; ev = np.linalg.eigvalsh(-J @ D2 @ J/2)
print("    H_8 centred Gram eigenvalues: min %.4f (negative => not Euclidean)" % ev.min())
D2 = np.array([[rk[add(A, B)] for B in mats] for A in mats], float); n = 16
J = np.eye(n) - np.ones((n, n))/n; ev = np.linalg.eigvalsh(-J @ D2 @ J/2)
print("    rho_2 centred Gram eigenvalues:", np.round(sorted(ev), 3))

# (c) can a further invertible matrix g be added to (a) u {I} inside T x T x R?  Its position (p, q, z) would need
# squared distance 1 to the six cells off its permutation graph and 2 to the three on it; in T x T x R the squared
# distance to cell (i, j) depends only on [i = leg(p)], [j = leg(q)], so the nine values form a rank-one-pattern table.
def feasible(g):
    s = sig[g]; target = {(i, j): (2 if i == s[j] else 1) for i in range(3) for j in range(3)}
    best = 1e9
    grid = np.linspace(0, 1.5, 31)
    for a in range(3):
        for b in range(3):
            for r in grid:
                for t in grid:
                    for z in np.linspace(-1.5, 1.5, 61):
                        p = ((a, r), (b, t), z)
                        e = max(abs(dTTR(p, ((i, 0.5), (j, 0.5), 0.0))**2 - target[(i, j)]) for i in range(3) for j in range(3))
                        best = min(best, e)
    return best
g = next(g for g in R2 if g != I)
print("(c) best fit of another invertible matrix to the nine cells inside T x T x R (grid search): max error %.3f (> 0: no place)" % feasible(g))

# (d) X_4(theta) in T x R: P1 = (leg 0, cos a; +sin a), P3 = (leg 1, cos a; -sin a), P4 = (leg 2, cos a; -sin a), a = (pi - theta)/2
def dTR(p, q): return math.hypot(dT(p[0], q[0]), p[1] - q[1])
for theta in (math.pi/6, math.pi/2, 2.5):
    a = (math.pi - theta)/2
    m = ((0, 0.0), 0.0); P1 = ((0, math.cos(a)), math.sin(a)); P3 = ((1, math.cos(a)), -math.sin(a)); P4 = ((2, math.cos(a)), -math.sin(a))
    print("(d) theta = %.3f: |mP| = %.3f %.3f %.3f, |P1P3| = %.3f, |P1P4| = %.3f, |P3P4| = %.4f (2 sin(theta/2) = %.4f)" % (
        theta, dTR(m, P1), dTR(m, P3), dTR(m, P4), dTR(P1, P3), dTR(P1, P4), dTR(P3, P4), 2*math.sin(theta/2)))
