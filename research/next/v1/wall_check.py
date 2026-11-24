# Numerical check of the wall lemma: if S = 0 on intersecting pairs and S >= 1 on disjoint pairs (2^d x 2^d),
# then gamma_2(S) >= (2/sqrt 3)^d.  Witness: u = w^{(x)d}, W = polar factor of M = R1 o (w w^T); <W^{(x)d} o (u u^T), S> >= (2/sqrt3)^d.
import numpy as np, functools
t = np.arctan(1/np.sqrt(2))                    # optimal angle: cos^2 = 2/3
w = np.array([np.cos(t), np.sin(t)]); R1 = np.array([[1., 1.], [1., 0.]])
M = R1*np.outer(w, w); U, s, Vt = np.linalg.svd(M); W = U @ Vt
print("trace norm of M =", s.sum(), " 2/sqrt3 =", 2/np.sqrt(3), " polar factor W =", W.round(4).tolist())
Qw = W*np.outer(w, w)                           # dual witness for one coordinate; entries on the support of R1 are positive
print("witness entries on support:", Qw[0, 0], Qw[0, 1], Qw[1, 0])
rng = np.random.default_rng(0)
for d in [2, 3, 4, 5]:
    Q = functools.reduce(np.kron, [Qw]*d); R = functools.reduce(np.kron, [R1]*d)
    ok = (Q[R > 0] > 0).all()
    S = R*(1 + 3*rng.random(R.shape))           # any matrix >= 1 on the support, 0 off it
    print("d=%d  witness positive on support: %s   <Q,R> = %.6f   (2/sqrt3)^d = %.6f   <Q,S> = %.4f >= bound: %s"
          % (d, ok, (Q*R).sum(), (2/np.sqrt(3))**d, (Q*S).sum(), (Q*S).sum() >= (2/np.sqrt(3))**d - 1e-9))
