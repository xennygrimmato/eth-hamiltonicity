"""Anthropic's contracting hypothesis, tested on geometries close to Hilbert space.

Hypothesis (paper, Def. 2.1): for some mu >= 2 and some s with s^2 < mu, every price on Mat_mu(F_2) has D(mu) <= s D(1),
where D(r)^2 is the mean squared distance between two matrices whose difference has rank r.

Hilbert metrics.  Averaging over translations keeps D(r) and keeps the metric Hilbert, so d(a, a+W)^2 = f(W) with
f(W) = sum_{B != 0} c_B (1 - chi_B(W)),  c_B >= 0,  chi_B(W) = (-1)^{<B,W>}.  Hence
    max over Hilbert metrics of D(mu)^2 / D(1)^2  =  max over B != 0 of  (1 - K_mu(B)/N_mu) / (1 - K_1(B)/N_1),
K_r(B) = sum over rank-r W of chi_B(W), N_r = number of rank-r matrices; K_r(B) depends only on rank B.
If every price is within Euclidean distortion c (squared distances within a factor c^2), the same ratio is at most c^2 times this."""
import itertools
def rank2(rows, mu):
    rows = list(rows); r = 0
    for bit in range(mu):
        piv = next((i for i in range(r, len(rows)) if rows[i] >> bit & 1), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i] >> bit & 1: rows[i] ^= rows[r]
        r += 1
    return r
print("mu   s_H^2 = max Hilbert ratio D(mu)^2/D(1)^2   (attained at rank B)   contracting needs s^2 < mu   allowed distortion c < sqrt(mu/s_H^2)")
for mu in [2, 3, 4]:
    mats = list(itertools.product(range(2**mu), repeat=mu)); rk = [rank2(m, mu) for m in mats]
    N = [rk.count(r) for r in range(mu + 1)]
    best = (0, None)
    for s in range(1, mu + 1):
        B = tuple((1 << i) if i < s else 0 for i in range(mu))            # diag(1^s, 0)
        K = [0]*(mu + 1)
        for W, r in zip(mats, rk):
            K[r] += (-1)**sum(bin(b & w).count("1") for b, w in zip(B, W))
        ratio = (1 - K[mu]/N[mu])/(1 - K[1]/N[1])
        if ratio > best[0]: best = (ratio, s)
    print("%2d   %.4f                                      (rank %d)             %s                 c < %.3f"
          % (mu, best[0], best[1], "yes" if best[0] < mu else "NO", (mu/best[0])**0.5))
print("Stars: d(x,y) = t_x + t_y gives D(mu)^2/D(1)^2 <= 2 for every mu (both are between 2 E t^2 and 4 E t^2).")
