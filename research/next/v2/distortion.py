"""How far is a Euclidean cone over a circle from Hilbert space?

Points (r, t) of the cone over a circle of length L.  Squared distance: r^2 + s^2 - 2 r s cos(min(angle, pi)).
If u(t) are unit vectors in a Hilbert space with <u(t), u(t')> = k(angle), then |r u(t) - s u(t')|^2 = r^2 + s^2 - 2 r s k.
With a (1 - cos min(a,pi)) <= 1 - k(a) <= b (1 - cos min(a,pi)) and a <= 1 <= b, the map (r,t) -> r u(t) changes squared distances by
factors in [a, b]  (Lean: EthFollowup.Spectral.coneSq_bounds).  So the Euclidean distortion of the whole cone is at most sqrt(b/a).
Lower bound for long circles: m directions pairwise at angle >= pi need inner products >= -1/(m-1), so far pairs lose a factor
2 in squared distance while near pairs lose none: distortion >= sqrt 2, the same as for a star.
Kernel used: periodised Gaussian k(x) = sum_n exp(-c (x + n L)^2) / normalisation, which is positive definite on the circle."""
import numpy as np, math
pi = math.pi
def kernel(L, c, x):
    n = np.arange(-60, 61)[:, None]
    num = np.exp(-c*(x[None, :] + n*L)**2).sum(0)
    den = np.exp(-c*(n[:, 0]*L)**2).sum()
    return num/den
def ratio_range(L, c, m=20001):
    x = np.linspace(1e-4, L/2, m)
    k = kernel(L, c, x)
    tgt = 1 - np.cos(np.minimum(x, pi))
    rr = (1 - k)/tgt
    return rr.min(), rr.max()
def best(L):
    out = None
    for c in np.linspace(0.05, 1.5, 291):
        lo, hi = ratio_range(L, c)
        # the radial part (r - s)^2 is kept exactly, so the squared-distance ratio ranges over [min(lo,1), max(hi,1)]
        d2 = max(hi, 1.0)/min(lo, 1.0)
        if out is None or d2 < out[0]: out = (d2, c, lo, hi)
    return out
if __name__ == "__main__":
    print("L/pi   best c   (1-k)/(1-cos) in [lo, hi]   Euclidean distortion of the cone <= sqrt(max(hi,1)/min(lo,1))")
    for L in [2.5*pi, 3*pi, 4*pi, 6*pi, 10*pi, 40*pi, 400*pi]:
        d2, c, lo, hi = best(L)
        print("%6.1f  %6.3f   [%.4f, %.4f]            %.4f" % (L/pi, c, lo, hi, math.sqrt(d2)))
    # positive definiteness check on a grid for L = 3 pi
    L = 3*pi; d2, c, lo, hi = best(L); t = np.linspace(0, L, 240, endpoint=False)
    D = np.abs(t[:, None] - t[None, :]); D = np.minimum(D, L - D)
    K = kernel(L, c, D.ravel()).reshape(D.shape)
    print("L = 3 pi: smallest eigenvalue of the kernel matrix on 240 directions: %.2e (>= 0 up to rounding)" % np.linalg.eigvalsh(K).min())
    # direct check on random points of the cone
    rng = np.random.default_rng(1); w, U = np.linalg.eigh(K); F = U*np.sqrt(np.clip(w, 0, None))      # rows = unit vectors u(t_i)
    worst = [9, 0]
    for _ in range(200000):
        i, j = rng.integers(0, 240, 2); r, s = rng.random(2)*2
        if i == j and abs(r - s) < 1e-6: continue
        a = min(abs(t[i]-t[j]), L - abs(t[i]-t[j]))
        dc = r*r + s*s - 2*r*s*math.cos(min(a, pi)); de = ((r*F[i] - s*F[j])**2).sum()
        if dc > 1e-9: worst = [min(worst[0], de/dc), max(worst[1], de/dc)]
    print("L = 3 pi: ratio of squared distances (Hilbert image / cone) over 200000 random pairs in [%.4f, %.4f]" % tuple(worst))
