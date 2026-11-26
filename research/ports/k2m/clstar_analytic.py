"""[N] sanity check of the analytic proof of (CL*) (notes Theorem D):
 Phi(s) = (1/2) sum_i sqrt((c_ij+c_ik)^2 + 10 (s_ij - s_ik)^2) - 3 + (3/2) sum_{i<j} |s_ij + s_ji|,  s in [-1,1]^6,
 chain:  Phi >= L1 := (1/2) sum_i [cosX (c_ij+c_ik) + sqrt(10) sinX |s_ij - s_ik|] - 3 + (3/2) E     (Cauchy-Schwarz)
             >= L2 := 3 cosX sqrt(1-m^2) + (3m/2)(V+E) - 3,     sinX = 3m/sqrt(10),  m = max|s|
             >= L3 := 3 cosX sqrt(1-m^2) + 3 m^2 - 3            (hexagon lemma V+E >= 2m)
             >= 0.
Also the weighted version (0 < w <= 1) and the direct check of the hexagon lemma."""
import numpy as np
rng = np.random.default_rng(3)
def pieces(s):
    s12, s13, s21, s23, s31, s32 = s
    c = np.sqrt(1 - s*s); c12, c13, c21, c23, c31, c32 = c
    verts = [((c12+c13), (s12-s13)), ((c21+c23), (s21-s23)), ((c31+c32), (s31-s32))]
    E = abs(s12+s21) + abs(s13+s31) + abs(s23+s32)
    V = sum(abs(d) for _, d in verts)
    return verts, V, E, c
worst = [np.inf]*5; bad = 0
for t in range(400000):
    kind = t % 4
    if kind == 0: s = rng.uniform(-1, 1, 6)
    elif kind == 1: s = np.clip(rng.choice([-1, 1], 6) + 0.1*rng.normal(size=6), -1, 1)
    elif kind == 2: s = 0.2*rng.normal(size=6).clip(-5, 5)
    else: s = np.sin(rng.uniform(-np.pi/2, np.pi/2, 6))
    w = 1.0 if t % 3 else rng.uniform(0.05, 1.0)
    K = 9/(w*w)                       # Phi_w: constant 1 + 9/w^2 inside, 3/(2w) outside
    verts, V, E, c = pieces(s)
    m = np.max(np.abs(s))
    Phi = 0.5*sum(np.sqrt(p*p + (1+K)*d*d) for p, d in verts) - 3 + 3/(2*w)*E
    sinX = 3*m/np.sqrt(9 + w*w); cosX = np.sqrt(1 - sinX**2)
    L1 = 0.5*sum(cosX*p + np.sqrt(1+K)*sinX*abs(d) for p, d in verts) - 3 + 3/(2*w)*E
    L2 = 3*cosX*np.sqrt(1-m*m) + 3*m/(2*w)*(V+E) - 3
    L3 = 3*cosX*np.sqrt(1-m*m) + 3*m*m/w - 3
    gaps = [Phi-L1, L1-L2, L2-L3, L3, V+E-2*m]
    worst = [min(a, b) for a, b in zip(worst, gaps)]
    if min(gaps) < -1e-12: bad += 1
print("min of (Phi-L1, L1-L2, L2-L3, L3, V+E-2m) over 400000 points:", ["%.3e" % x for x in worst], " violations:", bad)
