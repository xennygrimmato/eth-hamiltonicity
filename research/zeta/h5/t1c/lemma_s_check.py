#!/usr/bin/env python3
"""Check Lemma S (rank-trace slack) in the N-periodic model, configurations WITH off-line pairs.
Gram certificate from a window psi >= 0 on frequencies 0..N-1 (sum psi = 1):
  G = D^{1/2} T D^{1/2},  T_{jk} = S(j-k) (Hermitian for conjugation-symmetric configs; a pair t+-iy is the rank-2 block
  e_z e_zbar^* + e_zbar e_z^*).  Lemma S:  s1 >= 2N - ||G||_F^2 + 2 tr(Q'_-),  Q' = G - P1 (P1 = simple on-line part).
Also prints the isolated-pair formula tr(B_-) = ||u|| ||w|| - 1 ~ 2 y^2 Var_psi(omega)."""
import numpy as np
from scipy.optimize import minimize
N = 8; rng = np.random.default_rng(5)
j = np.arange(N); om = 2 * np.pi * j / N
def r_of(psi): return np.array([np.sum(psi[:N - l] * psi[l:]) for l in range(N)])
def val(psi): r = r_of(psi); return 2 - N * r[0] - (2 / N) * np.sum(r[1:] * np.arange(1, N))
res = minimize(lambda p: -val(np.abs(p) / np.abs(p).sum()), np.ones(N) / N, method='Nelder-Mead', options={'maxiter': 40000, 'xatol': 1e-12, 'fatol': 1e-14})
psi = np.abs(res.x) / np.abs(res.x).sum(); print('periodic MT-type Gram certificate value p_MT(8) =', round(val(psi), 6), ' (h3: 0.67728)')
def vec(z): return np.sqrt(psi) * np.exp(1j * om * z)          # e_z weighted, z complex
worst = 1e9
for trial in range(3000):
    k3 = rng.integers(0, 4); k2 = rng.integers(0, (N - 2 * k3) // 2 + 1); k1 = N - 2 * k2 - 2 * k3
    t = rng.uniform(0, N, k1 + k2 + k3); y = rng.uniform(0, 0.8, k3) * rng.choice([1, 0.1, 0.01], k3)
    P1 = np.zeros((N, N), complex); Qp = np.zeros((N, N), complex)
    for b in range(k1): v = vec(t[b]); P1 += np.outer(v, v.conj())
    for b in range(k2): v = vec(t[k1 + b]); Qp += 2 * np.outer(v, v.conj())
    for p in range(k3):
        z = t[k1 + k2 + p] + 1j * y[p]; u, wv = vec(z), vec(np.conj(z))
        Qp += np.outer(u, wv.conj()) + np.outer(wv, u.conj())
    G = P1 + Qp; assert np.allclose(G, G.conj().T)
    ev = np.linalg.eigvalsh(Qp); trQm = -ev[ev < -1e-12].sum(); pos = ev[ev > 1e-12]; b = k2 + k3
    f = 2 * trQm + np.sum((pos - 2) ** 2) + 4 * (b - len(pos))
    f2 = np.sum(pos ** 2) - 4 * b - 2 * trQm
    assert abs(f - f2) < 1e-8, (f, f2)
    lhs = k1; rhs = 2 * N - np.linalg.norm(G) ** 2 + 2 * trQm
    worst = min(worst, lhs - rhs); worstf = min(globals().get('worstf', 1e9), lhs - (2 * N - np.linalg.norm(G) ** 2 + f)); globals()['worstf'] = worstf
    assert abs(np.trace(G).real - N) < 1e-9
print('min over 3000 random configs of  s1 - [2N - ||G||^2 + 2 tr Q\'_-]  =', worst, '(>= 0 confirms Lemma S)')
print('Lemma S-prime (full Q\' slack f, both forms agree): min surplus =', worstf)
m1 = np.sum(psi * om); var = np.sum(psi * om ** 2) - m1 ** 2
for y in [0.01, 0.05, 0.1, 0.3]:
    u, wv = vec(1j * y), vec(-1j * y); exact = np.linalg.norm(u) * np.linalg.norm(wv) - 1
    print(f'isolated pair y={y}: tr B_- = {exact:.6e}   2 y^2 Var_psi(omega) = {2*y*y*var:.6e}   => Gram slack per pair (s1/N units) >= {2*exact/N:.3e}')
