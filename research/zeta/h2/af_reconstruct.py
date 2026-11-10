#!/usr/bin/env python3
"""h2: which reading of A-F Remark 7.2 (K=1.263, lam=3/2) gives R ~ 1.189 (0.811 / 0.905)?
Uses h5/family_opt.optimise (read-only import)."""
import sys, numpy as np
sys.path.insert(0, '/home/user/eth-hamiltonicity/research/zeta/h5')
from family_opt import optimise, R_of
K = 1.263
variants = {
 'A: F=a (a<=1), K*a (a>1)            ': lambda a: np.where(a <= 1, a, K*a),
 'B: F=K*a everywhere (LS for all a)  ': lambda a: K*a,
 'C: delta also scaled: handled below ': None,
 'D: F=a (a<=1), K (a>1) [flat cap]   ': lambda a: np.where(a <= 1, a, K),
 'E: F=min(a,1)*K                     ': lambda a: K*np.minimum(a, 1.0),
 'F: F=a (a<=1), 1+K*(a-1) (a>1)      ': lambda a: np.where(a <= 1, a, 1+K*(a-1)),
 'G: F=a (a<=1), a+ (K-1) (a>1)       ': lambda a: np.where(a <= 1, a, a+K-1),
}
for lam in (1.25, 1.5, 1.75, 1.99):
    print('lam', lam)
    for name, Ft in variants.items():
        if Ft is None: continue
        R, Rf, u, psi = optimise(lam, Ft, n=400)
        print('  %s opt R=%.4f -> %.4f / %.4f | flat R=%.4f -> %.4f' % (name, R, 2-R, (3-R)/2, Rf, 2-Rf))
    # C: whole energy (delta + F) scaled by K: R_C = K * R_{F=a}
    R, Rf, u, psi = optimise(lam, lambda a: a, n=400)
    print('  C: K*(delta + a) everywhere           opt R=%.4f -> %.4f / %.4f | flat -> %.4f' % (K*R, 2-K*R, (3-K*R)/2, 2-K*Rf))

print('--- cos-family windows psi=cos(c u) on [-lam/2,lam/2], variant A/G/B, target R=1.189..1.190')
def Rw(lam, Ft, c, n=600):
    h = lam/n; u = -lam/2 + h*(np.arange(n)+0.5)
    return R_of(np.cos(c*u), u, h, Ft)
for nm in ['A: F=a (a<=1), K*a (a>1)            ', 'G: F=a (a<=1), a+ (K-1) (a>1)       ', 'B: F=K*a everywhere (LS for all a)  ']:
    Ft = variants[nm]
    for lam in (1.5,):
        out = []
        for c in (0.0, 0.5, 2**-.5, 1.0, 2**.5, 1.6, 1.8, 2.0):
            out.append('c=%.3f:%.4f' % (c, 2-Rw(lam, Ft, c)))
        print(nm, 'lam', lam, ' '.join(out))
# which K reproduces 0.811 at lam=1.5 for optimal window in variant A?
for Kt in (1.263, 1.5, 1.6, 1.7, 1.8, 2.0):
    R, Rf, u, psi = optimise(1.5, lambda a: np.where(a <= 1, a, Kt*a), n=400)
    print('variant A, lam=1.5, K=%.3f -> %.4f / %.4f' % (Kt, 2-R, (3-R)/2))
