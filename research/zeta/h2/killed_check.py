#!/usr/bin/env python3
"""h2: cross-check D'Souza's constants with h5's QP and price h5's K with D'Souza's killed kernel.
kernel 'lin': F=a (a<=1), C*a (a>1)   [D'Souza [9] / h5 sec 3]
kernel 'kil': F=a (a<=1), C   (a>1)   [D'Souza Thm 1.1: C*min(|a|,1) on the out-zone]"""
import sys, numpy as np
sys.path.insert(0, '/home/user/eth-hamiltonicity/research/zeta/h5')
from family_opt import optimise
S = 0.47914534724162244
for nm, C in [("D'Souza C=pi^4/18", np.pi**4/18), ('h5 K=3/(2S)', 1.5/S), ('classical 2/S', 2/S), ('A-F 1.263', 1.263)]:
    for kern in ('lin', 'kil'):
        Ft = (lambda a, C=C: np.where(a <= 1, a, C*a)) if kern == 'lin' else (lambda a, C=C: np.where(a <= 1, a, C))
        best = max(((2-optimise(lam, Ft, n=240)[0]), lam) for lam in (1.1, 1.2, 1.25, 1.2768, 1.35, 1.5, 1.7, 1.99))
        print('%-20s C=%.4f %s: best simple>=%.4f at lam=%.3f' % (nm, C, kern, best[0], best[1]))
