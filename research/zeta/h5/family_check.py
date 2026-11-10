#!/usr/bin/env python3
"""Evaluate R(psi) for an explicit step window (from the optimiser) on finer grids, so the
reported constant is the value of a concrete admissible window (upper bound for R => valid lower bound)."""
import numpy as np
from family_opt import optimise, Ft_LS
S = 0.47914534724162244; K = 1.5 / S
lam, n = 1.5, 300
_, _, u, psi = optimise(lam, Ft_LS(K), n=n)
Ft = Ft_LS(K)
for rep in [4, 8, 16]:
    m = n * rep; h = lam / m
    uf = -lam / 2 + h * (np.arange(m) + 0.5); pf = np.repeat(psi, rep)
    # fine-grid quadrature: R = [h sum p^2 + h^2 p F p] / (h sum p)^2, diagonal self-average a~h/3 -> Ft(h/3)
    D = np.abs(uf[:, None] - uf[None, :]); F = Ft(D); np.fill_diagonal(F, h / 3)
    R = (h * (pf ** 2).sum() + h * h * pf @ F @ pf) / (h * pf.sum()) ** 2
    print('rep', rep, 'R=%.6f simple>=%.6f distinct>=%.6f' % (R, 2 - R, (3 - R) / 2))
np.savetxt('family_window_lam1.5.txt', np.c_[u, psi], header='u (units of log Q), psi(u); K=3/(2S)')
