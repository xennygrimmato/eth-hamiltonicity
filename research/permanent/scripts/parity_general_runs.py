#!/usr/bin/env python3
"""Targeted Q=6 checks of the observed rule R_general(J) = longest run of consecutive levels in J
(parity_general_interface.py; eigen-level measurement spaces, r=2)."""
import sys, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__file__))
from parity_general_interface import build, least_R, template_ok, general_ok
from fractions import Fraction
from math import comb
Q = 6
D, Psi, lev, a, d = build(Q)
pm = [Fraction(comb(Q, j)) * Fraction(1, 4)**j * Fraction(3, 4)**(Q - j) for j in range(Q + 1)]
for J in ([0, 1, 2, 3, 4, 6], [0, 1, 2, 3, 5, 6], [0, 1, 2, 3, 4]):
    B = Psi[:, [i for i in range(D) if lev[i] not in J]]
    eps = 1 - sum(pm[j] for j in J)
    rt = least_R(Q, D, B, a, d, template_ok)
    rg = least_R(Q, D, B, a, d, general_ok)
    print(f"Q=6 J={J} eps={float(eps):.5f} c={B.shape[1]} R_template={rt} R_general={rg}", flush=True)
