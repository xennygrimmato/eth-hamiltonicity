#!/usr/bin/env python3
"""Bounds on the true four-party network cost of the pieces, from the exact flattening ranks.

Reads the tables written by psi_build.py (out/r_*.txt).  For every N:
  LB = value of the cut LP on K4 (min sum of log2 bond dimensions subject to: bonds across every cut
       >= log2 of the flattening rank), computed from the seven exact ranks;
  UB = min( gather at one party,  2 min(log d1, log d2) + log2 rank(ab|cd),  the same with rank(ad|bc),
            log d1 + log d2 + log2 rank(ac|bd) )     (two-hub networks of Lemma A.3 with the TRUE ranks);
  raw = log2 d1 + log2 d2 (the two wires).
Prints LB/raw and UB/raw (cost per bit of the wires).
    four_party.py out/r_2_22_2_22.txt [...]
"""
import sys, re, math
import numpy as np
from game_true import dv
V = dv((0, 1, 2, 3))   # dual vertices, coordinates (single a/c, single b/d, ab|cd, ad|bc, ac|bd) with equal singles
def lb4(la, lb_, lc, ld, rab, rad, rac):
    # general singles: solve the LP directly
    from scipy.optimize import linprog
    # edges: ab ac ad bc bd cd
    A = [[1,1,1,0,0,0],[1,0,0,1,1,0],[0,1,0,1,0,1],[0,0,1,0,1,1],[0,1,1,1,1,0],[1,1,0,0,1,1],[1,0,1,1,0,1]]
    b = [la, lb_, lc, ld, rab, rad, rac]
    res = linprog(np.ones(6), A_ub=-np.array(A), b_ub=-np.array(b), bounds=[(0, None)] * 6, method='highs')
    return res.fun
for fn in sys.argv[1:]:
    L = open(fn).read().splitlines()
    hd = [l for l in L if l.startswith('classes')][0]
    d1, d2 = map(int, re.findall(r'd[12]=(\d+)', hd))
    l1, l2 = math.log2(d1), math.log2(d2)
    raw = l1 + l2
    print(hd)
    print("   N | LB/raw  UB/raw | binding lower bound")
    prev = None
    for l in L:
        m = re.match(r'\s*(\d+) \|\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+) \|', l)
        if not m: continue
        N, ra, rb, rc, rd, rab, rad, rac = map(int, m.groups())
        lg = lambda x: math.log2(x)
        lb = lb4(lg(ra), lg(rb), lg(rc), lg(rd), lg(rab), lg(rad), lg(rac))
        ub = min(raw + min(l1, l2), 2 * min(l1, l2) + lg(rab), 2 * min(l1, l2) + lg(rad), raw + lg(rac))
        singles = (lg(ra) + lg(rb) + lg(rc) + lg(rd)) / 2
        pairs = (lg(rab) + lg(rad) + lg(rac)) / 2
        why = 'pair cuts' if pairs >= singles - 1e-9 else 'single cuts'
        row = (round(lb / raw, 4), round(ub / raw, 4), why)
        if row != prev:
            print(f"{N:4d} | {lb/raw:.4f}  {ub/raw:.4f} | {why}")
        prev = row
