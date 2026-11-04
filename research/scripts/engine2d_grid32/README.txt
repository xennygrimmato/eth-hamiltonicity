research/engine2-decorrelated.md §7.5-7.6 (3x2 grid searches). Run from this directory.
match.py   : the 10395 perfect matchings of the 12 legs (lambda = 1, SL2 picture, eps pairings), costs (row, col).
m2.py      : span of matchings of min-cost <= k contains H?   (writes V.npy, hv.npy)
m3.py      : H is not in span(cost-0 matchings + one cost-2 matching)
m4.py      : exact 132-coordinate system (writes A.npy, h.npy, C.npy)
m5.py TH MODE TL : MILP (HiGHS) min weighted support; MODE=min: weight 2^min(r,c); MODE=theta: 2^(TH r+(1-TH)c)
m6.py      : verify and group the best MILP solution
cert.py / cert3.py : min-cut model of "node-local maps + one flattening" (all 3^12 capacity patterns);
             cert3 prints the patterns for which both a row- and a column-term need cost >= 3 lambda.
Outputs recorded in ../engine2d_grid32.out.
