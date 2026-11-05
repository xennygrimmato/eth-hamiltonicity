"""Task B, step 1: cost vectors on C of products/sums of the single-bit pieces P=[x=u][y=v], B=F-P per pair."""
import sys, itertools, numpy as np
from lib import *; from cpieces import *
c = config_C(2); F, Pp, B = single_bit_pieces()
fC = assemble(c, [F, F, F]); assert (fC == graph_tensor(c)).all()
print("f_C cost vector (merge0,1,2):", cost_vector(c, fC))
# Q split: forward strings X_{i,i+1}, Y_{i,i+1}
Qf = [l for l, (e, nd) in enumerate(c['legs']) if ((c['edges'][e][1] if c['edges'][e][0] == nd else c['edges'][e][0])[1] - nd[1]) % 3 == 1]
print("rank across Q of f_C:", frank(fC, Qf))
for name, pc in (('P', Pp), ('B', B), ('F', F)):
    T = assemble(c, [pc, F, F]); T1 = assemble(c, [pc, pc, pc])
    print(f"piece {name} on all 3 pairs: cost vector", cost_vector(c, T1), " rank_Q", frank(T1, Qf))
tot = 0; rows = []
for ch in itertools.product('PB', repeat=3):
    T = assemble(c, [Pp if s == 'P' else B for s in ch])
    cv = cost_vector(c, T); rows.append((ch, cv, min(cv))); tot += 2 ** min(cv)
    print(''.join(ch), cv, 'min', min(cv), 'rank_Q', frank(T, Qf))
print("8 product terms, S = sum 2^min =", tot)
PPP = assemble(c, [Pp] * 3)
R = fC - PPP
print("two-term decomposition f_C = PPP + (f_C - PPP):")
print("  PPP", cost_vector(c, PPP), "  f_C-PPP", cost_vector(c, R), " ranks:", cut_ranks(c, R, c['merges'][1]))
# all ways to put a subset of the 8 products into one merge-k bucket and sum (bucket sums can cancel rank)
prods = {ch: assemble(c, [Pp if s == 'P' else B for s in ch]) for ch in itertools.product('PB', repeat=3)}
keys = list(prods); best = None
for assign in itertools.product(range(3), repeat=8):
    S = 0; cvs = []
    for k in range(3):
        sel = [keys[i] for i in range(8) if assign[i] == k]
        if not sel: continue
        T = sum(prods[s] for s in sel)
        ck = c_flat(c, T, c['merges'][k]); S += 2 ** ck; cvs.append((k, ''.join(''.join(s) for s in sel), ck))
    if best is None or S < best[0]: best = (S, cvs)
print("best 3-bucket grouping of the 8 products (c_flat):", best)
