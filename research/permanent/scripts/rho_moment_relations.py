"""Moments sum_s s^k A_s of the Appendix-B pieces: k=1 vanishes (zero mode of V_1 is alpha_0 = 0), k=2 is g(x,v)[y=u] (zero mode of V_2 is a multiple of L_0 = h Id on V_h), k=3 is not of that form. Confirms sum_s s^k Q_s(a,b) = o(a_{(2h-1-k)} b)."""
import sys, math
sys.path.insert(0, '.')
from rho_fock_lib import partitions, piece_tensor
for h in [3,4,5,6]:
    N = len(partitions(h))
    pieces = {s: piece_tensor(h, s)[2] for s in range(-2*h, 2*h+1)}
    for k in [1,2,3]:
        tot = {}
        for s,T in pieces.items():
            for key,v in T.items():
                tot[key] = tot.get(key,0) + s**k * v
        tot = {kk:v for kk,v in tot.items() if v}
        if k == 1:
            print(f"h={h}: sum_s s*A_s == 0 : {len(tot)==0}")
        else:
            # is it of the form g(x,v) [y=u]?  and is g prop to [x=v]?
            offdiag = any(y != u for (x,y,u,v) in tot)
            diag_dep = set()
            for (x,y,u,v),val in tot.items():
                diag_dep.add((x,v,val))
            # check y-independence of the (x,v) coefficient
            byxv = {}
            for (x,y,u,v),val in tot.items():
                byxv.setdefault((x,v), set()).add(val)
            const = all(len(s_)==1 for s_ in byxv.values())
            xv = sorted(byxv)
            print(f"h={h}: sum_s s^{k} A_s : nonzero={len(tot)>0}, only y=u entries: {not offdiag}, coefficient g(x,v) independent of y: {const}, #(x,v) with g!=0: {len(byxv)} (N^2={N*N}, N={N})")
