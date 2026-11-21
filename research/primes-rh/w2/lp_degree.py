import numpy as np,sys
from lp_weights import run
for cuts in [(1/6,1/4,1/3),(1/8,1/6,1/5,1/4,1/3,0.4)]:
    for x in [10**4,10**5,10**6,3*10**6]:
        Dstar=None; vals=[]
        for D in range(2,11):
            try:
                pi,nv,nm,best,st=run(x,D,cuts)
            except Exception as e:
                vals.append(f"D={D}:err"); break
            vals.append(f"{D}:{best/pi:+.2f}({nm})")
            if best/pi>0 and st==0: Dstar=D; break
            if nm>4000: break
        print(f"cuts={len(cuts)+1} ranges x={x}: D*={Dstar}  "+" ".join(vals),flush=True)
