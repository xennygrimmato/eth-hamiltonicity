import numpy as np, json
from kernel_opt import run
out={}
for h,tl,tr,dt in [(4,-14,5,0.25),(4,-24,6,0.25),(4,-16,5,0.125),(2,-24,6,0.25),(2,-16,5,0.125),(1e9,-40,6,0.25),(1e9,-80,6,0.5)]:
    knots,g,R=run(h,tl,tr,dt,quiet=True)
    print(h,tl,tr,dt,'R=',R, 'alpha=',((h-1)/R)**2 if h<1e8 else 1/R**2, 'carm3=4/R^2=',4/R**2 if h==4 else '')
    g=g/g.max(); g=np.round(g,6); g[0]=0; g[-1]=0
    out[f"{int(h)}_{tl}_{tr}_{dt}"]={'knots':knots.tolist(),'g':g.tolist(),'R_float':R}
json.dump(out,open('kernels.json','w'))
