# multi-block version of e5: shifts delta in a list (both signs), common thM, th2, common weight c.
import numpy as np, sys
exec(open("e5_cue_shift.py").read().split('print("N"')[0].replace("N=int(sys.argv[1]); S=int(sys.argv[2])","N=40; S=60"))
def run(th1,shifts,thM,th2):
    best=(0,)
    z,coef,h=data[0]
    for c in [0.05,0.1,0.2,0.4,0.8]:
        bl=[]
        for dl in shifts:
            sc=1/np.mean(np.abs(fvec(z,coef,h,2*np.pi*dl/N,int(round(thM*N))))**2)
            bl+= [(dl,thM,th2,c*sc),(-dl,thM,th2,c*sc)]
        best=max(best,(rho(th1,bl),c))
    return best
for thM,th2 in [(0.5,0.5),(1.0,0.5),(1.0,1.0),(2.0,1.0)]:
    for shifts in [[0.5],[0.5,1.0],[0.5,1.0,1.5],[0.33,0.67,1.0,1.33,1.67]]:
        r,c=run(1.0,shifts,thM,th2)
        print(f"th1=1 thM={thM} th2={th2} shifts={shifts}: rho={r:.4f} (c={c})")
