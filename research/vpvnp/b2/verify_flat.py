# Direct check (exact Euclidean distances, finite M) of the flat-case hub bounds.
import numpy as np, itertools
nodes=[(r,c) for r in range(3) for c in range(3)]
tri={v:(v[0]+v[1])%3 for v in nodes}
E=[(u,v) for u in nodes for v in nodes if u<v and tri[u]==tri[v]]
mf=[lambda v:v[0],lambda v:v[1],lambda v:(v[0]-v[1])%3]
a=[np.array([np.cos(2*np.pi*j/3),np.sin(2*np.pi*j/3)])/np.sqrt(3) for j in range(3)]  # side 1
def hub(k,g,p):  # merge k hubs: equilateral triangle side 1 in block k of R^(2p)
    x=np.zeros(2*p); x[2*k:2*k+2]=a[g]; return x
def delta3(p,M):
    L=0; H=[0]*p
    for (u,v) in E:
        s=sum(hub(k,mf[k](u),p)-hub(k,mf[k](v),p) for k in range(p)); ue=s/np.linalg.norm(s)
        lu,lv=M*ue,-M*ue
        L+=np.linalg.norm(lu-lv)
        for k in range(p):
            H[k]+=np.linalg.norm(lu-hub(k,mf[k](u),p))+np.linalg.norm(lv-hub(k,mf[k](v),p))
    return [(L-H[k])/1.0 for k in range(p)]
for p in (1,2,3):
    for M in (1e2,1e4,1e6): print('Delta3 p=%d M=%g'%(p,M),np.round(delta3(p,M),5), 'target 9/sqrt(p)=%.5f'%(9/np.sqrt(p)))
# rectangle crossing: wires x-v (l1 bits), y-u (l2 bits); rows {x,y}|{u,v}, cols {x,u}|{y,v}
def rect(l1,l2,theta,M):
    A=np.array([1.0,0]); B=np.array([np.cos(theta),np.sin(theta)])
    oT,oB,oL,oR=A/2,-A/2,B/2,-B/2
    u1=(A+B)/np.linalg.norm(A+B); u2=(A-B)/np.linalg.norm(A-B)
    x,v=M*u1,-M*u1; y,u=M*u2,-M*u2
    d=np.linalg.norm
    L=l1*d(x-v)+l2*d(y-u)
    HR=l1*(d(x-oT)+d(v-oB))+l2*(d(y-oT)+d(u-oB))
    HC=l1*(d(x-oL)+d(v-oR))+l2*(d(y-oR)+d(u-oL))
    return (L-HR)/d(oT-oB),(L-HC)/d(oL-oR)
for l1,l2 in ((1,1),(1,0.5),(1,0.1)):
    best=max((sum(rect(l1,l2,t,1e6)),t) for t in np.linspace(0.01,np.pi-0.01,2000))
    print('rect',l1,l2,'max c_R+c_C bound',round(best[0],5),'2||l||_2=',round(2*np.hypot(l1,l2),5))
