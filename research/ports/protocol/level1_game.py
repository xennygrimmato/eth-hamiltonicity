import numpy as np, itertools, sys
from scipy.optimize import linprog
# nodes 0=u1,1=u2,2,3,4 = v1..v3
vp=[(2,3),(3,4),(2,4)]
def lp(thetas,Pe=(1/3,1/3,1/3),Q=(1,1,1),hubs=range(5),ret=False):
    # variables: lam[e][type][o][o'] , f_uu[3], f_vv[3][2], n
    H=list(hubs); nh=len(H)
    nl=3*2*nh*nh
    nv=nl+3+6+1
    def li(e,t,a,b): return ((e*2+t)*nh+a)*nh+b
    FU=nl; FV=nl+3; NN=nl+9
    # demand accumulation matrices: direct[u,v] (6), duu, dvv[3]
    A_direct=np.zeros((6,nv)); A_uu=np.zeros(nv); A_vv=np.zeros((3,nv))
    def add(col,x,y,delta):
        if x==y or delta==0: return
        x,y=min(x,y),max(x,y)
        if x<2 and y>=2: A_direct[x*3+(y-2),col]+=delta
        elif x<2 and y<2: A_uu[col]+=delta
        else: A_vv[vp.index((x,y)),col]+=delta
    for e,(i,j) in enumerate(vp):
        P=Pe[e]; q=Q[e]; rho=np.hypot(P,q)
        r=min(np.sqrt(2)*rho*np.cos(thetas[e]),P+q); rp=min(np.sqrt(2)*rho*np.sin(thetas[e]),P+q)
        a,c,b,d=0,1,i,j
        for ia,o in enumerate(H):
            for ib,o2 in enumerate(H):
                col=li(e,0,ia,ib)
                add(col,a,o,P);add(col,b,o,q);add(col,c,o2,P);add(col,d,o2,q);add(col,o,o2,r)
                col=li(e,1,ia,ib)
                add(col,a,o,P);add(col,d,o,q);add(col,b,o2,q);add(col,c,o2,P);add(col,o,o2,rp)
    Aub=[];bub=[]
    for k in range(2):
        for l in range(3):
            row=A_direct[k*3+l].copy()
            row[FU+l]+=1
            for pi,(x,y) in enumerate(vp):
                if l+2 in (x,y): row[FV+pi*2+k]+=1
            row[NN]=-1
            Aub.append(row);bub.append(0)
    Aeq=[];beq=[]
    row=A_uu.copy(); row[FU:FU+3]-=1; Aeq.append(row);beq.append(0)
    for pi in range(3):
        row=A_vv[pi].copy(); row[FV+pi*2:FV+pi*2+2]-=1; Aeq.append(row);beq.append(0)
    for e in range(3):
        row=np.zeros(nv); row[e*2*nh*nh:(e+1)*2*nh*nh]=1; Aeq.append(row);beq.append(1)
    cvec=np.zeros(nv); cvec[NN]=1
    res=linprog(cvec,A_ub=np.array(Aub),b_ub=bub,A_eq=np.array(Aeq),b_eq=beq,bounds=[(0,None)]*nv,method='highs')
    if ret: return res
    return res.fun
if __name__=="__main__":
    G=int(sys.argv[1]); ths=np.linspace(0,np.pi/2,G)
    worst=(0,None)
    for t in itertools.product(ths,repeat=3):
        v=lp(t)
        if v>worst[0]: worst=(v,t)
    print("worst n",worst,"rate",1/worst[0], "sym value",(4+np.sqrt(10))/6)
    print("all-middle",lp((np.pi/4,)*3))
