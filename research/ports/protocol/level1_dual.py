import numpy as np, itertools, sys
from scipy.optimize import minimize
P=5
pairs=[(i,j) for i in range(P) for j in range(i+1,P)]
S=[(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)]; T=[(0,1),(2,3),(3,4),(2,4)]
iu=np.array([[i,j] for i,j in pairs])
def D(d):
    M=np.zeros((P,P)); M[iu[:,0],iu[:,1]]=d; M[iu[:,1],iu[:,0]]=d; return M
NPH=int(sys.argv[3]) if len(sys.argv)>3 else 24
phis=np.linspace(0,np.pi/2,NPH+2)[1:-1]; pp=np.cos(phis)[:,None,None]; qq=np.sin(phis)[:,None,None]
pop=list(itertools.combinations(pairs,2))
off=~np.eye(P,dtype=bool)
def cons(d):
    M=D(d); out=[]
    Md=np.where(off,np.maximum(M,1e-9),1.0)
    for (x,v),(y,u) in pop:
        L=pp*M[x,v]+qq*M[y,u]
        a=(pp*M[x][None,:,None]+qq*M[y][None,:,None])+(pp*M[v][None,None,:]+qq*M[u][None,None,:])
        b=(pp*M[x][None,:,None]+qq*M[u][None,:,None])+(qq*M[y][None,None,:]+pp*M[v][None,None,:])
        rs=np.where(off,(L-a)/Md,0).max(axis=(1,2)).clip(0)
        rps=np.where(off,(L-b)/Md,0).max(axis=(1,2)).clip(0)
        out.append(2-rs**2-rps**2)
    return np.concatenate(out)
tri=[(i,j,k) for i,j,k in itertools.permutations(range(P),3) if i<j]
def tcons(d):
    M=D(d); return np.array([M[i,k]+M[k,j]-M[i,j] for i,j,k in tri])
def Rf(d):
    M=D(d); return sum(M[a] for a in S)/sum(M[a] for a in T)
def norm(d):
    M=D(d); return sum(M[a] for a in T)-1
if __name__=="__main__":
    rng=np.random.default_rng(int(sys.argv[1]))
    r10=np.sqrt(10)
    dsym=np.array([ (1+1/r10) if p==(0,1) else (1.0 if p[0]<2 else 1+3/r10) for p in pairs]); dsym/= (norm(dsym)+1)
    res_all=[]
    for st in range(int(sys.argv[2])):
        if st%2==0: d0=dsym*(1+0.3*rng.standard_normal(10))
        else: d0=rng.uniform(0.05,0.4,10)
        d0=np.abs(d0)
        res=minimize(Rf,d0,method='SLSQP',constraints=[{'type':'ineq','fun':cons},{'type':'ineq','fun':tcons},{'type':'eq','fun':norm}],bounds=[(0,None)]*10,options={'maxiter':400,'ftol':1e-12})
        d=res.x
        print(st,"R %.6f"%Rf(d),"mincons %.2e"%cons(d).min(),"tri %.2e"%tcons(d).min(),np.round(d/d[1],4),flush=True)
