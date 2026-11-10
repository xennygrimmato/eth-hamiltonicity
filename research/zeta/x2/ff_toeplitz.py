"""Idea 5: the finite shadow of Weil positivity for curves over F_p.
For y^2=f(x) (deg f = 2g+1 or 2g+2, squarefree) over F_p, count points over F_{p^k}, k<=2g, form
c_k = sum_i z_i^k = (p^k + 1 - #C(F_{p^k}))/p^{k/2}  (z_i = alpha_i/sqrt p), Toeplitz T=(c_{i-j})_{0<=i,j<=2g}.
Claim [R]: T = sum_i v(z_i) v(1/conj z_i)^*, so n_-(T) = #off-circle pairs, n_+(T)-n_-(T) = #distinct on-circle zeros,
rank T = #distinct zeros (when 2g+1 >= #distinct).  RH <=> T PSD."""
import numpy as np, itertools, sys
def irreducible(p,k):
    # find monic irreducible poly of degree k over F_p (coeffs low->high), brute force
    for tail in itertools.product(range(p),repeat=k):
        f=list(tail)+[1]
        if f[0]==0 and k>1: continue
        # check no roots in subfields via Rabin-lite: x^{p^k}=x mod f and gcd conditions skipped for small k: test no factor of deg<=k/2 by brute force
        ok=True
        for d in range(1,k//2+1):
            for g in itertools.product(range(p),repeat=d):
                gg=list(g)+[1]
                if polymod(f,gg,p)==[0]*d: ok=False;break
            if not ok:break
        if ok: return f
def polymod(a,m,p):
    a=a[:]; dm=len(m)-1
    for i in range(len(a)-1,dm-1,-1):
        c=a[i]%p
        if c:
            for j in range(dm+1): a[i-dm+j]=(a[i-dm+j]-c*m[j])%p
    r=[x%p for x in a[:dm]]; return r+[0]*(dm-len(r))
class Fq:
    def __init__(s,p,k):
        s.p=p;s.k=k;s.q=p**k;s.m=irreducible(p,k) if k>1 else [0,1]
    def mul(s,a,b):
        if s.k==1: return [(a[0]*b[0])%s.p]
        c=[0]*(2*s.k-1)
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b): c[i+j]+=x*y
        return polymod(c,s.m,s.p)
    def add(s,a,b): return [(x+y)%s.p for x,y in zip(a,b)]
    def pw(s,a,e):
        r=[1]+[0]*(s.k-1); b=a
        while e:
            if e&1: r=s.mul(r,b)
            b=s.mul(b,b); e>>=1
        return r
    def elems(s):
        for t in itertools.product(range(s.p),repeat=s.k): yield list(t)
def count(fcoef,p,k):
    F=Fq(p,k); q=F.q; tot=0; one=[1]+[0]*(k-1); zero=[0]*k
    for x in F.elems():
        v=zero; xp=one
        for c in fcoef:
            v=F.add(v,[(c*t)%p for t in xp]); xp=F.mul(xp,x)
        if v==zero: tot+=1
        else: tot+= 2 if F.pw(v,(q-1)//2)==one else 0
    deg=len(fcoef)-1
    inf = 1 if deg%2==1 else (2 if pow(fcoef[-1],(q-1)//2,p)==1 else 0)  # leading coeff in F_p: square in F_q?
    return tot+inf
def analyse(fcoef,p):
    deg=len(fcoef)-1; g=(deg-1)//2
    N=[count(fcoef,p,k) for k in range(1,2*g+1)]
    c=[2*g]+[(p**k+1-N[k-1])/p**(k/2) for k in range(1,2*g+1)]
    T=np.array([[c[abs(i-j)] if True else 0 for j in range(2*g+1)] for i in range(2*g+1)],float)
    ev=np.linalg.eigvalsh(T); tol=1e-8*max(1,abs(ev).max())
    npos=(ev>tol).sum(); nneg=(ev<-tol).sum()
    # zeros from L-polynomial via Newton identities: P(T)=prod(1-alpha_i T)
    s=[p**(k/2)*c[k] for k in range(1,2*g+1)]  # power sums of alpha
    e=[1.0]
    for n in range(1,2*g+1): e.append(sum((-1)**(i-1)*e[n-i]*s[i-1] for i in range(1,n+1))/n)
    coeffs=[(-1)**n*e[n] for n in range(2*g+1)]   # P(T)=sum coeffs T^n
    alphas=1/np.roots(coeffs[::-1])
    return g,N,np.round(ev,6),npos,nneg,alphas/np.sqrt(p)
if __name__=='__main__':
    for p,f in [(5,[0,-1,0,0,0,1]),(7,[1,2,0,3,0,1]),(5,[2,1,0,1,3,1]),(3,[1,0,1,0,0,1,0,1]),(7,[0,-1,0,0,0,0,0,1])]:
        g,N,ev,npos,nneg,z=analyse(f,p)
        print('p=%d f=%s g=%d counts=%s'%(p,f,g,N)); print('  eig(T)=',ev,' n+=%d n-=%d'%(npos,nneg))
        print('  |z|=',np.round(abs(z),6),' args/pi=',np.round(np.angle(z)/np.pi,4))
