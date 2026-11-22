# Sanity check of Lemma S: Psi(x,y) >= binom(pi(y)+u,u), u=floor(log x/log y); is it > sqrt(x) for y=c log^2 x ?
from mpmath import mp, loggamma, log, floor, li
from sympy import primepi
mp.dps=30
def margin(L,c):
    y=c*L*L; u=int(floor(L/log(y)))
    N=int(primepi(int(y))) if y<1e9 else int(y/log(y))   # pi(y)>=y/log y for y>=17
    return float(loggamma(N+u+1)-loggamma(N+1)-loggamma(u+1)-L/2), u, N
for c in [1.0,0.5,0.25,0.2,0.15]:
    print("c=",c,[(L,round(margin(L,c)[0],1)) for L in [20,50,100,300,1000,10**4,10**5,10**6]])
