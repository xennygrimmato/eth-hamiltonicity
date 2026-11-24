import sys
from crossing_d import *
d,e=int(sys.argv[1]),int(sys.argv[2]); S=symbols(d,1,e); Th=4*e
co={}
for k in itertools.product(S,repeat=4):
    co[k]=interpolate([det_int(matrix(d,X,*k)) for X in range(Th+1)])
ok=sum(co[(a,b,c,dd)][N]==co[(a,dd,c,b)][Th-N] for (a,b,c,dd) in co for N in range(Th+1)); tot=len(co)*(Th+1)
ok2=sum(co[(a,b,c,dd)][N]==-co[(a,dd,c,b)][Th-N] for (a,b,c,dd) in co for N in range(Th+1))
print(d,e,"reflection X^Th Psi(1/X;a,b,c,d)=Psi(X;a,d,c,b): matches",ok,"of",tot," (sign-flipped matches",ok2,")")
ok3=sum(abs(co[(a,b,c,dd)][N])==abs(co[(a,dd,c,b)][Th-N]) for (a,b,c,dd) in co for N in range(Th+1))
print("abs matches",ok3)
bad=[(k,N) for k in co for N in range(Th+1) if abs(co[k][N])!=abs(co[(k[0],k[3],k[2],k[1])][Th-N])]
print(bad[:3]); k,N=bad[0]; print(co[k], co[(k[0],k[3],k[2],k[1])])
