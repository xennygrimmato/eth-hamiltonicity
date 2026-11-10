"""Float (numpy) evaluation of the same closed forms, for exploration only (not part of any proof)."""
import numpy as np
from kern import PQ
P = {k: complex(PQ[0][k].real.mid().str(20,radius=False)) + 1j*float(PQ[0][k].imag.mid().str(20,radius=False)) for k in range(-2,3)}
Q = {k: complex(PQ[1][k].real.mid().str(20,radius=False)) + 1j*float(PQ[1][k].imag.mid().str(20,radius=False)) for k in range(-2,3)}
MU = {k: 4*np.pi*k/3 for k in range(-2,3)}
GL_x, GL_w = np.polynomial.legendre.leggauss(80)
def quad_nodes(a, b, n=4):
    xs=[];ws=[]
    edges=np.linspace(a,b,n+1)
    for i in range(n):
        xs.append((GL_x+1)/2*(edges[i+1]-edges[i])+edges[i]); ws.append(GL_w/2*(edges[i+1]-edges[i]))
    return np.concatenate(xs), np.concatenate(ws)
def r(al):
    al=np.asarray(al,dtype=float)
    s=0
    for k in range(-2,3): s=s+(P[k]+Q[k]*al)*np.exp(1j*MU[k]*al)
    return s.real
A15, W15 = quad_nodes(0,1.5,6); A1, W1 = quad_nodes(0,1,4)
R15 = r(A15); R1 = r(A1)
def K(x):
    x=np.atleast_1d(x)
    return 2*(np.cos(2*np.pi*np.outer(x,A15))*R15*W15).sum(1)
def beta(x,y):
    x=np.atleast_1d(x)
    return 2*(np.cos(2*np.pi*np.outer(x,A1))*(R1*(np.cosh(2*np.pi*A1*y)-1))*W1).sum(1)
def Gf(x,y): return K(x)+beta(x,y)
def Delta(y): return 2*((R1*(np.cosh(4*np.pi*A1*y)-1))*W1).sum()
