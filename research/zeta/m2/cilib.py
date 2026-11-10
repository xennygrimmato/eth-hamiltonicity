#!/usr/bin/env python3
"""m2: core library for the configuration inequality CI:
   D(X) = int_{-1}^{1} r(a)|S_X(a)|^2 da - (2N - s1) >= 0 ?
S_X(a) = sum_online m e^{2 pi i a t} + sum_pairs 2 m_p cosh(2 pi a y) e^{2 pi i a t}.
Kernels: h3's explicit 5-term (K5), MT, mixtures.  Normalisation int_R r = K(0) = 1."""
import numpy as np
from scipy.optimize import brentq

GX, GW = np.polynomial.legendre.leggauss(120)

def k5_coef():
    base = [2/3, 0.53044, -0.136227748726, 0.347412, -0.178443]
    def r1(a2):
        co = np.array([base[0], base[1], a2, base[3], base[4]]); return r_k5(co, np.array([1.0]))[0]
    a2 = brentq(r1, -0.14, -0.13, xtol=1e-15)
    return np.array([base[0], base[1], a2, base[3], base[4]])

def f_k5(co, u, c=1.5):
    return co[0]+co[1]*np.cos(2*np.pi*u/c)+co[2]*np.cos(4*np.pi*u/c)+co[3]*np.sin(2*np.pi*u/c)+co[4]*np.sin(4*np.pi*u/c)

def r_k5(co, a, c=1.5):
    """unnormalised autocorrelation r(a)=int f(u)f(u+a)du on support [-c/2,c/2]"""
    a = np.abs(np.atleast_1d(a)).astype(float); lo = -c/2; hi = c/2-a
    U = (hi-lo)[:, None]/2*GX[None, :]+(hi+lo)[:, None]/2
    return np.where(hi > lo, (hi-lo)/2*(GW[None, :]*f_k5(co, U)*f_k5(co, U+a[:, None])).sum(1), 0.0)

def r_K5(a):
    co = _CO
    return r_k5(co, a)/(co[0]*1.5)**2

def r_MT(a):
    """psi=cos(sqrt2 s) on [-1/2,1/2]; r = psi*psi/(int psi)^2"""
    a = np.abs(np.atleast_1d(a)).astype(float); lo = -0.5; hi = 0.5-a
    U = (hi-lo)[:, None]/2*GX[None, :]+(hi+lo)[:, None]/2
    ps = lambda s: np.cos(np.sqrt(2)*s)
    I = 2*np.sin(np.sqrt(2)/2)/np.sqrt(2)
    return np.where(hi > lo, (hi-lo)/2*(GW[None, :]*ps(U)*ps(U+a[:, None])).sum(1), 0.0)/I**2

_CO = k5_coef()

class Kernel:
    """r on [0,1] sampled at nq Gauss nodes; quadratic form = 2 sum_k W_k |S(a_k)|^2"""
    def __init__(self, rfun, nq=200, name=""):
        x, w = np.polynomial.legendre.leggauss(nq)
        self.a = 0.5*x+0.5; self.w = 0.5*w
        self.r = rfun(self.a); self.W = 2*self.w*self.r; self.name = name
        self.K10 = np.sum(self.W)  # K1(0) = int_{-1}^1 r
        self.value = 2 - (rfun(np.array([0.0]))[0] + 2*np.sum(self.w*self.a*self.r))
    def K1(self, z):
        """K1(z) = int_{-1}^1 r(a) e^{2 pi i a z} da (even)"""
        z = np.atleast_1d(z)
        return (self.W[None, :]*np.cos(2*np.pi*np.outer(z, self.a))).sum(1)

def mixture(eps, nq=200):
    return Kernel(lambda a: (1-eps)*r_MT(a)+eps*r_K5(a), nq, f"mix{eps}")

def S_of(ker, t_on, m_on, t_p, y_p, m_p):
    a = ker.a
    S = (m_on[None, :]*np.exp(2j*np.pi*np.outer(a, t_on))).sum(1)
    S = S + (2*m_p[None, :]*np.cosh(2*np.pi*np.outer(a, y_p))*np.exp(2j*np.pi*np.outer(a, t_p))).sum(1)
    return S

def target(m_on, m_p):
    return 2*np.sum(m_on) - np.sum(m_on == 1) + 4*np.sum(m_p)

def defect(ker, t_on, m_on, t_p, y_p, m_p):
    S = S_of(ker, t_on, m_on, t_p, y_p, m_p)
    return np.sum(ker.W*np.abs(S)**2) - target(m_on, m_p)

def defect_grad(ker, t_on, m_on, t_p, y_p, m_p):
    """value and gradient wrt (t_on, t_p, y_p)"""
    a = ker.a
    E_on = np.exp(2j*np.pi*np.outer(a, t_on)); E_p = np.exp(2j*np.pi*np.outer(a, t_p))
    Ch = np.cosh(2*np.pi*np.outer(a, y_p)); Sh = np.sinh(2*np.pi*np.outer(a, y_p))
    S = (m_on[None, :]*E_on).sum(1) + (2*m_p[None, :]*Ch*E_p).sum(1)
    val = np.sum(ker.W*np.abs(S)**2) - target(m_on, m_p)
    Sc = np.conj(S)
    tw = 2*np.pi*a
    g_ton = 2*np.real(((ker.W*Sc)[:, None]*(m_on[None, :]*1j*tw[:, None]*E_on)).sum(0))
    g_tp = 2*np.real(((ker.W*Sc)[:, None]*(2*m_p[None, :]*Ch*1j*tw[:, None]*E_p)).sum(0))
    g_yp = 2*np.real(((ker.W*Sc)[:, None]*(2*m_p[None, :]*Sh*tw[:, None]*E_p)).sum(0))
    return val, g_ton, g_tp, g_yp

if __name__ == "__main__":
    k = Kernel(r_K5, name="K5"); print("K5 value", k.value, "K1(0)", k.K10, "r(1)", r_K5(np.array([1.0])))
    print("int_R r =", 2*np.sum(Kernel(r_K5, 400).w*0) + 0)  # placeholder
    a = np.linspace(0, 1.5, 30001); print("int_R r (trap)", 2*np.trapezoid(r_K5(a), a))
    m = Kernel(r_MT, name="MT"); print("MT value", m.value, "K1(0)", m.K10)
    for e in (0.3, 0.5, 0.7): print("mix", e, mixture(e).value)
