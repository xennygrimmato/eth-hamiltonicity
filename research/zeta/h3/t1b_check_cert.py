#!/usr/bin/env python3
"""Adversarial check of a data-form certificate  s1/N >= c0 - sum_l a_l |Shat(l)|^2  on N-periodic configurations
WITH off-line pairs (weights 2cosh(2 pi l y/N)), batched Adam multistart.
Usage: t1b_check_cert.py file.npz [ymin] [ymax] [batch] [rounds]  -> min reduced cost  s1/N - c0 + sum a|S|^2 (>=0 means valid)"""
import sys, numpy as np
d = np.load(sys.argv[1]); c0 = float(d['c0']); a = d['a']; N = len(a)+1
YMIN = float(sys.argv[2]) if len(sys.argv) > 2 else 0.0; YMAX = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
B = int(sys.argv[4]) if len(sys.argv) > 4 else 400; RND = int(sys.argv[5]) if len(sys.argv) > 5 else 4
L = np.arange(1, N); OM = 2*np.pi*L/N; rng = np.random.default_rng(11)
def batch(pairs_required):
    base = np.zeros((B, N)); isp = np.zeros((B, N), bool); k1 = np.zeros(B)
    for b in range(B):
        k3 = rng.integers(1 if pairs_required else 0, N//2+1); k2 = rng.integers(0, N//2-k3+1)
        kk1 = N-2*k2-2*k3; k1[b] = kk1
        base[b, :kk1] = 1; base[b, kk1:kk1+k2+k3] = 2; isp[b, kk1+k2:kk1+k2+k3] = True
    # structured starts: near-lattice positions
    t = np.sort(rng.uniform(0, N, (B, N)), 1)
    lat = (np.cumsum(base, 1)-base/2)*(N/base.sum(1, keepdims=True))
    mix = rng.uniform(0, 1, (B, 1)); t = mix*t+(1-mix)*lat+rng.normal(0, 0.1, (B, N))
    y = (YMIN+rng.uniform(0, 1, (B, N))*(min(YMAX, YMIN+0.5)-YMIN))*isp
    return t, base, isp, y, k1
def opt(pr, steps=600, lr=0.03):
    t, base, isp, y, k1 = batch(pr)
    m = [np.zeros_like(t), np.zeros_like(y)]; v = [np.zeros_like(t), np.zeros_like(y)]
    for s in range(1, steps+1):
        W = np.where(isp[..., None], 2*np.cosh(y[..., None]*OM), base[..., None]); E = np.exp(1j*t[..., None]*OM); S = (W*E).sum(1)
        gS = 2*a*np.conj(S)
        g = [np.real(gS[:, None, :]*W*1j*OM*E).sum(2), np.real(gS[:, None, :]*2*np.sinh(y[..., None]*OM)*OM*E).sum(2)*isp]
        for i, x in enumerate((t, y)):
            m[i] = 0.9*m[i]+0.1*g[i]; v[i] = 0.999*v[i]+0.001*g[i]**2
            x -= lr*(m[i]/(1-0.9**s))/(np.sqrt(v[i]/(1-0.999**s))+1e-12)
        y[:] = np.where(isp, np.clip(y, YMIN, YMAX), 0)
    W = np.where(isp[..., None], 2*np.cosh(y[..., None]*OM), base[..., None]); S = (W*np.exp(1j*t[..., None]*OM)).sum(1)
    f = k1/N-c0+(np.abs(S)**2)@a; b = f.argmin()
    return f[b], (int(k1[b]), int((base[b] == 2).sum()-isp[b].sum()), int(isp[b].sum())), np.round(np.sort(y[b][isp[b]]), 3)
print(f"N={N} c0={c0:.6f} certificate value c0 - sum a_l*l = {c0-a@L:.6f}; ymin={YMIN} ymax={YMAX}")
on = min((opt(False) for _ in range(RND)), key=lambda z: z[0]) if YMIN == 0 else None
pa = min((opt(True) for _ in range(RND)), key=lambda z: z[0])
if on: print("  on-line+any  : min RC %+.3e at comp %s depths %s" % on)
print("  with pairs   : min RC %+.3e at comp %s depths %s" % pa)
