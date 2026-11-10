#!/usr/bin/env python3
"""T1b: does EVERY nonnegative certificate a>=0 valid on on-line configs stay valid with off-line pairs?
For random a>=0 compute m_on = min over on-line configs of s1/N + sum a|S|^2 and m_pair = same over configs
containing >=1 pair (depth in (0,YMAX]). m_pair < m_on  => that certificate breaks unconditionally."""
import sys, numpy as np
N = int(sys.argv[1]); T = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 0)
L = np.arange(1, N); OM = 2*np.pi*L/N
def run(a, pairs, B=600, steps=500, lr=0.05, full=False):
    base = np.zeros((B, N)); isp = np.zeros((B, N), bool); k1 = np.zeros(B)
    for b in range(B):
        if pairs:
            k3 = rng.integers(1, N//2+1); k2 = rng.integers(0, N//2-k3+1)
        else:
            k3 = 0; k2 = rng.integers(0, N//2+1)
        kk1 = N-2*k2-2*k3; k1[b] = kk1
        base[b, :kk1] = 1; base[b, kk1:kk1+k2+k3] = 2; isp[b, kk1+k2:kk1+k2+k3] = True
    t = rng.uniform(0, N, (B, N)); y = rng.uniform(0.0, 0.6, (B, N))*isp
    m = [np.zeros_like(t), np.zeros_like(y)]; v = [np.zeros_like(t), np.zeros_like(y)]
    for s in range(1, steps+1):
        W = np.where(isp[..., None], 2*np.cosh(y[..., None]*OM), base[..., None]); E = np.exp(1j*t[..., None]*OM); S = (W*E).sum(1)
        gS = 2*a*np.conj(S)
        g = [np.real(gS[:, None, :]*W*1j*OM*E).sum(2), np.real(gS[:, None, :]*2*np.sinh(y[..., None]*OM)*OM*E).sum(2)*isp]
        for i, x in enumerate((t, y)):
            m[i] = 0.9*m[i]+0.1*g[i]; v[i] = 0.999*v[i]+0.001*g[i]**2
            x -= lr*(m[i]/(1-0.9**s))/(np.sqrt(v[i]/(1-0.999**s))+1e-12)
        np.clip(y, 0, 1.0, out=y)
    W = np.where(isp[..., None], 2*np.cosh(y[..., None]*OM), base[..., None]); S = (W*np.exp(1j*t[..., None]*OM)).sum(1)
    f = k1/N + (np.abs(S)**2) @ a
    b = f.argmin()
    if full: return f[b], t[b], base[b], isp[b], y[b], k1[b]
    return f[b], (k1[b], (base[b] == 2).sum()-isp[b].sum(), isp[b].sum()), y[b][isp[b]]
worst = 0
for trial in range(T):
    kind = trial % 3
    if kind == 0: a = rng.exponential(1, N-1)/N**2            # generic positive
    elif kind == 1: a = np.sort(rng.exponential(1, N-1))[::-1]/N**2   # decreasing
    else: a = np.zeros(N-1); a[rng.integers(0, N-1, 2)] = rng.exponential(1, 2)/N  # sparse
    mon = run(a, False); mp = run(a, True)
    d = mp[0]-mon[0]
    if d < -1e-6:
        mon2 = min(run(a, False, B=4000, steps=800)[0] for _ in range(3))
        d = mp[0]-min(mon[0], mon2)
        np.save(f"/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/randcert_a_{N}_{trial}.npy", a)
        print(f"   deep on-line recheck: {mon2:.6f}", flush=True)
    worst = min(worst, d)
    print(f"trial {trial} kind {kind}: m_on {mon[0]:.6f} {mon[1]}  m_pair {mp[0]:.6f} {mp[1]} depths {np.round(mp[2],3)}  diff {d:+.2e}", flush=True)
print("most negative m_pair - m_on:", worst)
