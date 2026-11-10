import numpy as np
exec(open('mix_kernel.py').read().split("if __name__ == '__main__':")[0])
KC = tab(rC[np.abs(ll)], w); KMT = tab(rMT[np.abs(ll)], w)
for X in [15.5, 31.5]:
    m = np.abs(xs) <= X; print(f"|x|<={X}: min K_C={KC[m].min():.2e} at {xs[m][KC[m].argmin()]:.2f}; min K_MT={KMT[m].min():.2e}")
for eps in [0.3, 0.5, 0.6, 0.7, 0.8]:
    r, rr, Kt, K1t, K10 = setup(eps); out = []; mx = 0
    for y in [1e-5, 1e-4, 3e-4, 1e-3, 3e-3, 0.01, 0.03]:
        Gt, se = G_self(rr, Kt, K1t, K10, y); R, dm = R4(Gt, Kt, se, XMAX=15.5); out.append(f"{y:.0e}:{R:.3f}"); mx = max(mx, R)
    print(f"eps={eps} (XMAX=15.5): " + " ".join(out) + f"   max={mx:.3f}", flush=True)
