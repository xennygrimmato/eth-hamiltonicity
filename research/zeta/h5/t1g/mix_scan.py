#!/usr/bin/env python3
"""Scan sup_y R4_mix(y) on a fine y-grid for several eps (mixture weight of CGdL). Uses mix_kernel.py definitions."""
import numpy as np, sys
exec(open('mix_kernel.py').read().split("if __name__ == '__main__':")[0])
ys = np.r_[np.geomspace(3e-4, 0.03, 12), np.arange(0.04, 0.5, 0.04), np.arange(0.5, 1.3, 0.025), np.arange(1.3, 3.01, 0.1)]
for eps in [float(e) for e in sys.argv[1:]]:
    r, rr, Kt, K1t, K10 = setup(eps); worst = (0, None); small = 0
    for y in ys:
        Gt, se = G_self(rr, Kt, K1t, K10, y); R, dm = R4(Gt, Kt, se)
        if R > worst[0]: worst = (R, y)
        if y <= 0.03: small = max(small, R)
    print(f"eps={eps:.2f} tau={(1-eps)/eps:.3f} value(N=64)={value(r):.6f} continuum~{0.6725+eps*(0.6792-0.6725):.5f}:  sup R4 = {worst[0]:.4f} at y={worst[1]:.4f};  sup over y<=0.03: {small:.4f}", flush=True)
