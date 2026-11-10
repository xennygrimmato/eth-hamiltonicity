import numpy as np
exec(open('mix_kernel.py').read().split("if __name__ == '__main__':")[0])
KMT = tab(rMT[np.abs(ll)], w); KC = tab(rC[np.abs(ll)], w)
for x0 in [1.048, 1.935, 2.082, 3.02]:
    i = np.argmin(np.abs(xs - x0)); sl = slice(i - 200, i + 200)
    print(f"near x={x0}: min K_MT={KMT[sl].min():.3e}  min K_C={KC[sl].min():.3e}  K_MT at argmin K_C={KMT[sl][KC[sl].argmin()]:.3e}")
for eps in [0.5, 0.6, 0.7]:
    r, rr, Kt, K1t, K10 = setup(eps)
    out = []
    for y in [1e-5, 3e-5, 1e-4, 3e-4, 1e-3, 3e-3]:
        Gt, se = G_self(rr, Kt, K1t, K10, y); R, dm = R4(Gt, Kt, se); out.append(f"y={y:.0e}:{R:.3f}@x={xs[Gt.argmin()]:.2f}")
    print(f"eps={eps}: " + "  ".join(out), flush=True)
