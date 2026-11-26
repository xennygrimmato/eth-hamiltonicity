from hardregion import run
for lam in (0.88, 0.91, 0.915, 0.92):
    v, x = run(lam, 3-2*lam, starts=300)
    print(f"cut line lam={lam} (w={(3-2*lam)/lam:.4f}): min Br' over closure(F') = {v:+.6f}", flush=True)
