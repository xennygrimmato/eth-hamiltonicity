import numpy as np, sys
exec(open('t1b_onebody2.py').read().split('print(" y     self(y)')[0])
for y in [float(v) for v in sys.argv[2:]]:
    for k in (8, 12, 16, 24):
        f, se, X, m = run(y, k, B=384, steps=700)
        print(f"y={y} k={k}: self {se:.5f} min LHS {f:+.6f} ratio {f/se:+.4f}  x={X} m={m}", flush=True)
