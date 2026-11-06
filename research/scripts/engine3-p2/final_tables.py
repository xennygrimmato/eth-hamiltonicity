"""Final tables for engine3-p2.md: best R over all searches per (fam, n, Q, rho, r), with source."""
import json, os, math, collections
D = os.path.dirname(os.path.abspath(__file__))
def load(fn):
    p = os.path.join(D, fn)
    if not os.path.exists(p): return []
    import re   # parallel writers can glue two JSON lines together
    return [json.loads(m) for m in re.findall(r'\{[^{}]*(?:\[[^\[\]]*\][^{}]*)*\}', open(p).read())]
s1 = load('stage1.out') + load('stage1_rscale.out')
s2 = load('stage2.out'); one = load('milp_one.out')
best = collections.defaultdict(lambda: [99, 99])
avg = {}
for d in s1:
    key = (d['fam'], d['n'], d['Q'], d['rho'], d['r'], d.get('fixed', False))
    if [d['Rmax'], d['Rsum']] < best[key]: best[key] = [d['Rmax'], d['Rsum']]
s2imp = 0
for d in s2:
    f = d['file'][3:-4].split('_')
    fam, n, Q, rho, r = f[0], int(f[1][1:]), int(f[2][1:]), int(f[3][3:]), int(f[4][1:])
    key = (fam, n, Q, rho, r, False)
    if d['best'] < best[key]: best[key] = d['best']; s2imp += 1
Fs = {}
for d in one:
    if d['rho'] == 0 and d['status'] == 0: Fs[(d['fam'], d['n'])] = d['Fstar']
M = {('L3', 16): 48, ('L3', 20): 60, ('L3', 24): 72, ('G3', 16): 48, ('G3', 20): 60, ('G3', 24): 72,
     ('G4', 16): 64, ('G4', 20): 80, ('G4', 24): 96}
print("stage-2 strict improvements over stage 1:", s2imp)
def oai(Q, n, r):
    return math.sqrt(8 * Q * math.log(6 * r * r * math.ceil(math.log2(n))))
for rmode in ['r4', 'rscale']:
    print(f"\n== {rmode}: R_max (mean R_o) ==")
    print("fam  n  r  Q | rho=0  rho=1  rho=2   (R_max  .mean(R_o)/Q) | fixed-Lambda rho=1,2 | LB(rho=0) | Q/sqrt(ln n)  OAI   0.75Q")
    for fam in ['L3', 'G3', 'G4']:
        for n in [16, 20, 24]:
            r = 4 if rmode == 'r4' else n // 4
            if rmode == 'rscale' and n == 16: continue
            for Q in [4, 5, 6, 8, 10]:
                cells = []
                for rho in (0, 1, 2):
                    b = best.get((fam, n, Q, rho, r, False))
                    cells.append('  -   ' if not b or b[0] == 99 else f"{b[0]:2d} .{round(1000*b[1]/M[(fam,n)]/Q):03d}")
                fx = [best.get((fam, n, Q, rho, r, True), [99])[0] for rho in (1, 2)]
                fxs = ' '.join('-' if x == 99 else str(x) for x in fx)
                lb = '-'
                if (fam, n) in Fs: lb = str(math.ceil(Q * Fs[(fam, n)] / M[(fam, n)] - 1e-9))
                print(f"{fam} {n:2d} {r:2d} {Q:2d} | {' '.join(cells)}                 | {fxs:20s} | {lb:9s} | {Q/math.sqrt(math.log(n)):5.2f} {oai(Q,n,r):6.1f} {0.75*Q:5.1f}")
json.dump({str(k): v for k, v in best.items()}, open(os.path.join(D, 'final_best.json'), 'w'))
