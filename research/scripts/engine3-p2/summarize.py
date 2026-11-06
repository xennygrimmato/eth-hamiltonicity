"""Aggregate stage1.out / milp.out / stage2*.out into tables (best over SA seeds)."""
import json, sys, os, math, collections
D = os.path.dirname(os.path.abspath(__file__))
def load(fn):
    out = []
    if os.path.exists(os.path.join(D, fn)):
        for line in open(os.path.join(D, fn)):
            line = line.strip()
            if line.startswith('{'): out.append(json.loads(line))
    return out
s1 = load('stage1.out'); milp = load('milp.out')
best = collections.defaultdict(lambda: (99, 99, None))
for d in s1:
    key = (d['fam'], d['n'], d['Q'], d['rho'], d.get('fixed', False))
    if (d['Rmax'], d['Rsum']) < best[key][:2]: best[key] = (d['Rmax'], d['Rsum'], d['seed'])
mi = {(d['fam'], d['n'], d['Q'], d['rho']): d for d in milp}
def oai(Q, n, r=4):
    lam = math.ceil(math.log2(n)); return math.sqrt(8 * Q * math.log(6 * r * r * lam))
print("fam n  Q | R(rho=0) R(1) R(2) | R_fixedLambda(1) (2) | MILP singleton [best,dual] rho=0/1/2 | Q/sqrt(ln n)  OAI  0.75Q")
for fam in ['L3', 'G3', 'G4']:
    for n in [16, 20, 24]:
        for Q in [4, 5, 6, 8, 10]:
            row = [best[(fam, n, Q, rho, False)][0] for rho in (0, 1, 2)]
            fx = [best[(fam, n, Q, rho, True)][0] for rho in (1, 2)]
            ms = []
            for rho in (0, 1, 2):
                m = mi.get((fam, n, Q, rho))
                ms.append('-' if m is None else f"[{m['R_best']},{None if m['dual_bound'] is None else math.ceil(m['dual_bound']-1e-6)}]")
            print(f"{fam} {n} {Q:2d} | {row[0]:2d} {row[1]:2d} {row[2]:2d} | {fx[0]:2d} {fx[1]:2d} | {' '.join(ms):28s} | "
                  f"{Q/math.sqrt(math.log(n)):.2f} {oai(Q, n):.1f} {0.75*Q:.1f}")
if '--json' in sys.argv:
    json.dump({str(k): v for k, v in best.items()}, open(os.path.join(D, 'stage1_best.json'), 'w'))
