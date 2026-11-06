"""als_runs.py -- validation + searches.  Usage: python3 als_runs.py <mode> [restarts] [sweeps] [seed]
modes: rect | planted8 | tworect | cyc2 | cyc_<adj>_<d1>_<d2> | prism_<a>_<b>_<c>[_3] """
import sys, itertools, numpy as np, time
sys.path.insert(0, __import__('os').path.dirname(__file__))
from netals import Instance, als
mode = sys.argv[1]; restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 20
sweeps = int(sys.argv[3]) if len(sys.argv) > 3 else 100; seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
rng = np.random.default_rng(seed)
d8 = lambda i, j: min((j - i) % 8, (i - j) % 8)
G8 = [[1, 2], [3, 4], [5, 6], [7, 8]]; H8 = [[2, 3], [4, 5], [6, 7], [8, 1]]
E8two = [(i, j) for i, j in itertools.combinations(range(1, 9), 2) if d8(i, j) >= 3]
def K4(adj, a, b): return {(0, 1): adj, (1, 2): adj, (2, 3): adj, (0, 3): adj, (0, 2): a, (1, 3): b}
pos = {'A': (1, 1), 'B': (1, 2), 'C': (2, 2), 'D': (2, 3), 'E': (3, 3), 'F': (3, 1)}
EP = [(u, v) for u, v in itertools.combinations('ABCDEF', 2) if pos[u][0] != pos[v][0] and pos[u][1] != pos[v][1]]
GP = [['A', 'B'], ['C', 'D'], ['E', 'F']]; HP = [['A', 'F'], ['B', 'C'], ['D', 'E']]

if mode == 'rect':        # App. H: [x=v][y=u] = R + C with R product over {x,y}|{u,v}, C product over {x,u}|{y,v}
    inst = Instance('xyuv', [('x', 'v'), ('y', 'u')], None)
    specs = [([['x', 'y'], ['u', 'v']], {}), ([['x', 'u'], ['y', 'v']], {})]
elif mode == 'planted8':  # random G-net + random H-net (bonds 2) on the 8-cycle two-cell leg structure: must be found
    inst = Instance(range(1, 9), E8two, None)
    from netals import Net
    r0 = Net(inst, G8, K4(2, 2, 2), rng).full(); c0 = Net(inst, H8, K4(2, 2, 2), rng).full()
    inst.f = r0 + c0
    specs = [(G8, K4(2, 2, 2)), (H8, K4(2, 2, 2))]
elif mode == 'tworect':   # two disjoint rectangles, 4 groups per merge: f = R1 (x) f2 + C1 (x) f2  exactly,
    # R: G-network with bond 4 on (G3,G4) only, C: H-network with bond 4 on (H3,H4) only (crossings in different cells)
    nodes = ['x1', 'y1', 'u1', 'v1', 'x2', 'y2', 'u2', 'v2']
    inst = Instance(nodes, [('x1', 'v1'), ('y1', 'u1'), ('x2', 'v2'), ('y2', 'u2')], None)
    G = [['x1', 'y1'], ['u1', 'v1'], ['x2', 'y2'], ['u2', 'v2']]; H = [['x1', 'u1'], ['y1', 'v1'], ['x2', 'u2'], ['y2', 'v2']]
    specs = [(G, {(2, 3): 4}), (H, {(2, 3): 4})]
    if len(sys.argv) > 5 and sys.argv[5] == 'tight':   # control: bond 2 instead of 4 must FAIL (flattening: rank 4 needed)
        specs = [(G, {(2, 3): 2}), (H, {(2, 3): 2})]
elif mode.startswith('cyc'):
    inst = Instance(range(1, 9), E8two, None)
    adj, a, b = (2, 2, 2) if mode == 'cyc2' else map(int, mode.split('_')[1:4])
    specs = [(G8, K4(adj, a, b)), (H8, K4(adj, a, b))]
elif mode.startswith('prism'):
    parts = mode.split('_'); bd = tuple(map(int, parts[1:4])); three = len(parts) > 4
    inst = Instance('ABCDEF', EP, None)
    bP = {(0, 1): bd[0], (0, 2): bd[1], (1, 2): bd[2]}
    specs = [(GP, bP), (HP, bP)] + ([(GP, bP)] if three else [])
t0 = time.time(); res = []
for r in range(restarts):
    best, nets, ns = als(inst, specs, rng, sweeps)
    res.append(best)
    print(f"{mode} restart {r}: residual {best:.3e} after {ns} sweeps ({time.time() - t0:.0f}s)", flush=True)
    if best < 1e-8 and mode not in ('rect', 'planted8', 'tworect'): print("  EXACT CANDIDATE", flush=True); break
res = np.array(res)
print(f"SUMMARY {mode}: {len(res)} restarts x <= {sweeps} sweeps: min {res.min():.6f}, median {np.median(res):.6f}, max {res.max():.6f},"
      f" #exact(<1e-8) {int((res < 1e-8).sum())}")
