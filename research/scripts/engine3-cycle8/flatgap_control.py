"""flatgap_control.py -- consistency of flatgap.py with the ALS controls: the two-rectangle instance (als_runs.py tworect):
R bond 4 on (G3,G4) + C bond 4 on (H3,H4) must NOT be excluded (an exact identity exists); bond 2 must be excluded."""
import sys; sys.path.insert(0, __import__('os').path.dirname(__file__))
from flatgap import make, test
nodes = ['x1', 'y1', 'u1', 'v1', 'x2', 'y2', 'u2', 'v2']
E = [('x1', 'v1'), ('y1', 'u1'), ('x2', 'v2'), ('y2', 'u2')]
G = [['x1', 'y1'], ['u1', 'v1'], ['x2', 'y2'], ['u2', 'v2']]; H = [['x1', 'u1'], ['y1', 'v1'], ['x2', 'u2'], ['y2', 'v2']]
B = make(nodes, E, [G, H])
for e in (2, 1):
    b = {(i, j): 0 for i in range(4) for j in range(i + 1, 4)}; b[(2, 3)] = e
    print(f"tworect bonds 2^{e} on (3,4): excluded = {test(B, [(0, b), (1, b)])[0]}")
rect = make('xyuv', [('x', 'v'), ('y', 'u')], [[['x', 'y'], ['u', 'v']], [['x', 'u'], ['y', 'v']]])
print("rectangle bonds 1 (App. H): excluded =", test(rect, [(0, {(0, 1): 0}), (1, {(0, 1): 0})])[0])
