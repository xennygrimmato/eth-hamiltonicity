"""rc_crit.py -- the ansatz f = R + C (R a G-network, C an H-network) with the other-merge costs at raw: pieces (a, raw), (raw, b);
criterion  raw - (raw-a)(raw-b)/(2 raw - a - b) + 1 < raw  (min over q of the max).  Evaluated on the GH frontiers printed in
realdims.out (real bond dimensions) and frontier.out / twoterm.out (powers of 2).  Monotone, so the frontier suffices."""
import re, numpy as np
def crit(a, b, raw):
    if a >= raw or b >= raw: return raw + 1.0
    return raw - (raw - a) * (raw - b) / (2 * raw - a - b) + 1
txt = open(__import__('os').path.join(__import__('os').path.dirname(__file__) or '.', 'realdims.out')).read()
blocks = re.split(r'\n(?=\[)', txt)
label = None
for line in txt.splitlines():
    m = re.match(r'\[(.*?)\] \d+ patterns', line)
    if m: label = m.group(1); raw = 9 if label == 'prism' else 12
    if 'frontier GH' in line:
        pts = [(float(x), float(y)) for x, y in re.findall(r'np\.float64\(([\d.]+)\), np\.float64\(([\d.]+)\)', line)]
        v = min((crit(a, b, raw), a, b) for a, b in pts)
        print(f"{label}: R+C with raw cross costs, best over the real-dimension GH frontier: criterion {v[0]:.4f} at (a,b)=({v[1]},{v[2]}) (trade iff < {raw})")
for raw, pts, label in ((9, [(0, 9), (7, 8), (8, 7), (9, 0)], 'prism, powers of 2'), (12, [(0, 12), (10, 11), (11, 10), (12, 0)], '8-cycle two-cell, powers of 2')):
    v = min((crit(a, b, raw), a, b) for a, b in pts)
    print(f"{label}: criterion {v[0]:.4f} at {v[1:]}")
