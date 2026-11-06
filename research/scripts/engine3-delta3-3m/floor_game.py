"""floor_game.py -- floors for the THREE-merge game on Delta_3 (merges rows r, columns c, diagonals r-c).  [C]/[R]
(1) min-floor flattening certificate D3 = max_o min_k d_k(o) over all 3^9 orientations (closed form d_k = max_G |n_G|,
    n_G = net flow out of group G; identical to flatcert4 / q3_threemerge), and the same for every pair of merges.
(2) GAME floor from flattenings: for each orientation o, pigeonhole gives ONE piece with c_k >= d_k(o) lambda - O(log T)
    for all k simultaneously; the adversary mixes such pieces:  V >= max_{p in Delta(S)} min_k sum_s p_s s_k  (LP),
    S = {d(o)} (vectors), optionally with the CVZ per-merge full vectors 9 e_k (Theorem 1 of engine3-delta3-proof.md:
    for each merge k some piece has c_k >= 9 lambda - 1.5 log T) and the core vector (3,3,3).
    Fractional orientations are dominated (each d_k is convex in the flow), so integer orientations suffice.
(3) pigeonhole floor 9/3 (mix of the three CVZ-full pieces)."""
import itertools, numpy as np
from scipy.optimize import linprog
nodes = [(r, c) for r in range(3) for c in range(3)]
edges = [(u, v) for u, v in itertools.combinations(nodes, 2) if (u[0] + u[1]) % 3 == (v[0] + v[1]) % 3]
MER = {'r': lambda v: v[0], 'c': lambda v: v[1], 'd': lambda v: (v[0] - v[1]) % 3}
vecs = {}
for o in itertools.product((0, 1, -1), repeat=9):
    if not any(o): continue
    fl = {v: 0 for v in nodes}
    for (u, v), oe in zip(edges, o): fl[u] += oe; fl[v] -= oe
    d = tuple(max(abs(sum(fl[v] for v in nodes if MER[m](v) == g)) for g in range(3)) for m in 'rcd')
    vecs.setdefault(d, o)
print(f'distinct (d_r,d_c,d_d) vectors over 3^9-1 orientations: {len(vecs)}')
for ms in (('r', 'c'), ('r', 'd'), ('c', 'd'), ('r', 'c', 'd')):
    ix = ['rcd'.index(m) for m in ms]
    best = max(vecs, key=lambda d: min(d[i] for i in ix))
    print(f'min-floor D over merges {ms}: {min(best[i] for i in ix)} of 9, vector {best}, orientation {vecs[best]}')
def game(S, k):
    S = np.array(S, float); n = len(S)
    # max t s.t. S^T p >= t, sum p = 1
    A = np.hstack([-S[:, :k].T, np.ones((k, 1))])
    r = linprog(np.r_[np.zeros(n), -1], A_ub=A, b_ub=np.zeros(k), A_eq=[np.r_[np.ones(n), 0]], b_eq=[1],
                bounds=[(0, None)] * n + [(None, None)], method='highs')
    p = r.x[:n]; sup = [(tuple(int(x) for x in S[i]), round(p[i], 4)) for i in np.argsort(-p) if p[i] > 1e-9]
    return -r.fun, sup
V = list(vecs)
cvz3 = [(9, 0, 0), (0, 9, 0), (0, 0, 9)]
for lab, S, k in (('flattening vectors only, 3 merges', V, 3),
                  ('CVZ full vectors only (pigeonhole), 3 merges', cvz3, 3),
                  ('flattening + CVZ + core (3,3,3), 3 merges', V + cvz3 + [(3, 3, 3)], 3),
                  ('flattening only, 2 merges (r,c)', [v[:2] for v in V], 2),
                  ('flattening + CVZ, 2 merges (r,c) [Theorem 1 check: >= 4.5]', [v[:2] for v in V] + [(9, 0), (0, 9)], 2)):
    val, sup = game(S, k)
    print(f'GAME floor [{lab}]: V >= {val:.6f} lambda  (rho >= {val/9:.4f});  optimal mixture {sup[:8]}')
# the q-side: for the 3-merge floor LP, the dual q (weights on merges) certifying the floor is tight
# dual check: uniform q certifies the floor is exactly 4 within the flattening+CVZ world (min_q max_s <q,s>)
A = np.array(V + cvz3 + [(3, 3, 3)], float)
print('dual: with q = (1/3,1/3,1/3), max_s <q,s> =', (A.sum(1) / 3).max(), '; vectors with coordinate sum 12:',
      sorted(set(tuple(v) for v in V if sum(v) == 12))[:12], '... count', sum(1 for v in V if sum(v) == 12))
print('max single coordinate over flattening vectors:', A[:len(V)].max(), '; e.g. vectors with a 6:', [v for v in V if max(v) == 6][:6])
