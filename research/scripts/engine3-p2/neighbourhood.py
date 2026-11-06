"""Exhaustive single-slot neighbourhood [N]: for a design, for every (t,h) and every way of replacing ONE row of
R_{t,h} (or adding one, if fewer than rho rows) by ANY integer row with entries in {-2..2} supported in S_{t,h}
(all such rows up to sign), recompute all R_o exactly (mod p) and record whether (max R, sum R) improves
lexicographically, ties, or worsens.  Partitions/assignments fixed.
usage: python3 neighbourhood.py design.pkl [maxsupport]
"""
import sys, os, pickle, itertools, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2common import occurrences, min_R_occ, rank_exact
fn = sys.argv[1]; maxsup = int(sys.argv[2]) if len(sys.argv) > 2 else 99
d = pickle.load(open(fn, 'rb'))
if 'rows' not in d:
    r = d['r']; d['rows'] = [[[{v: 1} for v in d['meas'][t] if d['part'][t][v] == h] for h in range(r)] for t in range(d['Q'])]
cl = d['clauses']; occ = occurrences(cl); Q = d['Q']; r = d['r']; rho = d['rho']; n = d['n']
base = {o: min_R_occ(d, *o) for o in occ}
b0 = (max(base.values()), sum(base.values()))
t0 = time.time()
stats = {'improve': 0, 'tie': 0, 'worse': 0, 'tested': 0}
best = (b0, None); tie_nonsingle = 0; tie_newspace = []
for t in range(Q):
    for h in range(r):
        S = [v for v in range(n) if d['part'][t][v] == h]
        cands = []
        for vals in itertools.product(range(-2, 3), repeat=len(S)):
            nz = [x for x in vals if x != 0]
            if not nz or nz[0] < 0 or len(nz) > maxsup: continue     # up to sign
            cands.append({S[i]: x for i, x in enumerate(vals) if x != 0})
        old = d['rows'][t][h]
        slots = list(range(len(old))) + ([len(old)] if len(old) < rho else [])
        aff = [o for o in occ if d['alpha'][t][o[0]] != h]
        for sl in slots:
            for rw in cands:
                new = list(old)
                if sl < len(old): new[sl] = rw
                else: new.append(rw)
                d['rows'][t][h] = new
                Rs = dict(base)
                for o in aff: Rs[o] = min_R_occ(d, *o)
                key = (max(Rs.values()), sum(Rs.values()))
                stats['tested'] += 1
                if key < b0: stats['improve'] += 1
                elif key == b0:
                    stats['tie'] += 1
                    if len(rw) > 1:
                        tie_nonsingle += 1
                        # does the replacement change the space R_{t,h}?  (same span <=> equal ranks of old, new, old+new)
                        mat = lambda L: [[x.get(v, 0) for v in S] for x in L]
                        ro, rn, rb = rank_exact(mat(old)) if old else 0, rank_exact(mat(new)), rank_exact(mat(old + new))
                        if not (ro == rn == rb):
                            # also not 'irrelevant': record
                            tie_newspace.append((t, h, sl, rw))
                else: stats['worse'] += 1
                if key < best[0]: best = (key, (t, h, sl, rw))
        d['rows'][t][h] = old
print(json.dumps({'file': os.path.basename(fn), 'base': b0, **stats, 'ties_with_nonsingleton_row': tie_nonsingle,
                  'ties_nonsingleton_new_space': len(tie_newspace), 'examples_new_space': str(tie_newspace[:4]),
                  'best': [best[0], str(best[1])], 'secs': round(time.time() - t0)}))
