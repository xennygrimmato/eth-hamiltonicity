"""(rho+1)-minor lemma [R, proved in engine3-p2.md] checked on found designs [N]:
for occurrences o_1..o_{k} (k = rho+1) with distinct own variables v_1..v_k, the k x k matrix
(P_{o_j}(T))_{v_i} has det(0) = 1 and degree <= sum_j R_{o_j}; at every point t where all v_i lie in one group h
with alpha_t(e_j) != h for all j, its rows lie in R_{t,h}|_{v's} (dim <= rho), so det(t) = 0.  Hence
  #{co-absorption points of the tuple} <= sum_j R_{o_j}.
We count the co-absorption points for every tuple, check the inequality, and evaluate the averaged bound
  R >= sum_t sum_h #tuples(t,h) / (k * #tuples).
usage: python3 minor_check.py design.pkl [rho]
"""
import sys, os, pickle, itertools, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2common import occurrences, min_R_occ
fn = sys.argv[1]
d = pickle.load(open(fn, 'rb'))
if 'rows' not in d:   # stage-1 singleton design
    r = d['r']; d['rows'] = [[[{v: 1} for v in d['meas'][t] if d['part'][t][v] == h] for h in range(r)] for t in range(d['Q'])]
cl = d['clauses']; occ = occurrences(cl); Q = d['Q']
rho = int(sys.argv[2]) if len(sys.argv) > 2 else max(len(rl) for rt in d['rows'] for rl in rt)
dims = max(len(rl) for rt in d['rows'] for rl in rt)
k = rho + 1
Rs = {o: min_R_occ(d, *o) for o in occ}
cnt = {}
tot_events = 0
for t in range(Q):
    r = len(d['rows'][t])
    for h in range(r):
        F = [o for o in occ if d['part'][t][o[1]] == h and d['alpha'][t][o[0]] != h]
        for tup in itertools.combinations(F, k):
            if len({o[1] for o in tup}) < k: continue
            cnt[tup] = cnt.get(tup, 0) + 1; tot_events += 1
viol = [(tup, c) for tup, c in cnt.items() if c > sum(Rs[o] for o in tup)]
ntup = sum(1 for tup in itertools.combinations(occ, k) if len({o[1] for o in tup}) == k)
tight = max([c / max(1, sum(Rs[o] for o in tup)) for tup, c in cnt.items()] or [0])
print(json.dumps({'file': os.path.basename(fn), 'rho_used': rho, 'max_dim': dims, 'R': max(Rs.values()),
                  'tuples_coabsorbed': len(cnt), 'violations': len(viol), 'max_count_over_sumR': round(tight, 3),
                  'averaged_bound_R>=': round(tot_events / (k * ntup), 4)}))
