"""Exact system sizes and ranks [N, sympy DomainMatrix over QQ] for the worst occurrences of given designs:
at R = R_o (feasible: rank A = rank [A|b]) and R = R_o - 1 (infeasible: rank [A|b] = rank A + 1).
usage: python3 system_sizes.py design.pkl [...]"""
import sys, os, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2common import occurrences, min_R_occ, occ_system, rank_exact, lower_count
for fn in sys.argv[1:]:
    d = pickle.load(open(fn, 'rb'))
    if 'rows' not in d:
        d['rows'] = [[[{v: 1} for v in d['meas'][t] if d['part'][t][v] == h] for h in range(d['r'])] for t in range(d['Q'])]
    occ = occurrences(d['clauses'])
    Rs = {o: min_R_occ(d, *o) for o in occ}
    Rm = max(Rs.values()); worst = [o for o in occ if Rs[o] == Rm][:3]
    print(os.path.basename(fn), f"R_max={Rm}", f"#occ at max={sum(1 for o in occ if Rs[o]==Rm)}/{len(occ)}")
    for o in worst:
        for R in (Rm, Rm - 1):
            if R < 0: continue
            A, b = occ_system(d, o[0], o[1], R)
            if not A or not A[0]:
                print(f"  occ {o} R={R}: empty system (no unknowns), lower bound L_o={lower_count(d,*o)}"); continue
            ra = rank_exact(A); rab = rank_exact([x + [y] for x, y in zip(A, b)])
            print(f"  occ {o} R={R}: {len(A)} eqs x {len(A[0])} unknowns, rank A={ra}, rank[A|b]={rab} -> {'feasible' if ra==rab else 'INFEASIBLE'}"
                  f"   (L_o={lower_count(d,*o)})")
