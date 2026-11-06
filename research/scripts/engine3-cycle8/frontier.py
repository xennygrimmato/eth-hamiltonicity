"""frontier.py -- EXACT: which two-term ansaetze f = R + C (R a G-network, C an H-network, K_4 bonds of dimensions 2^e,
e in {0..4}) on the 12 two-cell edges of the 8-cycle (N = 2, one bit per edge) survive EVERY single-flattening test of
flatgap.py?  Over any field.  For a pair (e_R, e_C) the pair is excluded iff some contraction M has 2^-gapR + 2^-gapC < 1,
i.e. (gapR>=1 and gapC>=2) or (gapR>=2 and gapC>=1).  Computed with boolean matrix products over the classes of reachable
n^G and n^H (relation Rel = reachable pairs).  Reports the Pareto frontier of (cost_G(R), cost_H(C)) among survivors and
whether any survivor meets the trade criterion  min_q max_i <q,c(i)> + log2 2 < 12  with the other-merge costs at raw (12).
Also: same for the prism (3 groups, raw 9) for part (c), and with 3 terms R + R' + C (bonds of R' = bonds of R)."""
import itertools, numpy as np, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from flatgap import make, gaps, C8, E8_two, PR, EPR

def run(nodes, edges, merges, raw, emax, label):
    B = make(nodes, edges, merges)
    nG, iG = np.unique(B[0], axis=0, return_inverse=True); nH, iH = np.unique(B[1], axis=0, return_inverse=True)
    Rel = np.zeros((len(nG), len(nH)), bool); Rel[iG.ravel(), iH.ravel()] = True
    r = len(merges[0]); pairs = list(itertools.combinations(range(r), 2))
    pats = [p for p in itertools.product(range(emax + 1), repeat=len(pairs)) if sum(p) <= raw]
    print(f"[{label}] states {len(B[0])}, distinct n^G {len(nG)}, n^H {len(nH)}; bond patterns with cost <= raw: {len(pats)}", flush=True)
    gG = np.array([gaps(nG, dict(zip(pairs, p))) for p in pats]); gH = np.array([gaps(nH, dict(zip(pairs, p))) for p in pats])
    A1 = (gG >= 1).astype(np.float32); A2 = (gG >= 2).astype(np.float32)
    C1 = (gH >= 1).astype(np.float32); C2 = (gH >= 2).astype(np.float32)
    Rf = Rel.astype(np.float32)
    X = ((A1 @ Rf) @ C2.T > 0) | ((A2 @ Rf) @ C1.T > 0)      # excluded matrix, pats x pats
    cost = np.array([sum(p) for p in pats])
    surv = ~X
    best = {}
    for i, j in zip(*np.nonzero(surv)):
        key = (cost[i], cost[j])
        best.setdefault(key, (pats[i], pats[j]))
    keys = sorted(best)
    pareto = [k for k in keys if not any(o != k and o[0] <= k[0] and o[1] <= k[1] for o in keys)]
    print(f"[{label}] surviving (cost_G(R), cost_H(C)) Pareto frontier: {pareto}")
    for k in pareto: print(f"     e.g. R bonds {best[k][0]}  C bonds {best[k][1]}  (pairs {pairs})")
    def crit(a, b):
        # pieces (a, raw), (raw, b); min_q max
        qs = np.linspace(0, 1, 100001); return float(np.min(np.maximum(qs * a + (1 - qs) * raw, qs * raw + (1 - qs) * b)))
    ok = [(k, crit(*k) + 1) for k in keys if crit(*k) + 1 < raw - 1e-9]
    print(f"[{label}] survivors meeting the 2-term trade criterion (other-merge costs raw = {raw}): {ok if ok else 'NONE'}")
    print(f"[{label}] smallest criterion value among survivors: {min(crit(*k) + 1 for k in keys):.4f} (needs < {raw})")
    # also: survivors with symmetric cost (same pattern up to the G->H map is the dihedral map, so just costs)
    sym = sorted(k for k in keys if k[0] == k[1])
    print(f"[{label}] minimal symmetric surviving cost: {sym[0] if sym else None}", flush=True)
    # three terms R + R' + C with R' same bond pattern as R:  excluded iff some state has 2*2^-gR + 2^-gC < 1
    # gR=0 never; gR=1 needs gC>=... 2*0.5=1 not <1 ; gR>=2: 2*2^-gR <= 1/2, needs 2^-gC < 1 - 2^{1-gR}
    # => (gR==2 and gC>=2) or (gR>=3 and gC>=1)
    B2 = (gG == 2).astype(np.float32); B3 = (gG >= 3).astype(np.float32)
    X3 = ((B2 @ Rf) @ C2.T > 0) | ((B3 @ Rf) @ C1.T > 0)
    keys3 = sorted({(cost[i], cost[j]) for i, j in zip(*np.nonzero(~X3))})
    p3 = [k for k in keys3 if not any(o != k and o[0] <= k[0] and o[1] <= k[1] for o in keys3)]
    print(f"[{label}] three terms R+R'+C (R' with R's bonds): surviving Pareto (cost_G(R)=cost_G(R'), cost_H(C)): {p3}")
    def crit3(a, b):
        qs = np.linspace(0, 1, 100001); return float(np.min(np.maximum(qs * a + (1 - qs) * raw, qs * raw + (1 - qs) * b)))
    ok3 = [k for k in keys3 if crit3(*k) + np.log2(3) < raw - 1e-9]
    print(f"[{label}] 3-term survivors meeting criterion (+log2 3): {ok3 if ok3 else 'NONE'}", flush=True)

if __name__ == '__main__':
    run(list(PR['nodes']), EPR, [PR['G'], PR['H']], 9, 3, "prism")
    run(C8['nodes'], E8_two, [C8['G'], C8['H']], 12, 4, "8-cycle two-cell")
