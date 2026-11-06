"""party_dq.py -- party-lemma floors for Delta_q (one parallel class of AG(2,q) as configuration, q lines = K_q's, E = q*C(q,2))
under THREE other parallel classes as merges (rows y=const, columns x=const, 'diagonals' y-x=const), q prime.
Party lemma (engine3-pmerge.md, Thm 2): choose groups S_k of merge k (k = 1,2,3); delete every point lying in chosen groups of
two different merges; parties X_G = G minus deleted (one party per chosen group); H = union.  Some piece has, for all k,
   c_k >= max( max_{G in S_k} e(X_G, H\\X_G), (1/2) sum_{G in S_k} e(X_G, H\\X_G) ) * lambda - O(log T).
Reported: best min_k (over choices up to symmetry: a_k = |S_k| and a generic choice) as a fraction of E, i.e. a lower bound on
the min-floor M and on V at every q; and the game floor from mixing this piece with the three CVZ-full pieces (LP)."""
import itertools, numpy as np, sys
from scipy.optimize import linprog
def run(q):
    pts = [(x, y) for x in range(q) for y in range(q)]
    conf = lambda p: (p[0] + p[1]) % q           # configuration class: x + y = const
    mer = [lambda p: p[1], lambda p: p[0], lambda p: (p[1] - p[0]) % q]
    edges = [(u, v) for u, v in itertools.combinations(pts, 2) if conf(u) == conf(v)]
    E = len(edges)
    groups = [[[p for p in pts if m(p) == g] for g in range(q)] for m in mer]
    best = (0, None); bestgame = (0, None)
    rng = np.random.default_rng(1)
    tried = set()
    for a in itertools.product(range(q + 1), repeat=3):
        if sum(a) == 0: continue
        for rep in range(6 if q > 3 else 1):
            S = [tuple(sorted(rng.choice(q, a[k], replace=False).tolist())) for k in range(3)]
            key = (a, tuple(S))
            if key in tried: continue
            tried.add(key)
            chosen = [[groups[k][g] for g in S[k]] for k in range(3)]
            inter = set()
            for k1, k2 in ((0, 1), (0, 2), (1, 2)):
                for G1 in chosen[k1]:
                    for G2 in chosen[k2]:
                        inter |= set(G1) & set(G2)
            parties = [[(k, [p for p in G if p not in inter]) for G in chosen[k]] for k in range(3)]
            H = set(p for k in range(3) for (_, X) in parties[k] for p in X)
            Eh = [(u, v) for (u, v) in edges if u in H and v in H]
            cs = []
            for k in range(3):
                es = []
                for (_, X) in parties[k]:
                    Xs = set(X)
                    es.append(sum(1 for (u, v) in Eh if (u in Xs) != (v in Xs)))
                cs.append(max(max(es) if es else 0, 0.5 * sum(es)))
            val = min(cs)
            if val > best[0]: best = (val, (a, S, cs))
            # game: mix with full pieces (E,0,0),(0,E,0),(0,0,E)
            Smat = np.array([[E, 0, 0], [0, E, 0], [0, 0, E], cs], float)
            A = np.hstack([-Smat.T, np.ones((3, 1))])
            r = linprog(np.r_[np.zeros(4), -1], A_ub=A, b_ub=np.zeros(3), A_eq=[np.r_[np.ones(4), 0]], b_eq=[1],
                        bounds=[(0, None)] * 4 + [(None, None)], method='highs')
            if -r.fun > bestgame[0]: bestgame = (-r.fun, (a, cs))
    print(f'q = {q}: E = {E}; party-lemma min-floor >= {best[0]} = {best[0]/E:.4f} E  (a = {best[1][0]}, costs {best[1][2]});'
          f'  game floor (party piece + CVZ-full mixture) >= {bestgame[0]:.3f} = {bestgame[0]/E:.4f} E; pigeonhole 1/3, core floor 1/q')
for q in (3, 5, 7):
    run(q)
