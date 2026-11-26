"""Cones over high-girth cubic graphs: how badly do they violate the Euclidean Poincare constant of the graph itself?

Link = graph with every edge of angular length theta = 2 pi / girth (so the cone is nonpositively curved: no closed
geodesic in the link shorter than 2 pi).  Place vertex v at radius 1 on its own ray.  Then
   d(u,v)^2 = 2 - 2 cos(min(theta * dist_G(u,v), pi)).
Poincare ratio  V/E  with  V = mean of d^2 over all ordered pairs,  E = mean of d^2 over edges.
For Euclidean placements the best constant is 1/(1 - lambda_2) (lambda_2 = second eigenvalue of the normalised adjacency)."""
import networkx as nx, numpy as np, math
pi = math.pi
graphs = {
  "Petersen": nx.petersen_graph(),
  "Heawood": nx.heawood_graph(),
  "McGee": nx.LCF_graph(24, [12, 7, -7], 8),
  "Tutte-Coxeter": nx.LCF_graph(30, [-13, -9, 7, -7, 9, 13], 5),
  "Balaban 10-cage": nx.LCF_graph(70, [-9,-25,-19,29,13,35,-13,-29,19,25,9,-29,29,17,33,21,9,-13,-31,-9,25,17,9,-31,27,-9,17,-19,-29,27,-17,-9,-29,33,-25,25,-21,17,-17,29,35,-29,17,-17,21,-25,25,-33,29,9,17,-27,29,19,-17,9,-27,31,-9,-17,-25,9,31,13,-9,-21,-33,-17,-29,29], 1),
  "Tutte 12-cage": nx.LCF_graph(126, [17, 27, -13, -59, -35, 35, -11, 13, -53, 53, -27, 21, 57, 11, -21, -57, 59, -17], 7),
}
def girth(G):
    best = 10**9
    for s in G:
        dist = {s: 0}; par = {s: None}; q = [s]
        while q:
            u = q.pop(0)
            for w in G[u]:
                if w not in dist: dist[w] = dist[u] + 1; par[w] = u; q.append(w)
                elif par[u] != w: best = min(best, dist[u] + dist[w] + 1)
    return best
rows = []
print("%-16s %4s %5s %9s %9s %9s %7s" % ("graph", "n", "girth", "lambda_2", "Euclid", "cone", "ratio"))
for name, G in graphs.items():
    n = G.number_of_nodes(); g = girth(G); assert all(d == 3 for _, d in G.degree())
    A = nx.to_numpy_array(G)/3; lam2 = np.sort(np.linalg.eigvalsh(A))[-2]; gam = 1/(1 - lam2)
    th = 2*pi/g; D = dict(nx.all_pairs_shortest_path_length(G))
    V = sum(2 - 2*math.cos(min(th*D[u][v], pi)) for u in G for v in G)/n**2
    E = 2 - 2*math.cos(th)
    rows.append((name, n, g, lam2, gam, V/E)); print("%-16s %4d %5d %9.4f %9.3f %9.3f %7.2f" % (name, n, g, lam2, gam, V/E, V/E/gam))
import json; json.dump(rows, open("cages.json", "w"))
print("\nIdealised trend for a cubic graph of girth g whose typical pairs are at distance >= g/2:  cone ratio -> 4 / (2 - 2 cos(2 pi/g)) ~ g^2/pi^2,")
print("against the Ramanujan value 1/(1 - 2 sqrt2/3) = %.2f for the Euclidean constant.  Crossover near g = %.0f." % (1/(1 - 2*math.sqrt(2)/3), pi*math.sqrt(1/(1 - 2*math.sqrt(2)/3))))
