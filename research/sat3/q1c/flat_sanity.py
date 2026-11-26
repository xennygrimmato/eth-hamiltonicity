"""Sanity test of relax.py: with every CN / variance inequality imposed as an EQUALITY the metric on the point set is
Euclidean. Without node barycentres the bound stays at the cap (convexity of the leg functions is only tested on
midpoints); with node barycentres the barycentre chain is available and the bound is the flat value 9*sqrt(3)."""
from relax import *
net = delta3()
for spec in (['nodemid'], ['nodemid', 'samemid', 'edgemid'], ['nodebar'], ['nodemid', 'nodebar'], ['nodemid', 'nodebar', 'edgebar']):
    print("FLAT (all CN/variance as equalities), spec", spec)
    solve(net, level_points(net, spec), cn_eq=True)
print("flat value 9*sqrt(3) =", 9 * 3 ** 0.5, "  cap 27/sqrt(2) =", 27 / 2 ** 0.5)
