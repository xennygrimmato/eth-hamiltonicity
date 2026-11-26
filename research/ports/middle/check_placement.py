#!/usr/bin/env python3
"""Independent check of a placement saved by `tensorlab/examples/rankplace.rs` (JSON):
recomputes E_pairs D, E_edges D and the ratio with a plain-Python F_2 rank, from the stored edge list.
Usage: python3 check_placement.py file.json [file.json ...]"""
import json, sys

def rank(x):
    rows = [(x >> (8 * i)) & 0xFF for i in range(8)]
    basis = {}
    r = 0
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v; r += 1; break
    return r

for path in sys.argv[1:]:
    J = json.load(open(path))
    f = [int(h, 16) for h in J["f"]]
    n = J["n"]; E = J["edges"]
    assert len(f) == n
    deg = [0] * n
    for u, v in E: deg[u] += 1; deg[v] += 1
    assert len(set(deg)) == 1, "not regular"
    cache = {}
    def rk(a, b):
        x = a ^ b
        if x not in cache: cache[x] = rank(x)
        return cache[x]
    P = sum(rk(f[u], f[v]) for u in range(n) for v in range(n)) / n**2
    Ee = sum(rk(f[u], f[v]) for u, v in E) / len(E)
    print(f"{path.split('/')[-1]}: n={n} mu={J['mu']} E_pairs={P:.6f} E_edges={Ee:.6f} ratio={P/Ee:.6f} (stored {J['ratio']:.6f})"
          + ("" if abs(P / Ee - J['ratio']) < 1e-9 else "  MISMATCH"))
