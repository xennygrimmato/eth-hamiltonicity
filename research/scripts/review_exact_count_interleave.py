#!/usr/bin/env python3
"""Targeted test of the global interleaving sign: graphs whose crossing edges concentrate on
interleaving bundle pairs (0,2)/(1,3) (g=4) or several interleaving pairs (g=5,6).  Compares the
blob value with and without the global sign against the exact (weighted) target."""
import random, sys
import review_exact_count as R
from review_exact_count_ablate import value_no_global

def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    c = dict(tested=0, ok=0, noglobal_wrong=0)
    for t in range(trials):
        g = rng.choice([4, 4, 5, 6]); n = rng.randint(max(g, 6), 9)
        blob = [v % g for v in range(n)]
        rng.shuffle(blob)
        if max(blob) < g - 1: continue
        edges = set()
        perm = list(range(n)); rng.shuffle(perm)
        for i in range(n):       # a Hamiltonian cycle so the count is nonzero
            edges.add(tuple(sorted((perm[i], perm[(i + 1) % n]))))
        for i in range(n):
            for j in range(i + 1, n):
                d = abs(blob[i] - blob[j])
                if d >= 1 and rng.random() < (0.35 if d >= 2 else 0.25): edges.add((i, j))
        edges = sorted(edges)
        if len(edges) > 16: continue
        pos = list(range(n)); rng.shuffle(pos); r = rng.randrange(n)
        weighted = rng.random() < 0.5
        w = [rng.randint(1, 3) for _ in edges] if weighted else None
        u = [rng.choice([-2, -1, 1, 2, 3]) for _ in edges] if weighted else None
        B = R.Blobs(n, edges, r, blob, pos, 6, w, u)
        if len(B.cross) > 14: continue
        tgt = 0
        for X in R.two_factors(n, edges):
            pw = 1
            for k in X: pw *= (w[k] if w else 1)
            tgt += pw * R.tau(n, edges, X, r, u)
        c['tested'] += 1
        c['ok'] += B.value() == tgt
        c['noglobal_wrong'] += value_no_global(B) != tgt
    print(c)
if __name__ == "__main__":
    main()
