#!/usr/bin/env python3
"""(weighted) Ablation for review_exact_count.py: drop the global interleaving sign (or the same-bundle
C(N,2) term) and check that the tests then FAIL, i.e. the test-suite is sensitive to them."""
import random, sys, itertools
import review_exact_count as R

def value_no_global(B):
    tot = 0
    for lab in B.labels_iter():
        prod = 1
        for a in range(B.g):
            prod *= B.T(a, tuple(lab[k] for k in B.inc[a]))
        tot += prod
    return tot

def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    cnt = dict(tested=0, full_ok=0, noglobal_wrong=0, g_ge4=0)
    for t in range(trials):
        n = rng.randint(6, 9)
        edges = R.random_graph(n, rng.uniform(0.35, 0.7), rng, 'cubicish' if rng.random() < .5 else None)
        if len(edges) > 16: continue
        r = rng.randrange(n)
        g = rng.randint(4, 6)
        perm = list(range(n)); rng.shuffle(perm)
        blob = [0] * n
        for i, v in enumerate(perm): blob[v] = i % g
        pos = list(range(n)); rng.shuffle(pos)
        w = [rng.randint(1, 3) for _ in edges]; u = [rng.choice([-3, -2, -1, 1, 2, 3]) for _ in edges]
        B = R.Blobs(n, edges, r, blob, pos, 6, w, u)
        if len(B.cross) > 14: continue
        cnt['tested'] += 1; cnt['g_ge4'] += max(blob) >= 3
        tgt = 0
        for X in R.two_factors(n, edges):
            pw = 1
            for k in X: pw *= w[k]
            tgt += pw * R.tau(n, edges, X, r, u)
        v = B.value(); cnt['full_ok'] += v == tgt
        cnt['noglobal_wrong'] += value_no_global(B) != tgt
    print(cnt)
if __name__ == "__main__":
    main()
