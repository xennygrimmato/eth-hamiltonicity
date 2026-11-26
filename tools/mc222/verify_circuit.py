#!/usr/bin/env python3
"""Independent check of a circuit file written by the search (or by hand).

Evaluates the straight-line program on every input in F2^n and compares each output with the
target function, which is recomputed here from its definition (not from the search code).

File format:  G <u-list> | <v-list>   (one line per AND gate, in order)
              O <name> <list>          (output = XOR of the listed generators)
Generator indices: 0 = constant 1, 1..n = inputs x0..x(n-1), n+1+i = AND gate i.
"""
import sys
from itertools import product


def targets(problem):
    if problem == "mm222":  # x = a11 a12 a21 a22 b11 b12 b21 b22
        def f(x):
            A = [[x[0], x[1]], [x[2], x[3]]]
            B = [[x[4], x[5]], [x[6], x[7]]]
            return {f"c{i+1}{j+1}": (A[i][0] & B[0][j]) ^ (A[i][1] & B[1][j]) for i in range(2) for j in range(2)}
        return 8, f
    if problem == "mm221":
        def f(x):
            return {f"c{i+1}": (x[2*i] & x[4]) ^ (x[2*i+1] & x[5]) for i in range(2)}
        return 6, f
    if problem in ("polymul2", "polymul3"):
        t = 2 if problem == "polymul2" else 3
        def f(x):
            a, b = x[:t], x[t:]
            out = {}
            for s in range(2*t - 1):
                v = 0
                for i in range(t):
                    if 0 <= s - i < t:
                        v ^= a[i] & b[s-i]
                out[f"c{s}"] = v
            return out
        return 2*t, f
    if problem == "f4":  # (a0 + a1 w)(b0 + b1 w), w^2 = w + 1
        def f(x):
            a0, a1, b0, b1 = x
            return {"c0": (a0 & b0) ^ (a1 & b1), "c1": (a0 & b1) ^ (a1 & b0) ^ (a1 & b1)}
        return 4, f
    raise SystemExit("unknown problem " + problem)


def main(path):
    lines = [l.split("#")[0].strip() for l in open(path)]
    head = open(path).readline()
    problem = head.split()[2]
    n, f = targets(problem)
    gates, outs = [], {}
    for l in lines:
        if not l:
            continue
        if l.startswith("G "):
            u, v = l[2:].split("|")
            gates.append(([int(t) for t in u.split()], [int(t) for t in v.split()]))
        elif l.startswith("O "):
            w = l.split()
            outs[w[1]] = [int(t) for t in w[2:]]
    for i, (u, v) in enumerate(gates):
        assert all(t < n + 1 + i for t in u + v), "gate uses a later gate"
    for x in product([0, 1], repeat=n):
        val = [1] + list(x)
        for u, v in gates:
            lu = 0
            for t in u:
                lu ^= val[t]
            lv = 0
            for t in v:
                lv ^= val[t]
            val.append(lu & lv)
        want = f(x)
        assert set(want) == set(outs), "output names differ"
        for name, lst in outs.items():
            got = 0
            for t in lst:
                got ^= val[t]
            assert got == want[name], f"mismatch at input {x} output {name}"
    print(f"OK: {path}: {problem}, {len(gates)} AND gates, all {2**n} inputs, {len(outs)} outputs correct")


if __name__ == "__main__":
    for p in sys.argv[1:]:
        main(p)
