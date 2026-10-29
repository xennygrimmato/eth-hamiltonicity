#!/usr/bin/env python3
"""dense_pipeline.py -- end-to-end check of the algorithm of Theorem 1 with numeric evaluations only.

For each (R, T): evaluate the network quantity Q_{R,T}(w, x, t) (here by its path form; dense_locality.py checks
that it equals the local Grassmann/label network) at the points of a tensor grid, with x_{min R} := 1 (the
x-exponents of every monomial sum to 0) and the Laurent variables x_a shifted by x_a^n; recover all coefficients
by exact tensor-product Lagrange interpolation; extract [w^d x^0 t_T^1] and weight by prod (d_a - 1)!.
Compares with brute force and prints the exact number of evaluations
    E = sum_{(R,T)} (n+1)^{|R|} (2n+1)^{|R|-1} (n+1)^{|R|-1}.
"""
import itertools, random, sys
from fractions import Fraction as Fr
from math import factorial
sys.path.insert(0, __import__('os').path.dirname(__file__))
from dense_lib import *
from dense_lowrank_hc import rand_inst


def interp1(xs, ys):
    n = len(xs); co = [Fr(0)] * n
    for i in range(n):
        num = [Fr(1)]; den = Fr(1)
        for j in range(n):
            if j == i: continue
            num = [Fr(0)] + num
            for k in range(len(num) - 1): num[k] -= xs[j] * num[k + 1]
            den *= xs[i] - xs[j]
        for k in range(n): co[k] += ys[i] * num[k] / den
    return co


def tensor_interp(grid_vals, axes):
    """grid_vals: dict point-index-tuple -> value; axes: list of point lists. returns dict exponent tuple -> coeff."""
    vals = dict(grid_vals)
    for ax, pts in enumerate(axes):
        new = {}
        others = {k[:ax] + k[ax + 1:] for k in vals}
        for o in others:
            ys = [vals[o[:ax] + (i,) + o[ax:]] for i in range(len(pts))]
            co = interp1(pts, ys)
            for e, c in enumerate(co):
                new[o[:ax] + (e,) + o[ax:]] = c
        vals = new
    return vals


def run(seed, n, r, m):
    rng = random.Random(seed)
    U, V, L, D = rand_inst(rng, n, r, m)
    A = [[L[i][j] + D[i][j] for j in range(n)] for i in range(n)]
    truth = hc_dir_brute(A)
    Fs, base = [], 0
    for F in dir_subsets(arcs_of(D), n):
        if is_ham_dicycle(F, n): base += wprod(D, F); continue
        us = units(F, n)
        if us is not None: Fs.append((wprod(D, F), us))
    total, evals = Fr(base), 0
    for s in range(1, r + 1):
        for R in itertools.combinations(range(r), s):
            for par in in_arborescences(list(R)):
                T = sorted(par.items())
                xvars = list(R[1:])
                axes = [[Fr(k) for k in range(1, n + 2)] for _ in R] + \
                       [[Fr(k) for k in range(1, 2 * n + 2)] for _ in xvars] + \
                       [[Fr(k) for k in range(1, n + 2)] for _ in T]
                gv = {}
                for idx in itertools.product(*[range(len(a)) for a in axes]):
                    pt = [axes[k][i] for k, i in enumerate(idx)]
                    w = dict(zip(R, pt[:s])); x = {R[0]: Fr(1)}; x.update(zip(xvars, pt[s:s + len(xvars)]))
                    t = pt[s + len(xvars):]
                    def ell(u, v):
                        a_ = sum(V[u][a] * w[a] * x[a] for a in R); b_ = sum(U[v][b] / x[b] for b in R)
                        val = a_ * b_
                        for k, (a, b) in enumerate(T): val += t[k] * V[u][a] * w[a] * x[a] * U[v][b] / x[b]
                        return val
                    Q = Fr(0)
                    for (dF, us) in Fs:
                        p = Fr(dF)
                        for (u, v) in us: p *= ell(u, v)
                        Q += p
                    sh = Fr(1)
                    for a in xvars: sh *= x[a] ** n
                    gv[idx] = Q * sh
                    evals += 1
                co = tensor_interp(gv, axes)
                for e, c in co.items():
                    if c == 0: continue
                    d = e[:s]; xe = e[s:s + len(xvars)]; te = e[s + len(xvars):]
                    if any(v != n for v in xe) or any(v != 1 for v in te): continue
                    pr = 1
                    for da in d:
                        if da < 1: pr = 0; break
                        pr *= factorial(da - 1)
                    total += c * pr
    ok = total == truth
    print(f"seed={seed} n={n} r={r} m={m}: brute={truth} pipeline={total} evaluations={evals}  {'PASS' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    ok = True
    for seed, n, r, m in [(3, 4, 2, 4), (4, 5, 2, 5), (5, 5, 2, 6), (8, 4, 1, 5), (9, 6, 1, 7)]:
        ok &= run(seed, n, r, m)
    print("ALL PASS" if ok else "SOME FAIL")
