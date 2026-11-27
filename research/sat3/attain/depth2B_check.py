#!/usr/bin/env python3
"""Independent re-evaluation of single type-B strategies (no code shared with depth2B_core except none):
leaf cost by brute force over all g^6 placements of the six hubs (numpy, vectorised), level-1 stop cost from
game1.consts, th3 on a 4001-point grid, (th1, th2) on a grid plus the reported argmax.
Usage: depth2B_check.py GROUP w0,w1,w2 mode  a1 c1 b1 d1 a2 c2 b2 d2 t1 t2 u th1 th2   (node indices; e = (a,c))"""
import sys, math, itertools
import numpy as np
from game1 import net, consts


def main():
    name, w, mode = sys.argv[1], np.array([float(x) for x in sys.argv[2].split(',')]), sys.argv[3]
    a1, c1, b1, d1, a2, c2, b2, d2 = [int(x) for x in sys.argv[4:12]]
    t1, t2, u, th1s, th2s = [float(x) for x in sys.argv[12:17]]
    g, nodes, lab = net(name)
    p1, q1, p2, q2 = t1, 1 - t1, u * t2, u * (1 - t2)
    P = np.array(list(itertools.product(range(g), repeat=6)))  # o1, o1', o2, o2', U, U'
    T3 = np.linspace(0, math.pi / 2, 4001)

    def stop(legs, p, q, th):
        R = math.sqrt(2 * (p * p + q * q)); r = min(R * math.cos(th), p + q); rp = min(R * math.sin(th), p + q)
        tot = 0
        for k in range(3):
            S, Ac, Ab, A3 = consts(*[lab[x, k] for x in legs], p, q)
            tot += w[k] * min(S, A3 + 2 * min(p, q), Ac + r, Ab + rp)
        return tot

    def hubs(cut, a, b, c, d, p, q):
        return ([(a, p), (b, q)], [(c, p), (d, q)]) if cut == 0 else ([(a, p), (d, q)], [(b, q), (c, p)])

    def nest(cut1, cut2, r1, r2):
        O1, O1p = hubs(cut1, a1, b1, c1, d1, p1, q1)
        O2, O2p = hubs(cut2, a2, b2, c2, d2, p2, q2)
        R3 = math.sqrt(2 * (r1 * r1 + r2 * r2)); cap = r1 + r2
        rho = np.minimum(R3 * np.cos(T3), cap); rhop = np.minimum(R3 * np.sin(T3), cap)
        tot = np.zeros(len(T3))
        for k in range(3):
            def mv(hub, col):
                return sum(b * (lab[x, k] != P[:, col]) for (x, b) in hub)
            base = mv(O1, 0) + mv(O1p, 1) + mv(O2, 2) + mv(O2p, 3) + r1 * (P[:, 0] != P[:, 4]) + r1 * (P[:, 1] != P[:, 5])
            sep = P[:, 4] != P[:, 5]
            bc = base + r2 * (P[:, 2] != P[:, 4]) + r2 * (P[:, 3] != P[:, 5])   # cut c'
            bb = base + r2 * (P[:, 3] != P[:, 4]) + r2 * (P[:, 2] != P[:, 5])   # cut b'
            M = min(bc[~sep].min(), bb[~sep].min())
            ck = np.minimum(M, np.minimum(bc[sep].min() + rho, bb[sep].min() + rhop))
            tot += w[k] * ck
        return tot.max()

    def F(th1, th2):
        R1 = math.sqrt(2 * (p1 * p1 + q1 * q1)); R2 = math.sqrt(2 * (p2 * p2 + q2 * q2))
        r1s = (min(R1 * math.cos(th1), p1 + q1), min(R1 * math.sin(th1), p1 + q1))
        r2s = (min(R2 * math.cos(th2), p2 + q2), min(R2 * math.sin(th2), p2 + q2))
        opts = [stop((a1, b1, c1, d1), p1, q1, th1) + stop((a2, b2, c2, d2), p2, q2, th2)]
        for x in range(2):
            for y in range(2):
                opts.append(nest(x, y, r1s[x], r2s[y]))
        return min(opts), opts

    v, opts = F(th1s, th2s)
    print(f"at reported argmax ({th1s}, {th2s}): F = {v:.7f}; options (stop, cc, cb, bc, bb) = {np.round(opts, 6).tolist()}")
    best = v
    for th1 in np.linspace(th1s - 0.002, th1s + 0.002, 21):
        for th2 in np.linspace(th2s - 0.002, th2s + 0.002, 21):
            best = max(best, F(th1, th2)[0])
    print(f"max over an 21x21 neighbourhood grid (+-0.002): {best:.7f}")
    gl = max(F(a, b)[0] for a in np.linspace(0, math.pi / 2, 13) for b in np.linspace(0, math.pi / 2, 13))
    print(f"max over a global 13x13 grid: {gl:.7f}")


if __name__ == '__main__':
    main()
