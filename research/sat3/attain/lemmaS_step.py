#!/usr/bin/env python3
"""Stepwise form of Lemma S in the Banach relaxation of a product of pods and lines:
parent W with Aux hubs; cross two of its wires (bits p, q); is there theta with both children >= v(parent)?
gap = 1 - (r_c^2 + r_b^2) / (2(p^2+q^2)),  r_c (r_b) = least bond with child_c (child_b) >= v(parent).
Parents: random 'caterpillars': hubs h1, h2 (optionally identified, optionally joined by a wire), each
attached to 1-3 legs (finite, far, or at the branch point) with random bits; crossed wires: (h1, c), (h2, d)
with c, d legs or a third hub.  Usage: lemmaS_step.py BLOCKS seed n"""
import sys, json, math
import numpy as np
import cvxpy as cp
from lemmaS import Space, System, far, fin, depth1_threshold, random_far_wire, random_fin_wire


def rand_leg(space, rng, name):
    kind = rng.choice(['far', 'fin', 'branch'], p=[0.0, 0.7, 0.3])
    if kind == 'far':
        w = rng.normal(size=len(space.blocks)); w /= np.linalg.norm(w)
        arms = [int(rng.integers(m)) for m in space.blocks]
        wts = [float(w[b]) if m == 1 else float(abs(w[b])) for b, m in enumerate(space.blocks)]
        return far(space, arms, wts)
    pos = np.zeros(space.D)
    for b, m in enumerate(space.blocks):
        if m == 1:
            pos[space.off[b]] = rng.normal()
        elif kind == 'fin' and rng.random() > 0.2:
            pos[space.off[b] + rng.integers(m)] = abs(rng.normal())
    return fin(space, pos)


def parent(space, rng):
    parties, wires = {}, []
    same = rng.random() < 0.3
    hubs = ['h1', 'h1' if same else 'h2']
    parties['h1'] = ('aux',)
    if not same: parties['h2'] = ('aux',)
    p, q = [round(float(x), 3) for x in rng.uniform(0.2, 1.0, size=2)]
    if rng.random() < 0.3: p = q = 1.0
    third = rng.random() < 0.3
    if third:
        parties['h3'] = ('aux',)
        for t in range(int(rng.integers(2, 4))):
            parties[f'm{t}'] = rand_leg(space, rng, f'm{t}')
            wires.append(['h3', f'm{t}', round(float(rng.uniform(0.2, 1.5)), 3)])
    ends = []
    for nm in ('c', 'd'):
        if third and rng.random() < 0.5:
            ends.append('h3')
        else:
            parties[nm] = rand_leg(space, rng, nm); ends.append(nm)
    wires = [[hubs[0], ends[0], p], [hubs[1], ends[1], q]] + wires
    for hi, h in enumerate(sorted(set(hubs))):
        for t in range(int(rng.integers(1, 4))):
            nm = f'l{hi}{t}'
            parties[nm] = rand_leg(space, rng, nm)
            wires.append([h, nm, round(float(rng.uniform(0.2, 1.5)), 3)])
    if not same and rng.random() < 0.4:
        wires.append(['h1', 'h2', round(float(rng.uniform(0.2, 1.5)), 3)])
    return System(space, parties, wires), p, q


if __name__ == '__main__':
    blocks = [int(x) for x in sys.argv[1].split(',')]
    seed, n = int(sys.argv[2]), int(sys.argv[3])
    space = Space(blocks); rng = np.random.default_rng(seed)
    worst = (1e9, None); done = 0
    while done < n:
        S0, p, q = parent(space, rng)
        try:
            v = S0.value()
        except Exception:
            continue
        if not np.isfinite(v) or abs(v) > 1e6:
            continue          # unbounded parent (far legs not balanced): skip
        try:
            rc = depth1_threshold(S0, 0, 1, 'c', v - 1e-6 * (1 + abs(v)), p, q)
            rb = depth1_threshold(S0, 0, 1, 'b', v - 1e-6 * (1 + abs(v)), p, q)
        except Exception as e:
            continue
        if rc is None or rb is None:
            continue
        done += 1
        gap = 1 - (rc * rc + rb * rb) / (2 * (p * p + q * q))
        rec = dict(blocks=blocks, seed=seed, it=done, p=p, q=q, v=v, rc=rc, rb=rb, gap=gap,
                   wires=S0.wires, parties={k: [x if not isinstance(x, tuple) else list(map(float, x)) for x in val] for k, val in S0.parties.items()})
        print(json.dumps(rec), flush=True)
        if gap < worst[0]: worst = (gap, rec)
    print('WORST', json.dumps(worst[1]), flush=True)
