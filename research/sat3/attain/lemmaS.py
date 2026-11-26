#!/usr/bin/env python3
"""Test of the nested (depth-2) crossing game in products of pods and lines  (attain-notes.md, section 5).

Space X = product of pods (l2 product).  A pod with m arms is embedded in (R^m, l1); we work in the Banach
relaxation E = l2-sum of the blocks (R^m, l1) (a line is a block of size 1), where Steiner points may sit
anywhere.  v_E <= v_X, so "the adversary wins in E" implies "the adversary wins in X"; a loss in E is only a
CANDIDATE violation and must be confirmed in X by explicit positions (routine confirm()).

Wire system: wires (u, v, bits) between parties; parties are far legs (a direction xi: per pod block an arm
and a weight, per line block a signed weight; sum of squared weights 1), finite legs (a point) or Aux hubs.
Steiner value v(W) = min over Aux positions of sum bits*distance, by conic duality
    v(W) = max sum_w <F_w, const_w>,  ||F_w||_* <= bits_w,  equilibrium at Aux parties,
with ||F||_* = l2 norm of the blocks' sup norms; a far leg forces F onto a face of the dual ball.

Game (cover moves first at each step, adversary answers with theta, cover picks the cut):
  step 1: cross wires 1, 2 (bits p, q) -> bonds (r, r') on the circle r^2 + r'^2 = 2(p^2+q^2);
  step 2 (cover's option): stop, or cross any two wires of the resulting system -> (rho, rho') on the circle of
          THEIR bits; cover picks the cut.
The adversary wins if some leaf has Steiner value >= T = sum bits*|wire| (0 for far wires through the origin).
For cut c (resp. b) at step 1 let R_c (R_b) be the least bond for which the adversary wins against every
step-2 option.  Adversary wins the game iff R_c^2 + R_b^2 <= 2(p^2+q^2).  We report
    margin = 1 - (R_c^2 + R_b^2) / (2(p^2+q^2))        (negative = candidate violation of weak duality).
In Hilbert space the margin is exactly 0 for wires through one point (parallelogram law).
"""
import sys, math, itertools, json
import numpy as np
import cvxpy as cp

SOLVER = cp.CLARABEL


class Space:
    def __init__(self, blocks):
        self.blocks = blocks                      # list of block sizes (1 = line)
        self.off = np.cumsum([0] + blocks)
        self.D = int(self.off[-1])

    def dual_norm(self, F):
        return cp.norm(cp.hstack([cp.norm(F[self.off[b]:self.off[b + 1]], 'inf') for b in range(len(self.blocks))]), 2)

    def dist(self, P, Q):  # numpy, primal norm
        d = P - Q
        return math.sqrt(sum(np.abs(d[self.off[b]:self.off[b + 1]]).sum() ** 2 for b in range(len(self.blocks))))


def far(space, arms, weights):
    """far leg: arms[b] = arm index (ignored for lines), weights[b] >= 0 for pods, signed for lines."""
    return ('far', tuple(arms), tuple(weights))


def fin(space, pos):
    return ('fin', tuple(pos))


class System:
    """wires: list of [u, v, cap]; cap float or string key into caps dict (cvxpy expr)."""
    def __init__(self, space, parties, wires, const=0.0):
        self.space, self.parties, self.wires, self.const = space, dict(parties), [list(w) for w in wires], const
        self.naux = sum(1 for p in parties.values() if p[0] == 'aux')

    def copy(self):
        return System(self.space, self.parties, self.wires, self.const)

    def cross(self, i, j, cut, bond, tag):
        """replace wires i, j by the two-hub network of the given cut with bond capacity `bond`."""
        S = self.copy()
        (u1, v1, b1), (u2, v2, b2) = S.wires[i], S.wires[j]
        o, o2 = 'o' + tag, 'o' + tag + "'"
        S.parties[o] = ('aux',); S.parties[o2] = ('aux',)
        # a leg-leg wire that is removed carried a constant length; far-far wires are normalised to 0
        S.wires = [w for k, w in enumerate(S.wires) if k not in (i, j)]
        if cut == 'c':
            S.wires += [[u1, o, b1], [u2, o, b2], [v1, o2, b1], [v2, o2, b2], [o, o2, bond]]
        else:
            S.wires += [[u1, o, b1], [v2, o, b2], [u2, o2, b2], [v1, o2, b1], [o, o2, bond]]
        return S

    def _wire_const(self, k):
        u, v, b = self.wires[k]
        pu, pv = self.parties[u], self.parties[v]
        if pu[0] == 'fin' and pv[0] == 'fin':
            return b * self.space.dist(np.array(pu[1]), np.array(pv[1]))
        return 0.0

    def dual(self, caps):
        """returns (objective expr, constraints) of the dual (flow) problem; caps: dict name -> cvxpy expr."""
        sp = self.space
        cons, obj = [], 0.0
        bal = {n: 0 for n, p in self.parties.items() if p[0] == 'aux'}
        for (u, v, b) in self.wires:
            cap = caps[b] if isinstance(b, str) else b
            pu, pv = self.parties[u], self.parties[v]
            if pu[0] != 'aux' and pv[0] != 'aux':
                if pu[0] == 'fin' and pv[0] == 'fin':
                    obj = obj + cap * sp.dist(np.array(pu[1]), np.array(pv[1]))
                elif pu[0] == 'far' and pv[0] == 'far':
                    pass     # normalised: a far-far wire is a line through the origin, constant 0
                else:
                    raise ValueError('mixed far/finite wire')
                continue
            F = cp.Variable(sp.D)
            # orient so that the aux end is "u":  term cap*|P_u - P_v| = max <F, P_u - P_v>
            if pu[0] != 'aux':
                u, v, pu, pv = v, u, pv, pu
            bal[u] = bal[u] + F
            if pv[0] == 'aux':
                bal[v] = bal[v] - F
                cons.append(sp.dual_norm(F) <= cap)
            elif pv[0] == 'fin':
                cons.append(sp.dual_norm(F) <= cap)
                obj = obj - F @ np.array(pv[1])
            else:  # far leg: |M xi - P| - M = max over the face of <F, P>
                _, arms, wts = pv
                for bidx, m in enumerate(sp.blocks):
                    Fb = F[sp.off[bidx]:sp.off[bidx + 1]]
                    w = wts[bidx]
                    if m == 1:
                        cons.append(Fb[0] == -w * cap)
                    else:
                        i = arms[bidx]
                        cons.append(Fb[i] == -w * cap)
                        for k in range(m):
                            if k != i:
                                cons.append(cp.abs(Fb[k]) <= w * cap)
        for n, e in bal.items():
            if not isinstance(e, int):
                cons.append(e == 0)
        return obj + self.const, cons

    def value(self, caps=None):
        obj, cons = self.dual(caps or {})
        if isinstance(obj, float):
            return obj
        prob = cp.Problem(cp.Maximize(obj), cons)
        prob.solve(solver=SOLVER)
        return prob.value if prob.status in ('optimal', 'optimal_inaccurate') else -np.inf


def bits(S, k, rval):
    b = S.wires[k][2]
    return rval if isinstance(b, str) else b


def _solve(prob):
    for solver in (cp.CLARABEL, cp.SCS):
        try:
            prob.solve(solver=solver)
            if prob.status in ('optimal', 'optimal_inaccurate'):
                return prob.value
            if prob.status in ('infeasible', 'infeasible_inaccurate'):
                return None
        except Exception:
            continue
    return 'fail'


def wins_child(S1, T, rpar, rval, tol, opts=None, info=None):
    """S1: system after step 1 with bond name 'r' (cvxpy Parameter rpar set to rval).
    True iff the adversary wins against every step-2 option of the cover."""
    rpar.value = rval
    # option: stop.  slack form (always feasible): least extra bond s with v >= T
    if not hasattr(S1, '_stop'):
        s = cp.Variable(nonneg=True)
        obj, cons = S1.dual({'r': rpar + s})
        S1._stop = cp.Problem(cp.Minimize(s), cons + [obj >= T])
        S1._opt = {}
    val = _solve(S1._stop)
    if val is None or val == 'fail' or val > tol:
        if info is not None: info['fail'] = ('stop', val)
        return False
    n = len(S1.wires)
    pairs = opts if opts is not None else list(itertools.combinations(range(n), 2))
    for (i, j) in pairs:
        if (i, j) not in S1._opt:
            rho, rho2 = cp.Variable(nonneg=True), cp.Variable(nonneg=True)
            La = S1.cross(i, j, 'c', 'rho', '2'); Lb = S1.cross(i, j, 'b', 'rho', '2')
            oa, ca = La.dual({'r': rpar, 'rho': rho}); ob, cb = Lb.dual({'r': rpar, 'rho': rho2})
            S1._opt[(i, j)] = (cp.Problem(cp.Minimize(cp.sum_squares(cp.hstack([rho, rho2]))),
                                          ca + cb + [oa >= T, ob >= T]), rho, rho2)
        prob, rho, rho2 = S1._opt[(i, j)]
        val = _solve(prob)
        b1, b2 = bits(S1, i, rval), bits(S1, j, rval)
        lim = 2 * (b1 * b1 + b2 * b2)
        if val is None or val == 'fail' or val > lim * (1 + tol) + tol:
            if info is not None: info['fail'] = ((i, j), val, lim, S1.wires[i], S1.wires[j])
            return False
    return True


def threshold(S0, i, j, cut, T, p, q, tol=2e-5, opts=None, iters=18):
    rpar = cp.Parameter(nonneg=True)
    S1 = S0.cross(i, j, cut, 'r', '1')
    lo, hi = 0.0, p + q
    info = {}
    if not wins_child(S1, T, rpar, hi, tol, opts, info):
        return float('inf'), info
    for _ in range(iters):
        mid = (lo + hi) / 2
        if wins_child(S1, T, rpar, mid, tol, opts):
            hi = mid
        else:
            lo = mid
    info = {}
    wins_child(S1, T, rpar, max(lo - 1e-4, 0), tol, opts, info)
    return hi, info


def depth1_threshold(S0, i, j, cut, T, p, q):
    S1 = S0.cross(i, j, cut, 'r', '1')
    r = cp.Variable(nonneg=True)
    obj, cons = S1.dual({'r': r})
    prob = cp.Problem(cp.Minimize(r), cons + [obj >= T])
    prob.solve(solver=SOLVER)
    return prob.value


def game(S0, p, q, T, opts=None, verbose=False):
    out = {}
    for cut in 'cb':
        out['d1' + cut] = depth1_threshold(S0, 0, 1, cut, T, p, q)
        out['R' + cut], out['info' + cut] = threshold(S0, 0, 1, cut, T, p, q, opts=opts)
    circ = 2 * (p * p + q * q)
    out['margin1'] = 1 - (out['d1c'] ** 2 + out['d1b'] ** 2) / circ
    out['margin2'] = 1 - (out['Rc'] ** 2 + out['Rb'] ** 2) / circ
    return out


def random_far_wire(space, rng, bitsval, name):
    w = rng.normal(size=len(space.blocks)); w /= np.linalg.norm(w)
    armsa, armsc, wa, wc = [], [], [], []
    for b, m in enumerate(space.blocks):
        if m == 1:
            armsa.append(0); armsc.append(0); wa.append(w[b]); wc.append(-w[b])
        else:
            i, j = rng.choice(m, size=2, replace=False)
            armsa.append(int(i)); armsc.append(int(j)); wa.append(abs(w[b])); wc.append(abs(w[b]))
    return {name + '+': far(space, armsa, wa), name + '-': far(space, armsc, wc)}, [name + '+', name + '-', bitsval]


def random_fin_wire(space, rng, bitsval, name, pbranch=0.3):
    parts = {}
    for end in '+-':
        pos = np.zeros(space.D)
        for b, m in enumerate(space.blocks):
            if m == 1:
                pos[space.off[b]] = rng.normal()
            elif rng.random() > pbranch:
                pos[space.off[b] + rng.integers(m)] = abs(rng.normal())
        parts[name + end] = fin(space, pos)
    return parts, [name + '+', name + '-', bitsval]


def instance(space, rng, kind):
    parties, wires = {}, []
    bitsv = [round(float(x), 3) for x in rng.uniform(0.2, 1.0, size=3)]
    if rng.random() < 0.3:
        bitsv = [1.0, 1.0, 1.0]
    for n, b in zip('123', bitsv):
        P, w = (random_far_wire if kind == 'far' else random_fin_wire)(space, rng, b, 'w' + n)
        parties.update(P); wires.append(w)
    S0 = System(space, parties, wires)
    T = sum(S0._wire_const(k) for k in range(3))
    return S0, bitsv, T


if __name__ == '__main__':
    blocks = [int(x) for x in sys.argv[1].split(',')]
    kind = sys.argv[2]
    seed, n = int(sys.argv[3]), int(sys.argv[4])
    space = Space(blocks)
    rng = np.random.default_rng(seed)
    worst = (1e9, None)
    for it in range(n):
        S0, bitsv, T = instance(space, rng, kind)
        try:
            res = game(S0, bitsv[0], bitsv[1], T)
        except Exception as e:
            print('ERR', e, flush=True); continue
        rec = dict(blocks=blocks, kind=kind, seed=seed, it=it, bits=bitsv, T=T, parties={k: v for k, v in S0.parties.items()},
                   d1c=res['d1c'], d1b=res['d1b'], Rc=res['Rc'], Rb=res['Rb'], margin1=res['margin1'], margin2=res['margin2'],
                   infoc=str(res['infoc']), infob=str(res['infob']))
        print(json.dumps(rec), flush=True)
        if res['margin2'] < worst[0]:
            worst = (res['margin2'], rec)
    print('WORST', json.dumps(worst[1]), flush=True)
