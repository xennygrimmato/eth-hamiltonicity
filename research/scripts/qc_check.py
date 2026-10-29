"""Checks for research/quantum-circuits.md (exact amplitudes of Clifford+T circuits through the
integer networks of [A] and the truncated-ring tensor networks of [O]).  Exact arithmetic only.

Run: python3 -I qc_check.py [seed] [instances]

Q1  circuit -> gate tensors on segments (1q runs merged): value / sqrt2^k = <y|C|x> (state vector, exact Z[w])
Q2  Definition-2 integer network (Kronecker x = 2^b, b = ceil(k/2)+2): brute force over crossing bits
    = literal Definition 2 sum (small cases) = variable elimination; decode mod 2^{4b}+1 -> amplitude
Q3  full Kronecker decode (no reduction, deg <= 3g) gives the same amplitude
Q4  Definition-2 parameters: P_a <= P = 4 ceil(G/g)+1 (condition (i)), U = 2 #cross <= 4G, |W_a| < 2^B
Q5  [O]-ring emulation: contraction in (Z/2^{P0})[V]/(V^l), P0 = ceil(k/2)+3, l = 3G+1, then mod V^4+1
Q6  Galois bound |a_j| <= 2^{k/2} (all four embeddings unitary) on every instance
Q7  doubled network: marginals sum_{y_Sbar} |<y|C|x>|^2 (numerator in Z[sqrt2], denominator 2^k), via
    the integer network (b = k+2) and via VE; S = all qubits gives 1 exactly
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qc_lib import *  # noqa: E402

FAILS = 0


def check(cond, msg):
    global FAILS
    if not cond:
        FAILS += 1
        print("  FAIL:", msg)


def _bnd_sizes(net, groups, g):
    endp = {}
    for gi, (legs, _) in enumerate(net.gates):
        for l in legs:
            if not isinstance(l, tuple):
                endp.setdefault(l, set()).add(groups[gi])
    return [[v for v, s in endp.items() if a in s and len(s) == 2] for a in range(g)]


def amp_sv(ops, n, x, y):
    vec, k = statevector(ops, n, x)
    return vec[sum(y[q] << (n - 1 - q) for q in range(n))], k


def run(seed, count):
    rng = random.Random(seed)
    stats = dict(inst=0, brute=0, lit=0, oai_brute=0, maxG=0, maxcross=0, marg=0)
    for t in range(count):
        n = rng.randint(2, 6)
        G = rng.randint(1, 20)
        G1 = rng.randint(0, 25)
        ops = random_circuit(rng, n, G, G1)
        x = [rng.randrange(2) for _ in range(n)]
        y = [rng.randrange(2) for _ in range(n)]
        A_sv, k_sv = amp_sv(ops, n, x, y)
        net = circuit_to_net(ops, n, x, y)
        stats['inst'] += 1; stats['maxG'] = max(stats['maxG'], G)
        # Q1
        val = zmul(net.scalar, ve_value(gate_factors(net, lambda a: a), net.nvars, **ZR))
        check(net.k == k_sv == circuit_k(ops), f"k mismatch {net.k} {k_sv}")
        check(val == A_sv, f"Q1 VE {val} != sv {A_sv}")
        if net.nvars <= 14:
            vb = zmul(net.scalar, brute_value(net, conv=lambda a: a, **ZR))
            check(vb == A_sv, "Q1 brute")
        # Q6 Galois bound (numerator of the whole amplitude)
        check(all(abs(c) <= 2 ** (k_sv / 2) for c in A_sv), f"Q6 Galois bound {A_sv} k={k_sv}")
        for tt in (1, 3, 5, 7):
            s = zsigma(A_sv, tt)
            # |sigma(A)|^2 = s * conj(s) must be <= 2^k: test via the real part in Z[sqrt2]: compute exactly
            nn = zmul(s, zconj(s))      # = r0 + r1 sqrt2 with r1 = nn[1] (nn real: nn[2]=0, nn[3]=-nn[1])
            check(nn[2] == 0 and nn[3] == -nn[1], "Q6 norm not real")
            r0, r1 = nn[0], nn[1]       # value r0 + r1*sqrt2 <= 2^k  <=>  check exactly
            lhs = (1 << k_sv) - r0      # need r1*sqrt2 <= lhs
            ok = (r1 <= 0 and (lhs >= 0 or 2 * r1 * r1 >= lhs * lhs)) or (r1 > 0 and lhs >= 0 and 2 * r1 * r1 <= lhs * lhs)
            check(ok, f"Q6 |sigma_{tt}(A)|^2 > 2^k")
        # Q2-Q4: integer network with g groups (the untouched-qubit scalar is applied after decoding)
        k_net = net.k
        bdec = -(-k_net // 2) + 2
        for g in (1, 2, 3, 4):
            groups = random_groups(rng, len(net.gates), g, contiguous=(rng.random() < 0.5))
            if max(len(v) for v in _bnd_sizes(net, groups, g)) > 14:
                stats['skipped'] = stats.get('skipped', 0) + 1
                continue
            IN = IntNetwork(net, groups, g, bdec)
            stats['maxcross'] = max(stats['maxcross'], len(IN.cross))
            Zve = IN.value_ve()
            if len(IN.cross) <= 16:
                Zb = IN.value_brute(); stats['brute'] += 1
                check(Zb == Zve, f"Q2 brute {Zb} != VE {Zve}")
            if sum(len(IN.bnd[a]) for a in range(g)) <= 14:
                Zl = IN.value_def2_literal(); stats['lit'] += 1
                check(Zl == Zve, "Q2 literal Def 2")
            A_net = zmul(net.scalar, decode_mod(Zve, bdec))
            check(A_net == A_sv, f"Q2 decode_mod {A_net} != {A_sv} (g={g})")
            # Q3 full decode with a b large enough for the unreduced polynomial
            l1 = 1
            for a in range(g):
                l1 *= IN.l1[a] * (2 ** 0)
            bfull = (l1 * 2 ** len(IN.cross)).bit_length() + 2
            IN2 = IntNetwork(net, groups, g, bfull)
            A_full = zmul(net.scalar, decode_full(IN2.value_ve(), bfull, 3 * g))
            check(A_full == A_sv, f"Q3 full decode (g={g})")
            # Q4 parameters
            P, Pa = IN.params()
            check(all(Pa[a] <= P for a in range(g)), "Q4 (i)")
            check(IN.U == sum(Pa.values()) and IN.U <= 4 * len(net.gates), "Q4 U")
            for a in range(g):
                Bbits = (IN.l1[a]).bit_length() + 3 * bdec + 2
                check(all(abs(v) < 2 ** Bbits for v in IN.tables[a].values()), "Q4 B")
        # Q5 OpenAI ring
        Gv = len(net.gates)
        P0 = -(-k_net // 2) + 3
        ell = 3 * max(Gv, 1) + 1
        ring, conv, mod = make_trunc_ring(P0, ell)
        Vval = ve_value(gate_factors(net, conv), net.nvars, **ring)
        A_oai = zmul(net.scalar, reduce_x4p1_mod(Vval, mod))
        # the scalar (untouched qubits) can carry extra sqrt2 powers; compare numerators mod 2^P0 after lifting
        check(all((u - v) % mod == 0 for u, v in zip(A_oai, A_sv)), "Q5 OpenAI ring (mod)")
        check(reduce_x4p1_mod(Vval, mod) == zmul(ONE, ve_value(gate_factors(net, lambda a: a), net.nvars, **ZR)),
              "Q5 OpenAI ring exact lift")
        if net.nvars <= 12:
            Vb = brute_value(net, conv=conv, **ring); stats['oai_brute'] += 1
            check(Vb == Vval, "Q5 brute vs VE in ring")
        # Q7 marginals
        if n <= 5 and G <= 14:
            S = sorted(rng.sample(range(n), rng.randint(0, n)))
            yS = {q: y[q] for q in S}
            dn = circuit_to_net_free(ops, n, x, yS)
            num = zmul(dn.scalar, ve_value(gate_factors(dn, lambda a: a), dn.nvars, **ZR))
            vec, k1 = statevector(ops, n, x)
            ref = ZERO
            for idx, a in enumerate(vec):
                if all(((idx >> (n - 1 - q)) & 1) == yS[q] for q in S):
                    ref = zadd(ref, zmul(a, zconj(a)))
            check(dn.k == 2 * k1, "Q7 k")
            check(num == ref, f"Q7 marginal VE {num} != {ref}")
            check(num[2] == 0 and num[3] == -num[1], "Q7 not in Z[sqrt2]")
            if not S:
                check(num == (1 << (dn.k // 2), 0, 0, 0), "Q7 normalisation (value / sqrt2^k = 1)")
            # integer network on the doubled net, b = k+2
            bb = dn.k + 2
            for g in (2, 3):
                groups = random_groups(rng, len(dn.gates), g, contiguous=True)
                if max(len(v) for v in _bnd_sizes(dn, groups, g)) > 14:
                    continue
                IN = IntNetwork(dn, groups, g, bb)
                Zv = IN.value_ve()
                if len(IN.cross) <= 16:
                    check(IN.value_brute() == Zv, "Q7 brute")
                check(zmul(dn.scalar, decode_mod(Zv, bb)) == ref, "Q7 integer network decode")
                check(IN.U <= 2 * (2 * len(dn.gates)), "Q7 U")
            stats['marg'] += 1
    return stats


def ccz_check(seed, count):
    """IQP link (Dalzell et al.): <0|H^n D_f H^n|0> = gap(f)/2^n, with CCZ compiled to CNOT+T/Tdg
    (7 T gates, 6 CNOTs, 2 H), through the integer network."""
    rng = random.Random(seed)
    for _ in range(count):
        n = rng.randint(3, 5)
        terms = set()
        m = rng.randint(1, 6)
        while len(terms) < m:
            d = rng.choice([1, 2, 3])
            terms.add(tuple(sorted(rng.sample(range(n), d))))
        ops = [('1', 'H', (q,)) for q in range(n)]
        for tm in sorted(terms):
            if len(tm) == 1:
                ops.append(('1', 'Z', tm))
            elif len(tm) == 2:
                ops.append(('2', 'CZ', tm))
            else:
                a, b, c = tm
                ops += ccz_ops(a, b, c)
        ops += [('1', 'H', (q,)) for q in range(n)]
        gap = 0
        for xx in range(1 << n):
            bits = [(xx >> q) & 1 for q in range(n)]
            f = sum(all(bits[i] for i in tm) for tm in terms) % 2
            gap += -1 if f else 1
        x = [0] * n
        net = circuit_to_net(ops, n, x, x)
        A = zmul(net.scalar, ve_value(gate_factors(net, lambda a: a), net.nvars, **ZR))
        # A / sqrt2^k = gap / 2^n  <=>  A * 2^n = gap * sqrt2^k
        check(tuple(c * (1 << n) for c in A) == zmul((gap, 0, 0, 0), zpow_sqrt2(net.k)), f"CCZ/IQP gap {gap}")


def ccz_ops(a, b, c):
    # standard CCZ = (I(x)I(x)H) Toffoli (I(x)I(x)H); Toffoli 7-T decomposition (Nielsen-Chuang Fig. 4.9)
    H = lambda q: ('1', 'H', (q,))
    T = lambda q: ('1', 'T', (q,))
    Td = lambda q: ('1', 'Tdg', (q,))
    CX = lambda p, q: ('2', 'CNOT', (p, q))
    tof = [H(c), CX(b, c), Td(c), CX(a, c), T(c), CX(b, c), Td(c), CX(a, c), T(b), T(c), H(c),
           CX(a, b), T(a), Td(b), CX(a, b)]
    return [H(c)] + tof + [H(c)]


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    st = run(seed, count)
    ccz_check(seed, 20)
    print("stats:", st)
    print("PASS" if FAILS == 0 else f"FAIL ({FAILS} failures)")


def ablations(seed):
    """Negative controls: each deliberately broken variant must be caught on some instance."""
    rng = random.Random(seed + 1000)
    caught = {'b_too_small': False, 'ell_too_small': False, 'no_conj': False, 'P0_too_small': False}
    for _ in range(40):
        n = rng.randint(3, 5); G = rng.randint(8, 16)
        ops = random_circuit(rng, n, G, rng.randint(10, 25))
        x = [rng.randrange(2) for _ in range(n)]; y = [rng.randrange(2) for _ in range(n)]
        A_sv, k = amp_sv(ops, n, x, y)
        net = circuit_to_net(ops, n, x, y)
        groups = random_groups(rng, len(net.gates), 2, contiguous=True)
        if max(len(v) for v in _bnd_sizes(net, groups, 2)) > 14:
            continue
        bsmall = max(2, (max(abs(c) for c in A_sv) + 1).bit_length() - 1)
        IN = IntNetwork(net, groups, 2, bsmall)
        try:
            caught['b_too_small'] |= zmul(net.scalar, decode_mod(IN.value_ve(), bsmall)) != A_sv
        except AssertionError:
            caught['b_too_small'] = True
        ring, conv, mod = make_trunc_ring(-(-net.k // 2) + 3, 4)
        caught['ell_too_small'] |= reduce_x4p1_mod(ve_value(gate_factors(net, conv), net.nvars, **ring), mod) != \
            ve_value(gate_factors(net, lambda a: a), net.nvars, **ZR)
        P0s = max(1, (max(abs(c) for c in A_sv)).bit_length())  # one bit short of the signed range
        ring, conv, mod = make_trunc_ring(P0s, 3 * len(net.gates) + 1)
        caught['P0_too_small'] |= reduce_x4p1_mod(ve_value(gate_factors(net, conv), net.nvars, **ring), mod) != \
            ve_value(gate_factors(net, lambda a: a), net.nvars, **ZR)
        dn = circuit_to_net_free(ops, n, x, {})
        dn.gates = [(legs, {kk: (zconj(v) if gi >= len(dn.gates) // 2 else v) for kk, v in tab.items()})
                    for gi, (legs, tab) in enumerate(dn.gates)]   # undo the conjugation of the second copy
        num = zmul(dn.scalar, ve_value(gate_factors(dn, lambda a: a), dn.nvars, **ZR))
        caught["no_conj"] |= num != (1 << (dn.k // 2), 0, 0, 0)
    return caught


if __name__ == "__main__":
    ab = ablations(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    print("ablations caught:", ab)
    check(all(ab.values()), "an ablation was not detected")
    print("PASS (with ablations)" if FAILS == 0 else f"FAIL ({FAILS} failures)")
