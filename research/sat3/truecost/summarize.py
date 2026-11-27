#!/usr/bin/env python3
"""Compact summary of the tables out/r_*.txt (seven exact flattening ranks of every Psi_N)."""
import sys, re, glob
def pn(m):
    q = [1] + [0] * m
    for k in range(1, m + 1):
        for j in range(k, m + 1): q[j] += q[j - k]
    return q
P = pn(200)
stable = lambda k: sum((k - j + 1) * P[j] for j in range(k + 1))
for fn in sorted(glob.glob('out/r_*.txt')):
    L = open(fn).read().splitlines()
    hd = [l for l in L if l.startswith('classes')]
    if not hd: continue
    n1, e1, n2, e2 = map(int, re.match(r'classes \((\d+),(\d+)\) d1=\d+, \((\d+),(\d+)\)', hd[0]).groups())
    d1, d2 = map(int, re.findall(r'd[12]=(\d+)', hd[0])); Th = 2 * (e1 + e2)
    rows = {}
    for l in L:
        m = re.match(r'\s*(\d+) \|\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+) \|', l)
        if m:
            v = list(map(int, m.groups())); rows[v[0]] = v[1:]
    Ns = sorted(rows)
    if not Ns: continue
    seq = [rows[N][5] if N in rows else 0 for N in range(0, Th // 2 + 1, 2)]
    full = d1 * d2
    upto = next((i for i, v in enumerate(seq) if v == full), len(seq))
    k0 = next((k for k, v in enumerate(seq) if v != stable(k)), None)
    singles_full = [N for N in Ns if rows[N][0] == d1 and rows[N][1] == d2 and rows[N][2] == d1 and rows[N][3] == d2]
    third = sorted(set(rows[N][6] for N in Ns))
    mono = all(seq[i] <= seq[i + 1] for i in range(len(seq) - 1))
    sym = all(rows[N][5] == rows[Th - N][4] for N in Ns if Th - N in rows)
    print(f"({n1},{e1})x({n2},{e2}): d1={d1} d2={d2} Theta={Th} identity={any("identity (a): True" in l for l in L)}")
    print(f"   rank ad|bc, N=0,2,..: {seq[:upto+1]}  (full {full} first at N={2*upto})")
    print(f"   agrees with sum_j (k-j+1)p(j) for k < {k0};  monotone up to Theta/2: {mono};  rank_ab|cd(N) = rank_ad|bc(Theta-N): {sym}")
    print(f"   single-party ranks full for N in [{min(singles_full)}, {max(singles_full)}] (all N there: {len(singles_full) == (max(singles_full)-min(singles_full))//2+1});  nonzero N: [{Ns[0]}, {Ns[-1]}]")
    print(f"   third cut ac|bd: max {max(third)} (min(d1^2,d2^2) = {min(d1*d1,d2*d2)}), at N=Theta/2: {rows[Th//2][6] if Th//2 in rows else '-'}; values {third[:8]}{'...' if len(third)>8 else ''}")
