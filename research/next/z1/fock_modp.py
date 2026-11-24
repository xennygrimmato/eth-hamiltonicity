"""Route 4: ranks of App. B Fock pieces A_s (scripts/pieces_fock_ranks.py, unchanged) modulo small primes versus
the large prime 2^61-1 (= Q-rank with overwhelming probability).  Identity: sum_s A_s = h! [x=v][y=u], so for q <= h
the identity vanishes mod q.  Reports the worst piece's (c_row + c_col)/(4 lambda) per modulus."""
import sys, math
sys.path.insert(0, '/home/user/eth-hamiltonicity/research/scripts')
import pieces_fock_ranks as M
primes = [(1 << 61) - 1, 2, 3, 5, 7, 11, 13]
for h in [int(a) for a in sys.argv[1:]]:
    rows = {}
    for q in primes:
        M.P = q
        N, ok, res = M.run(h)
        rows[q] = {s: (rr, rc) for s, rr, rc, _, _ in res}
    lam = math.log2(N)
    print(f'h={h} N={N} identity_ok={ok} h!={math.factorial(h)}')
    for q in primes:
        worst = 0; diff = 0
        for s, (rr, rc) in rows[q].items():
            c = (math.log2(rr) if rr else 0) + (math.log2(rc) if rc else 0); worst = max(worst, c)
            if (rr, rc) != rows[primes[0]][s]: diff += 1
        tag = 'Q' if q == primes[0] else f'GF({q})' + (' [d=h! = 0 here]' if q <= h else '')
        print(f'  {tag:22s} worst (c_row+c_col)/(4 lam) = {worst/(4*lam):.4f}   pieces with rank profile != Q: {diff}/{len(rows[q])}')
    for s in sorted(rows[primes[0]]):
        print('   s=%3d ' % s + ' '.join(f'{rows[q][s]}' for q in primes))
    sys.stdout.flush()
