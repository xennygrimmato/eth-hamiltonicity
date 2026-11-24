"""2-adic / q-adic content of the App. B pieces: v_q(gcd of entries of A_s) versus v_q(h!).  If every piece is
divisible by q^{v_q(h!)}, dividing gives an identity with d = 1 mod q, and the mod-q ranks of A_s/q^v are the
relevant costs.  Also reports those ranks (row, col) for q = 2, 3."""
import sys, math, re
from functools import reduce
sys.path.insert(0, '/home/user/eth-hamiltonicity/research/scripts')
import pieces_fock_ranks as M
src = open('/home/user/eth-hamiltonicity/research/scripts/pieces_fock_ranks.py').read()
src = src.replace("        T = {k:v for k,v in T.items() if v}\n", "        T = {k:v for k,v in T.items() if v}\n        TENS[s] = dict(T)\n")
ns = dict(M.__dict__); ns['TENS'] = {}
exec(compile(src.split('if __name__')[0], 'fock', 'exec'), ns)
from flint import nmod_mat
def vq(n, q):
    v = 0
    while n % q == 0: n //= q; v += 1
    return v
for h in [int(a) for a in sys.argv[1:]]:
    ns['TENS'].clear(); N, ok, res = ns['run'](h)
    hf = math.factorial(h)
    for q in (2, 3):
        V = vq(hf, q); lines = []; worst = 0; allok = True
        for s, T in sorted(ns['TENS'].items()):
            g = reduce(math.gcd, [abs(x) for x in T.values()])
            v = vq(g, q)
            if v < V: allok = False
            Mr = [[0]*(N*N) for _ in range(N*N)]; Mc = [[0]*(N*N) for _ in range(N*N)]
            for (x,y,u,w), val in T.items():
                val //= q ** min(v, V)
                Mr[x*N+y][u*N+w] = val % q; Mc[x*N+u][y*N+w] = val % q
            rr = nmod_mat(Mr, q).rank(); rc = nmod_mat(Mc, q).rank()
            if v >= V: worst = max(worst, (math.log2(rr) if rr else 0) + (math.log2(rc) if rc else 0))
            lines.append(f's={s}:v{v},({rr},{rc})')
        print(f'h={h} N={N} q={q} v_q(h!)={V} all pieces divisible by q^V: {allok}; worst normalised (c_r+c_c)/(4lam) = {worst/(4*math.log2(N)):.4f}')
        print('   ', ' '.join(lines))
    sys.stdout.flush()
