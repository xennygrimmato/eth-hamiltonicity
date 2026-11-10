"""Certify the kernel facts used in single_pair.md (Lemma 1-2): admissibility, value, constants.  Prints PASS/FAIL."""
from flint import arb, acb, ctx
from kern import *
from certlib import *
ok_all = True
def rep(name, ok, extra=''):
    global ok_all
    ok_all &= bool(ok)
    print(('PASS ' if ok else 'FAIL ') + name, extra)

rr = lambda d: (lambda a: r(a, d))
# exact f and f' (for the endpoint lemma near alpha = 3/2)
c = fourier_coeffs(A2)
def f_d(u, d=0):
    u = acb(u); s = acb(0)
    for n in range(-2, 3):
        lam = I * MU(n); s += c[n] * lam ** d * (lam * u).exp()
    return s.real
rep('f(3/4) = 0 and f(-3/4) = 0 (exact: a1 = 2/3 + a2; ball check)', abs(f_d(arb(0.75))) < 1e-40 and abs(f_d(arb(-0.75))) < 1e-40,
    f'f(3/4) in {f_d(arb(0.75))}')
rep('int f = 1, i.e. K(0) = 1', abs(Kd(arb(0)) - 1) < 1e-40, str(Kd(arb(0))))

# --- r >= 0 on [0,1], r <= 0 on [1,3/2] ---
d1 = arb('0.02')
r1ball = r(arb(1) + arb(0, d1.upper()), 1)
rep('r\' < 0 on [1-0.02, 1+0.02]', r1ball < 0, str(r1ball))
ok, n, mn = certify_positive(rr(0), rr(1), lambda B: r(B, 2), 0, arb(1) - d1)
rep('r > 0 on [0, 0.98]', ok, f'({n} boxes, min lower bound {mn})')
neg = lambda d: (lambda a: -r(a, d))
d3 = arb('0.02')
ok, n, mn = certify_positive(neg(0), neg(1), lambda B: -r(B, 2), arb(1) + d1, arb(1.5) - d3)
rep('r < 0 on [1.02, 1.48]', ok, f'({n} boxes, min {mn})')
fp_lo = f_d(arb(-0.75) + arb(0, 0.02) + 0.02, 1); fp_hi = f_d(arb(0.75) - arb(0, 0.02) - 0.02, 1)
# f' on [-3/4, -3/4+0.04] and [3/4-0.04, 3/4]
rep("f' < 0 on [-3/4,-3/4+0.04] and on [3/4-0.04,3/4]  (=> r<0 on (3/2-0.04,3/2), Lemma 1(c))", fp_lo < 0 and fp_hi < 0, f'{fp_lo} {fp_hi}')

# --- value ---
I1 = moments_r(1, acb(0), 1)
r0 = r(arb(0))
val = 2 - r0 - 2 * I1[1].real
rep('value 2 - r(0) - 2 int_0^1 a r(a) da > 0.67364 (record)', val > arb('0.67364'), str(val))
print('   value =', val.str(10))
tau = -2 * (moments_r(1.5, acb(0), 0)[0].real - moments_r(1, acb(0), 0)[0].real)
print('   tau = int_{|a|>1} |r| =', tau.str(8), '  K1(0) = int r1 =', (2 * I1[0].real).str(10))

# --- constants for the analytic lemmas ---
def supabs(d, a, b, n=2000):
    """certified sup of |r^{(d)}| on [a,b] via boxes."""
    a = arb(a); b = arb(b); m = arb(0)
    for i in range(n):
        lo = a + (b - a) * i / n; hi = a + (b - a) * (i + 1) / n
        B = (lo + hi) / 2 + arb(0, ((hi - lo) / 2).upper())
        v = abs(r(B, d)).upper()
        if v > m: m = arb(v)
    return m
consts = {}
for d in range(4):
    consts[f'R{d}'] = supabs(d, 0, 1)
consts['rp1'] = r(arb(1), 1); consts['rpp1'] = r(arb(1), 2)
consts['K1dd0'] = -(TWO_PI) ** 2 * 2 * I1[0].real * 0  # placeholder replaced below
m2 = moments_r(1, acb(0), 4)
consts['K1dd0'] = -(TWO_PI ** 2) * 2 * m2[2].real          # K1''(0) = -4pi^2 int_{-1}^1 a^2 r
consts['m4'] = 2 * m2[4].real                               # int_{-1}^1 a^4 r  (= int a^4 |r1|, r>=0)
consts['normr1'] = 2 * m2[0].real                           # int |r1| = K1(0)
consts["rp0"] = r(arb(0), 1)
for k, v in consts.items():
    print(f'   {k} = {v.str(12)}')
# rho: r(a) >= rho (1-a) on [a0,1]; certify via r'(t) <= -rho on [a0,1]  (r(a) = int_a^1 -r')
a0 = arb('0.75'); B = (a0 + 1) / 2 + arb(0, ((1 - a0) / 2).upper())
mx = None
n = 200
for i in range(n):
    lo = a0 + (1 - a0) * i / n; hi = a0 + (1 - a0) * (i + 1) / n
    v = r((lo + hi) / 2 + arb(0, ((hi - lo) / 2).upper()), 1).upper()
    mx = v if mx is None or v > mx else mx
rho = -arb(mx)
rep("r' <= -rho < 0 on [0.75,1] (rho for Lemma 7)", rho > 0, f'rho = {rho.str(8)}')
# kappa table: K' <= 0 on (0, 0.75], and K(d) lower bounds
ok, n, mn = certify_positive(lambda x: -Kd(x, 2), lambda x: -Kd(x, 3), lambda B: -Kd(B, 4), 0, arb('0.25'))
rep("K'' < 0 on [0,0.25]", ok)
ok2, n2, mn2 = certify_positive(lambda x: -Kd(x, 1), lambda x: -Kd(x, 2), lambda B: -Kd(B, 3), arb('0.25'), arb('0.75'))
rep("K' < 0 on [0.25,0.75] (so K decreasing on [0,0.75])", ok2)
import json
out = {k: [float(v.lower()), float(v.upper())] for k, v in consts.items()}
out['rho'] = [float(rho.lower()), float(rho.upper())]
out['value'] = [float(val.lower()), float(val.upper())]
json.dump(out, open('kernel_constants.json', 'w'), indent=1)
print('ALL PASS' if ok_all else 'SOME FAIL')
