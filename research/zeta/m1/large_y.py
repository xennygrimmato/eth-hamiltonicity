"""Lemma 9 (large depth, y >= Y2): certified.  Prints PASS and the bound on the charge ratio.
Pieces [k l,(k+1) l], l = 0.4; g_k <= lam cosh(2pi y)/(2 pi^2 (k^2 l^2 + y^2)) + v_k; Delta(y) >= rho theta e^{4 pi y}/(16 pi^2 y^2).
Every term of the resulting bound is non-increasing in y, so the value at Y2 bounds the ratio for all y >= Y2."""
import sys
from common import *
Y2 = arb(sys.argv[1]) if len(sys.argv) > 1 else arb(10)
ell = arb('0.4'); kap = kappa(0.4)
import json
# rho from cert_kernel: r' <= -rho on [0.75,1]; recompute here
a0 = arb('0.75'); mx = None
for i in range(200):
    v = r(ballx(a0 + (1 - a0) * i / 200, a0 + (1 - a0) * (i + 1) / 200), 1).upper()
    mx = v if mx is None or v > mx else mx
rho = -arb(mx); assert rho > 0
c = 4 * PI * Y2; b = 1 - a0
theta = 1 - 2 * (-c * b).exp() - c * b * (-c * b).exp() - c * c * b * b * (-c).exp()
lam = RP1 + (RPP1 + R[3] / (2 * PI * Y2)) / (2 * PI * Y2)
K10 = NORM_R1
# V1, V2
K0 = 2000
V1 = arb(0); V2 = arb(0)
for k in range(0, K0 + 1):
    if k == 0:
        v = K10
    else:
        x = k * ell
        w = (RP1 + (RPP1 + R[3]) / (2 * PI * x)) / (2 * PI ** 2 * x * x)
        v = w if w < K10 else K10
    V1 += v; V2 += v * v
cc = (RP1 + (RPP1 + R[3]) / (2 * PI * K0 * ell)) / (2 * PI ** 2)
V1 += cc / (ell ** 2 * K0); V2 += cc ** 2 / (ell ** 4 * 3 * K0 ** 3)   # sum_{k>K0} k^-4 <= 1/(3 K0^3)
y = Y2
TA2 = 32 * lam ** 2 / (PI ** 2 * rho * theta * kap) * (1 / y ** 2 + PI / (4 * ell * y))
TA1 = 64 * lam / (rho * theta) * (-2 * PI * y).exp() * (1 + PI * y / (2 * ell))
TV = 16 * (V1 + V2 / kap) * 16 * PI ** 2 * y ** 2 * (-4 * PI * y).exp() / (2 * rho * theta)
tot = TA2 + TA1 + TV
print(f'Y2={Y2.str(5)} rho={rho.str(6)} theta={theta.str(6)} lambda={lam.str(6)} kappa(0.4)={kap.str(6)} V1={V1.str(6)} V2={V2.str(6)}')
print(f'ratio <= {float(tot.upper()):.5f}  (quadratic part {float(TA2.upper()):.5f}, linear {float(TA1.upper()):.2e}, K1(x) part {float(TV.upper()):.2e})')
print('PASS large-y lemma for all y >= %s' % Y2.str(5) if tot < 1 else 'FAIL')
