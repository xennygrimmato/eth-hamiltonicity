"""Independent cross-check of the closed forms in kern.py by direct numerical quadrature (mpmath, 30 digits)."""
import mpmath as mp
from kern import *
mp.mp.dps = 30
a2 = mp.mpf((A2).mid().str(35, radius=False))
b1, b2 = mp.mpf('0.347412'), mp.mpf('-0.178443'); a1 = mp.mpf(2)/3 + a2
mu = lambda n: 4 * mp.pi * n / 3
f = lambda u: mp.mpf(2)/3 + a1*mp.cos(mu(1)*u) + a2*mp.cos(mu(2)*u) + b1*mp.sin(mu(1)*u) + b2*mp.sin(mu(2)*u)
rq = lambda al: mp.quad(lambda u: f(u)*f(u+al), [-0.75, 0.75-al])
worst = 0
for al in [0, 0.1, 0.37, 0.8, 1.0, 1.2, 1.45]:
    d = abs(rq(al) - mp.mpf((r(arb(al))).mid().str(35, radius=False))); worst = max(worst, d)
fh = lambda x: mp.quad(lambda u: f(u)*mp.exp(-2j*mp.pi*u*x), [-0.75, 0, 0.75])
for x in [0, 0.5, 1.05, 3.3, 9.7]:
    d = abs(abs(fh(x))**2 - mp.mpf((Kd(arb(x))).mid().str(35, radius=False))); worst = max(worst, d)
for x, y in [(0.7, 0.3), (2.2, 1.1), (5.0, 0.01)]:
    v = mp.quad(lambda al: rq(al)*mp.cos(2*mp.pi*al*x)*mp.cosh(2*mp.pi*al*y), [0, 0.5, 1])*2
    d = abs(v - mp.mpf((Pd(arb(x), arb(y))).mid().str(35, radius=False))); worst = max(worst, d)
# derivatives by finite differences
h = mp.mpf('1e-8')
for (x, y) in [(mp.mpf("0.9"), mp.mpf("0.4"))]:
    for a, b in [(1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]:
        F = lambda xx, yy: mp.mpf((G(arb(str(xx)), arb(str(yy)))).mid().str(35, radius=False))
        if (a, b) == (1, 0): fd = (F(x+h, y) - F(x-h, y))/(2*h)
        if (a, b) == (0, 1): fd = (F(x, y+h) - F(x, y-h))/(2*h)
        if (a, b) == (2, 0): fd = (F(x+h, y) - 2*F(x, y) + F(x-h, y))/h**2
        if (a, b) == (0, 2): fd = (F(x, y+h) - 2*F(x, y) + F(x, y-h))/h**2
        if (a, b) == (1, 1): fd = (F(x+h, y+h) - F(x+h, y-h) - F(x-h, y+h) + F(x-h, y-h))/(4*h*h)
        d = abs(fd - mp.mpf((G(arb("0.9"), arb("0.4"), a, b)).mid().str(35, radius=False)))
        print('deriv', a, b, float(d))
print('max abs discrepancy closed form vs quadrature:', float(worst))
print('PASS' if worst < 1e-20 else 'FAIL')
