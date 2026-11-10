"""Lemma 6 (small depth, 0 < y <= Y1): certified.  Prints PASS with the margin.
For y<=Y1:  G_y(x) >= K(x) - y^2 W(x),  W = K1''/2 + Y1^2 E4,  E4 = (2pi)^4 cosh(2pi Y1)/24 * int a^4 r1.
Core [0,X0]: boxes where W<0 or K - Y1^2 W > 0 cannot meet {G_y<0}; the rest is grouped into pieces P, charge 8 y^2 sup_P W.
Tail x>X0: Lemma 5(b) with coefficients <= (y/Y1)^2 * coef(Y1).  Self term 2 Delta(y) >= 4 y^2 |K1''(0)|."""
import sys
from common import *
Y1 = arb(sys.argv[1]) if len(sys.argv) > 1 else arb('0.01')
X0 = arb(sys.argv[2]) if len(sys.argv) > 2 else arb('15.5')
DMAX = 0.5
E4 = (2 * PI) ** 4 * (2 * PI * Y1).cosh() / 24 * M4
y1s = Y1 * Y1
def F0(x):
    k, k1 = Kjet(x, 2); return k[0] - y1s * (k1[2] / 2 + y1s * E4)
def F1(x):
    k, k1 = Kjet(x, 3); return k[1] - y1s * k1[3] / 2
def F2(B):
    k, k1 = Kjet(B, 4); return k[2] - y1s * k1[4] / 2
def Wup(B):
    """upper bound of W on ball B (Taylor: W(c) + |W'(c)|h + sup|W''| h^2/2)."""
    c = arb(B.mid()); h = arb(B.rad())
    k, k1 = Kjet(c, 3); kb, k1b = Kjet(B, 4)
    return up(k1[2] / 2 + abs(k1[3]) / 2 * h + abs(k1b[4]) / 4 * h * h + y1s * E4)

def classify(lo_, hi_, depth=0, wmin=1e-4):
    B = ballx(lo_, hi_)
    w = Wup(B)
    if w < 0:
        return []
    c = (lo_ + hi_) / 2; h = (hi_ - lo_) / 2
    L = F0(c) - abs(F1(c)) * h - abs(F2(B)) * h * h / 2
    if L > 0:
        return []
    if float(hi_ - lo_) <= wmin:
        return [(lo_, hi_, w)]
    m = (lo_ + hi_) / 2
    return classify(lo_, m, depth + 1, wmin) + classify(m, hi_, depth + 1, wmin)

N0 = int(float(X0) / 0.05)
cand = []
for i in range(N0):
    cand += classify(X0 * i / N0, X0 * (i + 1) / N0)
# group into pieces
pieces = []
for (a, b, w) in cand:
    if pieces and abs(float(pieces[-1][1] - a)) < 1e-15 and float(b - pieces[-1][0]) <= DMAX:
        pa, pb, pw = pieces[-1]; pieces[-1] = (pa, b, pw if pw > w else w)
    else:
        pieces.append((a, b, w))
S = arb(0); okk = True
for (a, b, w) in pieces:
    kap = kappa(min(float(up(b - a)), 0.75))
    if not (2 * y1s * w <= kap): okk = False
    S += w
core_ratio = up(16 * S / (4 * K1DD0))
a1c, b1c = tail_coef_small(Y1)
kt = kappa(0.5)
tail1 = tail_charge(a1c, b1c, X0, arb('0.5'), kt)
tail_ratio = up(2 * tail1 / (4 * y1s * K1DD0))
tot = core_ratio + tail_ratio
print(f'Y1={Y1.str(4)} X0={X0.str(4)} pieces={len(pieces)}')
for (a, b, w) in pieces:
    print(f'   piece [{float(a):.4f},{float(b):.4f}]  sup W <= {float(w.upper()):.4e}')
print(f'core ratio <= {float(core_ratio.upper()):.4f}, tail ratio <= {float(tail_ratio.upper()):.4f}, total <= {float(tot.upper()):.4f}')
print('PASS small-y lemma: sum of charges <= %.4f * 2Delta(y) for all 0<y<=%s' % (float(tot.upper()), Y1.str(4))
      if (tot < 1 and okk) else 'FAIL')
