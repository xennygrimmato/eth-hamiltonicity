"""Lemma 8 (intermediate depths): certified cell criterion on y-boxes covering [YA, YB].
Usage: python3 grid.py YA YB [mode geom|lin] [step] [X]
For each y-box Y=[ya,yb] (rigorous, ball arithmetic):
  * cover [0,X] by x-boxes; a box is CLEAR if a Taylor-model lower bound of the scaled function
      Gs(x,y) = G(x,y) e^{-s (y-ya)}  (s>=0 fixed per y-box)  is > 0 on box x Y; otherwise it is a candidate with
      u = upper bound of sup (-Gs)_+ on box x Y.
  * consecutive candidate boxes are partitioned (dynamic programming) into pieces P of length <= 0.75; charge
      h(max_P u, kappa(|P|)) (Lemma 4).
  * tail x > X: Lemma 5 bounds at y = yb, pieces of length 0.5.
  * PASS iff  2*sum_P h + 2*Tail(yb)  <  2 * min_Y Delta(y) e^{-2 s (y-ya)}   (Lemma 8 of single_pair.md).
"""
import sys, time, json, math
from common import *

def kappa_table():
    return [None] + [kappa(0.01 * j) for j in range(1, 76)]
KT = kappa_table()
TOLREL = 3e-5
def kap_len(L):
    j = int(math.ceil(float(arb(L).upper()) / 0.01 - 1e-12))
    j = max(j, 1)
    if j > 75: return None
    return KT[j]

NT = 8   # Taylor order

def scaled_derivs(D, s, n):
    """derivatives of e^{-s u} G at u=0 from those of G:  d_y^b (e^{-su}G) = sum_j C(b,j)(-s)^{b-j} d_y^j G."""
    out = {}
    for (a, b) in D:
        if a + b > n: continue
        v = arb(0)
        for j in range(b + 1):
            v += comb(b, j) * (-s) ** (b - j) * D[(a, j)]
        out[(a, b)] = v
    return out

def remainder_coeffs(ymax, s, n):
    """S[(a,b)] >= sup_{box} |d^{a,b} (e^{-s(y-ya)} G)| for a+b = n+1 (y>=ya so the exponential is <= 1)."""
    cr = {}
    S = {}
    for a in range(n + 2):
        b = n + 1 - a
        v = arb(0)
        for j in range(b + 1):
            key = (a, j)
            if key not in cr: cr[key] = crudeG(a, j, ymax)
            v += comb(b, j) * s ** (b - j) * cr[key]
        S[(a, b)] = up(v)
    return S

def Dhat_low(ya, yb, s, n=NT):
    """lower bound of Dhat(y) = Delta(y) e^{-2 s (y-ya)} on [ya,yb] (Taylor of order n at the midpoint + crude remainder)."""
    ya = arb(ya); yb = arb(yb); s = arb(s)
    c = (ya + yb) / 2; h = (yb - ya) / 2
    D = Gderivs(arb(0), 2 * c, n)
    d = [D[(0, 0)] - Kd(arb(0))] + [2 ** j * D[(0, j)] for j in range(1, n + 1)]
    E = (-2 * s * (c - ya)).exp()
    dh = []
    for m in range(n + 1):
        v = arb(0)
        for j in range(m + 1):
            v += comb(m, j) * (-2 * s) ** (m - j) * d[j]
        dh.append(v * E)
    m = n + 1
    crude = [coshmom(0, 2 * yb) - 2 * MOM1[0].real] + [(2 * TWO_PI) ** j * coshmom(j, 2 * yb) for j in range(1, m + 1)]
    R = arb(0)
    for j in range(m + 1):
        R += comb(m, j) * (2 * s) ** (m - j) * crude[j]
    L = dh[0] - sum((abs(dh[k]) * h ** k / factorial(k) for k in range(1, n + 1)), arb(0)) - R * h ** m / factorial(m)
    return L

def box_bound(xlo, xhi, ya, Y, s, S, n=NT):
    """(L, G0, err): certified  e^{-s(y-ya)} G >= L on [xlo,xhi] x Y; Taylor order n at the centre, Lagrange remainder via S."""
    c = (xlo + xhi) / 2; hx = (xhi - xlo) / 2
    yc = arb(Y.mid()); hy = arb(Y.rad())
    D = scaled_derivs(Gderivs(c, yc, n), s, n)
    e = (-s * (yc - ya)).exp()
    G0 = D[(0, 0)] * e
    err = arb(0)
    for (a, b), v in D.items():
        if a + b == 0: continue
        err += abs(v) * e * hx ** a * hy ** b / (factorial(a) * factorial(b))
    for (a, b), v in S.items():
        err += v * hx ** a * hy ** b / (factorial(a) * factorial(b))
    return G0 - err, G0, up(err)

def scan_x(ya, Y, s, X, w0, wmin, tol_abs, S):
    out = []   # list of (xlo, xhi, u) candidates in order
    nbox = [0]
    def rec(lo_, hi_):
        nbox[0] += 1
        L, G0, err = box_bound(lo_, hi_, ya, Y, s, S)
        if L > 0:
            return
        w = float((hi_ - lo_).mid())
        g0 = float(G0.mid()); e = float(err.upper())
        if float((-L).upper()) <= tol_abs:
            out.append((lo_, hi_, up(-L))); return
        if w > wmin and e > 0.05 * abs(g0):
            m = (lo_ + hi_) / 2
            rec(lo_, m); rec(m, hi_)
            return
        out.append((lo_, hi_, up(-L)))
    n0 = int(round(float(X) / w0))
    for i in range(n0):
        rec(arb(X) * i / n0, arb(X) * (i + 1) / n0)
    return out, nbox[0]

def pieces_cost(cands):
    """split candidate boxes into runs and solve the DP. returns (total charge (arb), list of pieces)."""
    runs = []
    for (a, b, u) in cands:
        if runs and float(abs(runs[-1][-1][1] - a).upper()) < 1e-14:
            runs[-1].append((a, b, u))
        else:
            runs.append([(a, b, u)])
    total = arb(0); plist = []
    for run in runs:
        n = len(run)
        xs = [float(run[0][0].mid())] + [float(b.mid()) for (_, b, _) in run]
        us = [float(u.upper()) for (_, _, u) in run]
        KF = [None] + [float(k.lower()) for k in KT[1:]]
        def hf(g, k):
            return 8 * g if 2 * g <= k else (2 * g + k) ** 2 / k
        best = [0.0] + [math.inf] * n; arg = [0] * (n + 1)
        for j in range(1, n + 1):
            umax = 0.0
            for i in range(j - 1, -1, -1):
                umax = max(umax, us[i])
                L = xs[j] - xs[i]
                jj = int(math.ceil(L / 0.01 - 1e-9)) + 1   # safety: one table step more
                if jj > 75: break
                c = best[i] + hf(umax, KF[max(jj, 1)])
                if c < best[j]: best[j] = c; arg[j] = i
        # exact recomputation of the chosen partition in arb
        j = n
        while j > 0:
            i = arg[j]
            umax = up(arb(max(us[i:j])))
            L = run[j - 1][1] - run[i][0]
            kp = kap_len(L)
            assert kp is not None
            total += h_charge(umax, kp)
            plist.append((xs[i], xs[j], float(umax.upper())))
            j = i
    return up(total), plist

def tail_bound(yb, X):
    a1, b1 = tail_coef_small(yb); a2, b2 = tail_coef_large(yb)
    kt = kappa(0.5)
    t1 = tail_charge(a1, b1, X, arb('0.5'), kt); t2 = tail_charge(a2, b2, X, arb('0.5'), kt)
    return t1 if t1 < t2 else t2

def check_ybox(ya, yb, X=arb('15.5'), w0=0.05, wmin=2e-4, verbose=False):
    ya = arb(ya); yb = arb(yb)
    Y = ballx(ya, yb)
    # scaling exponent s = Delta'(ya)/(2 Delta(ya)) (any s>=0 is valid)
    j = Gjet(arb(0), 2 * ya)
    D = j['G'] - j['K']; D1 = 2 * j['Gy']
    s = arb(float((D1 / (2 * D)).mid()))
    if s < 0: s = arb(0)
    Dl = Dhat_low(ya, yb, s)
    tol_abs = TOLREL * float(Dl.lower())
    # y in Y may lie below ya by the rounding radius: e^{-s(y-ya)} <= Fy^(1/2) there; account for it explicitly
    Fy = (2 * s * (arb(ya.upper()) - arb(Y.lower()))).exp()
    Fy = up(Fy)
    S = {k: up(v * Fy) for k, v in remainder_coeffs(arb(Y.upper()), s, NT).items()}
    cands, nb = scan_x(ya, Y, s, X, w0, wmin, tol_abs, S)
    tot, plist = pieces_cost(cands)
    T = tail_bound(arb(Y.upper()), X)
    ratio = up((2 * tot + 2 * T) * Fy / (2 * Dl))
    ok = Dl > 0 and ratio < 1
    return ok, float(ratio.upper()), nb, len(plist), plist, float(T.upper() / Dl.lower())

if __name__ == '__main__':
    YA = float(sys.argv[1]); YB = float(sys.argv[2])
    mode = sys.argv[3] if len(sys.argv) > 3 else 'geom'
    step = float(sys.argv[4]) if len(sys.argv) > 4 else (0.05 if mode == 'geom' else 0.02)
    X = arb(sys.argv[5]) if len(sys.argv) > 5 else arb('15.5')
    logf = open(f'grid_{YA}_{YB}.log', 'w')
    ya = YA; allok = True; worst = 0; t0 = time.time(); nboxes = 0
    while ya < YB - 1e-15:
        yb = ya * (1 + step) if mode == 'geom' else ya + step
        yb = min(yb, YB)
        # exact decimal endpoints (rounded to 1e-9) so consecutive boxes overlap/abut exactly
        yb = round(yb, 9)
        ok, rat, nb, npc, pl, tr = check_ybox(arb(repr(ya)) if False else arb(str(ya)), arb(str(yb)), X)
        sub = 0
        if not ok:
            # split into halves
            m = round((ya + yb) / 2, 9)
            ok1, r1, nb1, _, _, _ = check_ybox(arb(str(ya)), arb(str(m)), X)
            ok2, r2, nb2, _, _, _ = check_ybox(arb(str(m)), arb(str(yb)), X)
            ok = ok1 and ok2; rat = max(r1, r2); nb += nb1 + nb2; sub = 1
        nboxes += 1
        worst = max(worst, rat)
        line = f'Y=[{ya:.9g},{yb:.9g}] ratio<={rat:.5f} {"ok" if ok else "FAIL"} xboxes={nb} pieces={npc} tail/D={tr:.2e} split={sub} t={time.time()-t0:.0f}s'
        print(line, flush=True); logf.write(line + '\n'); logf.flush()
        allok &= ok
        ya = yb
    res = f'{"PASS" if allok else "FAIL"} grid [{YA},{YB}]: {nboxes} y-boxes, worst certified ratio {worst:.5f}'
    print(res); logf.write(res + '\n')
