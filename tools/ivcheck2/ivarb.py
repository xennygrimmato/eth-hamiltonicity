"""Endpoint interval arithmetic whose every rounding is delegated to Arb (python-flint).

An Iv holds two exact Arb numbers lo <= hi (radius 0).  Every operation computes each endpoint
with Arb ball arithmetic (rigorous enclosure of the exact real result) and keeps the outward
end of that ball (`lower()` / `upper()`).  Case distinctions use Arb's comparison operators,
which return True only when the relation is certain; every "else" branch is a valid
(possibly looser) enclosure, so an undecided comparison can never make a result wrong.

Only the operations the checked functions need are provided.
"""
from flint import arb, ctx

ctx.prec = 64
ZERO = arb(0)
ONE = arb(1)
PI = arb.pi()
HALF_PI = PI / 2


def _lo(x):
    return x.lower()


def _hi(x):
    return x.upper()


class Iv:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        if not isinstance(lo, arb):
            lo = arb(lo)  # exact for Python floats / ints
        if not isinstance(hi, arb):
            hi = arb(hi)
        self.lo = _lo(lo)
        self.hi = _hi(hi)

    @staticmethod
    def _raw(lo, hi):
        r = Iv.__new__(Iv)
        r.lo = lo
        r.hi = hi
        return r

    def __repr__(self):
        return "Iv[%s, %s]" % (self.lo.str(20, radius=False), self.hi.str(20, radius=False))

    # --- ring operations -------------------------------------------------------------------
    def __add__(self, o):
        if not isinstance(o, Iv):
            o = Iv(o)
        return Iv._raw(_lo(self.lo + o.lo), _hi(self.hi + o.hi))

    __radd__ = __add__

    def __neg__(self):
        return Iv._raw(-self.hi, -self.lo)

    def __sub__(self, o):
        if not isinstance(o, Iv):
            o = Iv(o)
        return Iv._raw(_lo(self.lo - o.hi), _hi(self.hi - o.lo))

    def __rsub__(self, o):
        return Iv(o) - self

    def scale(self, c):
        """Multiply by an exact constant c (Python float/int or exact arb)."""
        c = arb(c)
        if c >= 0:
            return Iv._raw(_lo(self.lo * c), _hi(self.hi * c))
        return Iv._raw(_lo(self.hi * c), _hi(self.lo * c))

    def __mul__(self, o):
        if not isinstance(o, Iv):
            return self.scale(o)
        p = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        lo = _lo(p[0]); hi = _hi(p[0])
        for q in p[1:]:
            ql = _lo(q); qh = _hi(q)
            if ql < lo:
                lo = ql
            if qh > hi:
                hi = qh
        return Iv._raw(lo, hi)

    __rmul__ = __mul__

    def sqr(self):
        if self.lo >= 0:
            return Iv._raw(_lo(self.lo * self.lo), _hi(self.hi * self.hi))
        if self.hi <= 0:
            return Iv._raw(_lo(self.hi * self.hi), _hi(self.lo * self.lo))
        a = _hi(self.lo * self.lo); b = _hi(self.hi * self.hi)
        return Iv._raw(ZERO, a if a > b else b)

    def abs(self):
        if self.lo >= 0:
            return self
        if self.hi <= 0:
            return -self
        a = -self.lo
        return Iv._raw(ZERO, a if a > self.hi else self.hi)

    def sqrt(self):
        """sqrt of the non-negative part (callers apply it only to quantities that are >= 0
        mathematically; a negative lower end can only come from overestimation)."""
        if self.hi < 0:
            raise ValueError("sqrt of negative interval")
        lo = _lo(self.lo.sqrt()) if self.lo > 0 else ZERO
        return Iv._raw(lo, _hi(self.hi.sqrt()))

    def recip_pos(self):
        """1/x for an interval certainly > 0."""
        if not (self.lo > 0):
            raise ValueError("recip of interval not certainly positive")
        return Iv._raw(_lo(ONE / self.hi), _hi(ONE / self.lo))

    def __truediv__(self, o):
        return self * o.recip_pos()

    def contains_zero(self):
        return not (self.lo > 0 or self.hi < 0)

    # --- trigonometric ranges used by the 3-variable problem ------------------------------
    def cos_halfpi(self):
        """cos on an interval certainly inside [-pi/2, pi/2]... [-pi, pi]: cos is increasing on
        [-pi,0] and decreasing on [0,pi], so the minimum is at an endpoint."""
        if not (self.lo >= -PI and self.hi <= PI):
            return _ball_fallback(self, "cos")
        cl = self.lo.cos(); ch = self.hi.cos()
        lo = _lo(cl) if cl.lower() < ch.lower() else _lo(ch)
        if self.lo <= 0 and self.hi >= 0:
            hi = ONE
        elif self.hi < 0:
            hi = _hi(ch)
        elif self.lo > 0:
            hi = _hi(cl)
        else:
            hi = ONE
        return Iv._raw(lo, hi)

    def sin2(self):
        """sin^2 on an interval certainly inside [-pi, pi]: sin^2 is even and, as a function of
        |x| on [0, pi], increasing on [0, pi/2] and decreasing on [pi/2, pi]."""
        if not (self.lo >= -PI and self.hi <= PI):
            return _ball_fallback(self, "sin2")
        a = self.abs()
        p, q = a.lo, a.hi
        sp = p.sin(); sq = q.sin()
        sp2 = sp * sp; sq2 = sq * sq
        if q <= HALF_PI:
            return Iv._raw(_lo(sp2), _hi(sq2))
        if p >= HALF_PI:
            return Iv._raw(_lo(sq2), _hi(sp2))
        lo = _lo(sp2) if sp2.lower() < sq2.lower() else _lo(sq2)
        return Iv._raw(lo, ONE)


def _ball_fallback(x, fn):
    """Rigorous but loose: evaluate Arb's ball function on a ball containing [lo, hi]."""
    b = x.lo.union(x.hi)
    if fn == "cos":
        r = b.cos()
    else:
        s = b.sin()
        r = s * s
        r = r.nonnegative_part() if hasattr(r, "nonnegative_part") else r
    return Iv._raw(_lo(r), _hi(r))


def iv_of_ball(b):
    return Iv._raw(_lo(b), _hi(b))
