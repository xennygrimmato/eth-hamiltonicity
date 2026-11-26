"""Read an ivcert certificate only as a bisection tree, and rebuild its leaf boxes.

Used from the format: header lines `dim N`, `domain <hex lo> <hex hi>` (N lines), `tree`, the
preorder lines, `end <leaves>`.  In the preorder, `S d` splits coordinate d at the float
midpoint lo + 0.5*(hi - lo) (computed here in IEEE double, as Python floats are); every other
line is a leaf whose first token is its tag.  All numerical data the prover attached to a leaf
(lower bounds, centres, preconditioners) is ignored: only the tag is kept, and the only tag
given meaning is `X` (excluded: must lie in a region covered by another argument).
Tags `P` (symmetry-pruned) and `F` (failed) are reported and make the certificate unusable
for this checker.

Coverage is structural: each split replaces [lo, hi] by [lo, m] and [m, hi] with
lo < m < hi checked exactly, so the leaves partition the domain (up to shared faces).  As an
independent sanity check the leaf volumes are summed with exact rationals and compared with the
domain volume.
"""
import struct
from fractions import Fraction


def hexf(h):
    return struct.unpack(">d", bytes.fromhex(h))[0]


class Cert:
    def __init__(self, path):
        self.path = path
        self.problem = None
        self.dim = None
        self.domain = []
        self.leaves = []  # list of (tag, box) with box = tuple of (lo, hi) floats
        self.declared_leaves = None
        self.max_depth = 0
        self._parse()

    def _parse(self):
        with open(self.path) as f:
            lines = [ln.split("#", 1)[0].strip() for ln in f]
        lines = [ln for ln in lines if ln]
        it = iter(lines)
        assert next(it) == "ivcert-certificate v1", "bad magic"
        for ln in it:
            tok = ln.split()
            if tok[0] == "problem":
                self.problem = tok[1]
            elif tok[0] == "dim":
                self.dim = int(tok[1])
            elif tok[0] == "bound":
                self.bound = hexf(tok[1])
            elif tok[0] == "domain":
                lo, hi = hexf(tok[1]), hexf(tok[2])
                assert lo < hi
                self.domain.append((lo, hi))
            elif tok[0] == "tree":
                break
            else:
                raise ValueError("unknown header line: " + ln)
        assert len(self.domain) == self.dim
        # preorder walk with an explicit stack of pending boxes
        stack = [(tuple(self.domain), 0)]
        for ln in it:
            tok = ln.split()
            if tok[0] == "end":
                self.declared_leaves = int(tok[1])
                break
            if not stack:
                raise ValueError("tree has more nodes than boxes")
            box, depth = stack.pop()
            self.max_depth = max(self.max_depth, depth)
            if tok[0] == "S":
                d = int(tok[1])
                lo, hi = box[d]
                m = lo + 0.5 * (hi - lo)
                if not (lo < m < hi):
                    raise ValueError("degenerate split")
                left = box[:d] + ((lo, m),) + box[d + 1:]
                right = box[:d] + ((m, hi),) + box[d + 1:]
                stack.append((right, depth + 1))  # left child comes next in preorder
                stack.append((left, depth + 1))
            elif len(tok[0]) == 1 and tok[0] in "NMTCGXPF":
                self.leaves.append((tok[0], box))
            else:
                raise ValueError("unknown tree line: " + ln)
        if stack:
            raise ValueError("tree ended with %d unvisited boxes" % len(stack))
        for ln in it:
            raise ValueError("trailing data after end: " + ln)

    def coverage_report(self):
        vol = Fraction(0)
        for _, box in self.leaves:
            v = Fraction(1)
            for lo, hi in box:
                v *= Fraction(hi) - Fraction(lo)
            vol += v
        dvol = Fraction(1)
        for lo, hi in self.domain:
            dvol *= Fraction(hi) - Fraction(lo)
        tags = {}
        for t, _ in self.leaves:
            tags[t] = tags.get(t, 0) + 1
        return {
            "leaves": len(self.leaves),
            "declared": self.declared_leaves,
            "volume_equal": vol == dvol,
            "tags": tags,
            "max_depth": self.max_depth,
        }
