"""The counted cost of the Appendix-B pieces for large h, exactly.

p(E) by the Euler recurrence (exact integers).  For each lambda (or h): the paper's
    c^row_s + c^col_s = clog2(R^row_s) + clog2(R^col_s),  R^row_s = sum_{i=0}^{2h} p(s+i),  R^col_s = sum_i p(2h-s-i),
its maximum over s in [-2h, 2h] (= cost at s = 0 up to rounding), divided by 4 lambda, and the
"general law" f(2h) / (2 f(h)) with f = log2 p.  Also the same law for f(E) = log2 (number of
partitions of E into squares) and into powers of two (sub-square growth), as a reference for what
beta < 1/2 would give IF a two-order structure existed on those spaces.
"""
import math, sys


def partition_numbers(M):
    pp = [0] * (M + 1)
    pp[0] = 1
    for n in range(1, M + 1):
        s = 0
        k = 1
        while True:
            g1 = k * (3 * k - 1) // 2
            if g1 > n:
                break
            sign = 1 if k % 2 else -1
            s += sign * pp[n - g1]
            g2 = k * (3 * k + 1) // 2
            if g2 <= n:
                s += sign * pp[n - g2]
            k += 1
        pp[n] = s
    return pp


def restricted_partition_numbers(M, parts):
    pp = [0] * (M + 1)
    pp[0] = 1
    for k in parts:
        if k > M:
            break
        for n in range(k, M + 1):
            pp[n] += pp[n - k]
    return pp


def clog2(n):
    return (n - 1).bit_length() if n >= 1 else 0


def lg(n):
    return math.log2(n) if n > 0 else float('-inf')


def h_of(lam, pp):
    h = 2
    while pp[h] < 2 ** lam:
        h += 1
    return h


def main():
    M = 20000
    pp = partition_numbers(M)
    cHR = math.pi * math.sqrt(2 / 3) / math.log(2)
    print("lambda    h   p(h)>=2^lam  max_s(c_row+c_col)/(4lam)  [s*]   f(2h)/(2f(h))   (c_HR sqrt(2h)-log(2h))/(2 c_HR sqrt h)")
    for lam in [8, 16, 32, 64, 128, 256, 512, 1024, 2048]:
        h = h_of(lam, pp)
        if 4 * h > M:
            break
        best, sbest = 0, None
        # cumulative sums of p for R^row_s, R^col_s
        cum = [0] * (4 * h + 2)
        for E in range(4 * h + 1):
            cum[E + 1] = cum[E] + pp[E]
        for s in range(-2 * h, 2 * h + 1):
            lo, hi = max(s, 0), min(s + 2 * h, 4 * h)
            Rrow = cum[hi + 1] - cum[lo] if hi >= lo else 0
            lo2, hi2 = max(-s, 0), min(2 * h - s, 4 * h)
            Rcol = cum[hi2 + 1] - cum[lo2] if hi2 >= lo2 else 0
            c = clog2(Rrow) + clog2(Rcol)
            if c > best:
                best, sbest = c, s
        law = lg(pp[2 * h]) / (2 * lg(pp[h]))
        hr = (cHR * math.sqrt(2 * h) - math.log2(2 * h)) / (2 * cHR * math.sqrt(h))
        print(f"{lam:6d} {h:6d} {str(pp[h] >= 2**lam):>8}   {best/(4*lam):.4f}   [{sbest:4d}]      {law:.4f}       {hr:.4f}")
    print(f"\n1/sqrt2 = {1/math.sqrt(2):.4f}.  The counted cost converges to 1/sqrt2 from above, like 1 - O(log lam / lam).")

    # reference growths
    print("\nReference: the general law rho = f(2h)/(2 f(h)) for other graded spaces (no two-order structure known):")
    M2 = 200000
    sq = restricted_partition_numbers(M2, [k * k for k in range(1, 500)])
    pw = restricted_partition_numbers(M2, [2 ** k for k in range(0, 20)])
    ppl = partition_numbers(M2) if M2 <= 20000 else None
    print(" space                        h      log2 dim V_h     f(2h)/(2 f(h))   2^(beta-1) for the nominal beta")
    for name, arr, beta in [("partitions into squares (beta=1/3)", sq, 1 / 3), ("binary partitions (beta->0)", pw, 0.0)]:
        for h in [1000, 10000, 100000]:
            print(f" {name:33s} {h:7d}   {lg(arr[h]):10.2f}        {lg(arr[2*h])/(2*lg(arr[h])):.4f}          {2**(beta-1):.4f}")
    for h in [1000, 5000, 10000]:
        print(f" {'all partitions (beta=1/2)':33s} {h:7d}   {lg(pp[h]):10.2f}        {lg(pp[2*h])/(2*lg(pp[h])):.4f}          {2**(0.5-1):.4f}")


if __name__ == "__main__":
    main()
