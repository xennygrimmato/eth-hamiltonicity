# Idea 7: sizes of explicit sparse families inside [x,2x] for which primes are known (or conjectured) to exist.
import math
for e in [8,12,16,20]:
    x=10**e
    fi=sum( max(0, math.isqrt(2*x-b**4)-math.isqrt(max(x-b**4,0)-1) if x-b**4>0 else math.isqrt(2*x-b**4)+1) for b in range(1,int((2*x)**0.25)+1))
    sq1=math.isqrt(2*x-1)-math.isqrt(x-2)          # n^2+1
    ps=lambda c: int((2*x)**(1/c))-int(x**(1/c))   # floor(n^c)
    print(f"x=1e{e}: sqrt x={math.isqrt(x):.2e} | a^2+b^4 (FI, proved) {fi:.2e} ~x^{math.log(fi)/math.log(x):.3f} | n^2+1 (conj.) {sq1:.2e} ~x^0.5 "
          f"| PS c=1.16 (proved, Rivat-Wu c<243/205) {ps(243/205):.2e} ~x^{1/(243/205):.3f} | BHP interval x^0.525={x**0.525:.2e} | RH interval sqrt(x)log x={math.sqrt(x)*math.log(x):.2e}")
