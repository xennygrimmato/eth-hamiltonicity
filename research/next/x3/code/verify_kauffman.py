# Exact check (integers) of the skein identity C_{2,1} = N1 + N2 and of its tensor powers' bookkeeping.
# Terminals order: (e1, e2, -e1, -e2); C[a,b,c,d] = [a==c][b==d].
import itertools, math
def C(a,b,c,d): return int(a==c and b==d)
def N1(a,b,c,d): return int(a==d and b==c)            # wires e1--(-e2), e2--(-e1): length sqrt2 each
eps=lambda x,y: (x-y)                                  # singlet  |01>-|10>  (as eps[0][1]=-1? sign irrelevant, squared)
def N2(a,b,c,d): return eps(a,b)*eps(c,d)              # wires e1--e2, (-e1)--(-e2) carrying the singlet
ok=all(C(*t)==N1(*t)+N2(*t) for t in itertools.product((0,1),repeat=4))
print("C_{2,1} = N1 + N2 exactly over Z:",ok)
w=2*math.sqrt(2); A=2; D=2; m=1
print(f"w={w:.4f}, saving 2Dm-w={2*D*m-w:.4f}, sigma=saving/log2A={(2*D*m-w)/math.log2(A):.4f}; need >2sqrtD={2*math.sqrt(D):.4f} ([A]) or >2D=4 ([O])")
