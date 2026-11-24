# Exact-identity certificate for D=2 (no tensor powers): each network a has integer min-cut widths
# k1 (cut {e1,e2}|{-e1,-e2}), k2 (cut {e1,-e2}|{-e1,e2}); Crofton+min-cut: cost >= L = c1*(k1+k2)+c2*max(k1,k2),
# c1 = 2-sqrt2, c2 = 2(sqrt2-1).  Rank constraints: sum_a 2^k1 >= 4^m, sum_a 2^k2 >= 4^m (flattening),
# sum_a min(2^k1,2^k2) >= 2^m (SWAP lemma, r+s>=n).  Instance excluded if no multiset of A profiles has max L < W*.
import itertools, math
c1=2-math.sqrt(2); c2=2*(math.sqrt(2)-1)
def feasible(m,A,thr):
    W = 4*m - thr*math.log2(A)
    prof=[(a,b) for a in range(2*m+1) for b in range(2*m+1) if c1*(a+b)+c2*max(a,b) < W-1e-12]
    if not prof: return False,W,None
    # A small: brute force multisets via combinations_with_replacement on Pareto-maximal profiles
    par=[p for p in prof if not any(q!=p and q[0]>=p[0] and q[1]>=p[1] for q in prof)]
    for ms in itertools.combinations_with_replacement(par,A):
        if sum(2**a for a,b in ms)>=4**m and sum(2**b for a,b in ms)>=4**m and sum(min(2**a,2**b) for a,b in ms)>=2**m:
            return True,W,ms
    return False,W,None
for name,thr in [("[A] sqrt-D",2*math.sqrt(2)),("[O] 2D",4.0)]:
    print(name)
    for m in range(1,11):
        row=[]
        for A in range(2,9):
            ok,W,ms=feasible(m,A,thr)
            row.append(f"A={A}:{'open' if ok else 'excl'}")
        print(f" m={m}: "+"  ".join(row))
ok,W,ms=feasible(4,2,2*math.sqrt(2)); print("m=4,A=2 witness profile",ms,"W*",W)
ok,W,ms=feasible(3,2,2*math.sqrt(2)); print("m=3,A=2",ok,W)
