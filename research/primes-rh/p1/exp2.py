# Deletion adversary on REAL primes: given a query family F (sets in a window W), find
# Y subset of P∩W, |Y| <= rank(F), such that X = P\Y has EVEN count on every query
# (Davenport/Olson for (Z/2)^Q: D = Q+1). GF(2) elimination with python-int bitsets.
import numpy as np, sys
P=np.load(sys.argv[1]).astype(np.int64)
def seg(a,b): return P[np.searchsorted(P,a,'left'):np.searchsorted(P,b,'right')]
def family(N,H,J):
    Q=[]
    for i in range(0,H.bit_length()):          # geometric prefixes
        for j in range(0,J+1):                 # residue classes mod 2^j inside each prefix
            for a in range(2**j):
                Q.append(('pre',N,N+2**i,j,a))
        for b in range(40):                     # bit classes inside each prefix (XOR family)
            Q.append(('bit',N,N+2**i,b))
    for k in range(1,65):                       # sliding windows [N, N+kH/64]
        Q.append(('pre',N,N+k*H//64,0,0))
    return Q
def member(q,p):
    if q[0]=='pre': return q[1]<=p<=q[2] and (p%(2**q[3]))==q[4]
    return q[1]<=p<=q[2] and (p>>q[3])&1
def attack(N,H,J):
    S=[int(p) for p in seg(N,N+H)]; F=family(N,H,J)
    # vector for each prime: bitmask over queries; want subset Y with XOR of vectors = XOR over all S
    vec=[sum(1<<i for i,q in enumerate(F) if member(q,p)) for p in S]
    target=0
    for v in vec: target^=v
    basis={}  # pivot-> (vector, set of prime indices as int mask)
    for idx,v in enumerate(vec):
        m=1<<idx
        while v:
            piv=v.bit_length()-1
            if piv in basis: bv,bm=basis[piv]; v^=bv; m^=bm
            else: basis[piv]=(v,m); break
    t=target; m=0
    while t:
        piv=t.bit_length()-1; bv,bm=basis[piv]; t^=bv; m^=bm
    Y=[S[i] for i in range(len(S)) if m>>i&1]
    X=set(S)-set(Y)
    ok=all(sum(member(q,p) for p in X)%2==0 for q in F)
    return len(F),len(basis),len(S),len(Y),ok,min(X) if X else None
for N,H,J in [(10**9,2**12,3),(10**9+12345,2**14,4),(1999999000,2**15,5)]:
    print(dict(zip("Q rank #P |Y| allEven minX".split(),attack(N,H,J))),"N",N,"H",H)
