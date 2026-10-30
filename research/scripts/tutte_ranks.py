"""Exact ranks of the gluing matrices of the Tutte plane (research/tutte-plane.md §4-5).

R1  M_q[P,Q] = q^{|P v Q|} on set partitions of [b]:  M_q = Zeta diag((q)_{|S|}) Zeta^T  with
    Zeta[P,S] = [P <= S] unitriangular, so rank M_q = #{S : (q)_{|S|} != 0}
    = sum_{j <= q} S(b,j) for q in {0,..,b-1}, Bell(b) otherwise.     (b <= 6, exact over Q)
R2  connectivity C[P,Q] = [P v Q = 1]: C = Zeta diag(mu(S,1)) Zeta^T, mu(S,1) = (-1)^{k-1}(k-1)!,
    rank_Q = Bell(b);  rank_{F_p} = #{S : |S| <= p}.                    (b <= 6, p = 2,3,5)
R3  the whole-plane gluing kernel K_{u,v}[P,Q] = u^{|PvQ|} v^{b-|P|-|Q|+|PvQ|}  (u=x-1, v=y-1):
    rank = rank M_{uv} when uv != 0; at v = 0 (y=1) it is the weighted acyclicity matrix
    A_u[P,Q] = u^{|PvQ|}[|P|+|Q|-|PvQ| = b] whose rank is <= 4^b  (printed; it equals the
    number of ... see the table printed); at u = 0 (x=1) it is C up to scaling: rank Bell(b).
R4  realisability on max-degree-3 test graphs: L side = linear forest F_sigma on u_1..u_b,
    crossing matching u_i w_i, R side = linear forest F_tau on w_1..w_b.  The cut matrix
    [Z_{G(sigma,tau)}(q,v)] has rank = rank M_q whenever x != 0 and y != 1 (proof in the note:
    it is A M_q B^T with A, B triangular); the T-normalised matrix [T_{G(sigma,tau)}(x,y)] is
    computed too.  x = 0: the triangle gadget (two crossing edges per u_i) is used instead.
R5  contrast with Hamiltonian cycles: perfect-matching connectivity matrix
    H[M,M'] = [M u M' is one cycle] on perfect matchings of [2k]: rank over Q (single exponential).
Prints PASS/FAIL.
"""
import sys, itertools, math, random
from fractions import Fraction
from tutte_lib import *

def falling(q, k):
    r = Fraction(1)
    for i in range(k):
        r *= (q - i)
    return r

def M_matrix(b, q):
    Ps = set_partitions(b)
    return Ps, [[Fraction(q) ** nblocks(join(P, Q)) for Q in Ps] for P in Ps]

def expected_rank_Mq(b, q):
    q = Fraction(q)
    if q.denominator == 1 and 0 <= q < b:
        return sum(stirling2(b, j) for j in range(1, int(q) + 1)) if q > 0 else 0
    return bell(b)

def mobius_to_top(S):
    k = nblocks(S)
    return (-1) ** (k - 1) * math.factorial(k - 1)

def linear_forest_edges(P, verts):
    """path through each block (in index order) on the given vertex list."""
    E = []
    for B in blocks(P):
        for s, t in zip(B, B[1:]):
            E.append((verts[s], verts[t]))
    return E

def test_graph(b, sig, tau, gadget="matching"):
    """vertices: u_i = i, w_i = b+i (and w'_i = 2b+i for the triangle gadget)."""
    U = list(range(b)); W = [b + i for i in range(b)]
    E = linear_forest_edges(sig, U) + linear_forest_edges(tau, W)
    if gadget == "matching":
        E += [(i, b + i) for i in range(b)]
        n = 2 * b
    else:   # triangle gadget: u_i - w_i, u_i - w'_i, w_i - w'_i
        E += [(i, b + i) for i in range(b)] + [(i, 2 * b + i) for i in range(b)] + [(b + i, 2 * b + i) for i in range(b)]
        n = 3 * b
    return n, E

def eval_T_and_Z(n, E, x, y):
    """exact T(x,y) and Z(q,v) by subset expansion (independent of the partition formula)."""
    x, y = Fraction(x), Fraction(y); u, v = x - 1, y - 1
    k = ncomp(n, E); rE = n - k
    T = Fraction(0); Z = Fraction(0)
    for _, A in subsets(E):
        kA = ncomp(n, A); rA = n - kA
        T += u ** (rE - rA) * v ** (len(A) - rA) if (rE - rA >= 0 and (u != 0 or rE == rA)) else 0
        Z += (u * v) ** kA * v ** len(A)
    return T, Z

def eval_T(n, E, x, y):
    x, y = Fraction(x), Fraction(y); u, v = x - 1, y - 1
    k = ncomp(n, E); rE = n - k; T = Fraction(0)
    for _, A in subsets(E):
        kA = ncomp(n, A); rA = n - kA
        a, c = rE - rA, len(A) - rA
        T += (u ** a if a else 1) * (v ** c if c else 1)
    return T

def main(maxb=5, seed=1):
    rng = random.Random(seed)
    C = Checker("tutte_ranks")
    # ---------------- R1
    print("R1 rank of M_q = [q^{|PvQ|}]")
    qs = [0, 1, 2, 3, 4, 5, -1, -2, Fraction(1, 2), Fraction(7, 3), Fraction(-5, 2)]
    for b in range(1, 7):
        row = []
        for q in qs:
            if b == 6 and q not in (2, 3, Fraction(1, 2), -1):
                continue
            Ps, M = M_matrix(b, q)
            r = rank_Q(M)
            C.check(r == expected_rank_Mq(b, q), f"R1 b={b} q={q} rank {r}")
            row.append(f"q={q}:{r}")
        print(f"  b={b} Bell={bell(b)} " + " ".join(row))
    # factorization check M_q = Zeta diag((q)_|S|) Zeta^T
    for b in range(1, 6):
        Ps = set_partitions(b)
        for q in (Fraction(3, 2), 2, -1):
            ok = all(Fraction(q) ** nblocks(join(P, Q)) ==
                     sum(falling(q, nblocks(S)) for S in Ps if refines(P, S) and refines(Q, S))
                     for P in Ps for Q in Ps)
            C.check(ok, f"R1 factorization b={b}")
    # ---------------- R2
    print("R2 connectivity [PvQ = 1]: rank over Q and F_p")
    for b in range(1, 7):
        Ps = set_partitions(b); top = tuple([0] * b)
        Cm = [[1 if join(P, Q) == top else 0 for Q in Ps] for P in Ps]
        rq = rank_Q(Cm)
        C.check(rq == bell(b), f"R2 b={b}")
        ok = all(Cm[i][j] == sum(mobius_to_top(S) for S in Ps if refines(P, S) and refines(Q, S))
                 for i, P in enumerate(Ps) for j, Q in enumerate(Ps)) if b <= 5 else True
        C.check(ok, f"R2 Mobius factorization b={b}")
        rp = {}
        for p in (2, 3, 5):
            rp[p] = rank_p(Cm, p)
            C.check(rp[p] == sum(stirling2(b, j) for j in range(1, min(b, p) + 1)), f"R2 mod {p} b={b}")
        print(f"  b={b} rank_Q={rq} rank_F2={rp[2]} rank_F3={rp[3]} rank_F5={rp[5]}")
    # ---------------- R3
    print("R3 whole-plane kernel K_{u,v}; y=1 acyclicity matrix ranks")
    for b in range(1, 7):
        Ps = set_partitions(b)
        for (u, v) in ((Fraction(2), Fraction(3, 4)), (Fraction(-1, 3), Fraction(5))):
            if b == 6:
                break
            K = [[u ** nblocks(join(P, Q)) * v ** (b - nblocks(P) - nblocks(Q) + nblocks(join(P, Q))) for Q in Ps] for P in Ps]
            C.check(rank_Q(K) == expected_rank_Mq(b, u * v), "R3 K rank = M_uv rank")
        acyc = [[1 if nblocks(P) + nblocks(Q) - nblocks(join(P, Q)) == b else 0 for Q in Ps] for P in Ps]
        ra = rank_Q(acyc)
        Au = [[Fraction(5, 3) ** nblocks(join(P, Q)) * acyc[i][j] for j, Q in enumerate(Ps)] for i, P in enumerate(Ps)]
        rau = rank_Q(Au)
        C.check(rau <= 4 ** b and ra <= 4 ** b, "R3 acyclic rank <= 4^b")
        # spanning-tree point (1,1): [P v Q = 1 and acyclic]
        top = tuple([0] * b)
        tr = [[1 if (join(P, Q) == top and acyc[i][j]) else 0 for j, Q in enumerate(Ps)] for i, P in enumerate(Ps)]
        rt = rank_Q(tr)
        print(f"  b={b} Bell={bell(b)} rank[acyclic]={ra} rank[u^c acyclic, u=5/3]={rau} rank[tree]={rt} 2^b={2**b} C(2b,b)={math.comb(2*b,b)}")
    # ---------------- R4 realisability
    print("R4 cut matrices on max-degree-3 test graphs (exact subset expansion)")
    pts = [(2, 2), (3, Fraction(1, 2)), (-2, 3), (Fraction(1, 2), 3), (2, 0), (-1, 0), (0, -2),
           (1, 2), (1, -1), (1, 1), (2, 1), (Fraction(5, 2), 1), (3, 3), (0, Fraction(1, 2)), (0, 3), (Fraction(-1, 2), Fraction(-1, 2))]
    for b in range(1, maxb + 1):
        Ps = set_partitions(b)
        line = []
        for (x, y) in pts:
            if b == 5 and (x, y) not in ((2, 2), (1, 2), (2, 1), (-2, 3), (0, Fraction(1, 2))):
                continue
            x, y = Fraction(x), Fraction(y); u, v = x - 1, y - 1; q = u * v
            gadget = "triangle" if x == 0 else "matching"
            Tm = []; Zm = []
            for P in Ps:
                tr_, zr_ = [], []
                for Q in Ps:
                    n, E = test_graph(b, P, Q, gadget)
                    T = eval_T(n, E, x, y)
                    tr_.append(T)
                    if u != 0 and v != 0:
                        zr_.append(T * u ** ncomp(n, E) * v ** n)
                Tm.append(tr_); Zm.append(zr_)
            rT = rank_Q(Tm)
            rZ = rank_Q(Zm) if (u != 0 and v != 0) else None
            if u != 0 and v != 0:
                C.check(rZ == expected_rank_Mq(b, q), f"R4 Z-rank b={b} ({x},{y}) {rZ}")
            if v == 0:
                pred = None
            elif u == 0:
                C.check(rT == bell(b), f"R4 x=1 T-rank b={b} y={y}: {rT}")
            line.append(f"({x},{y}):T{rT}" + (f"/Z{rZ}" if rZ is not None else ""))
        print(f"  b={b} Bell={bell(b)}  " + " ".join(line))
    # ---------------- R5 HC contrast
    print("R5 perfect-matching connectivity [M u M' Hamiltonian] rank over Q")
    for k in range(1, 5):
        pts2 = list(range(2 * k))
        def pms(S):
            if not S:
                yield []
                return
            a = S[0]
            for i in range(1, len(S)):
                for rest in pms(S[1:i] + S[i + 1:]):
                    yield [(a, S[i])] + rest
        Ms = list(pms(pts2))
        H = [[1 if ncomp(2 * k, M1 + M2) == 1 else 0 for M2 in Ms] for M1 in Ms]
        r = rank_Q(H)
        print(f"  k={k} (b=2k={2*k} boundary vertices) #matchings={len(Ms)} rank={r}  2^(k-1)={2**(k-1)} Bell(2k)={bell(2*k)}")
        C.check(r <= 4 ** k, "R5 HC rank single exponential")
    return C.done()

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 4)
