#!/usr/bin/env python3
"""Exact check of the structural claims in clique-evaluation.md §3 (MM inside a level).

(K,lam)-clique with K = 3g, D = 2^lam, random integer tables.  Checks, all exact integers:
 (a) value = trace(M1 M2 M3) where M_i is the group tensor (D^{g^2} x D^{g^2} matrix).
 (b) a rank decomposition of the MM tensor <D',D',D'> = <D,D,D>^{(x) g^2}, with the g^2 factors
     indexed by the triangles (a, b, L(a,b)) of a Latin square L, turns the value into
        sum over r in [R]^{g x g} of Z1(r) Z2(r) Z3(r)
     where Z1(r) is a (g,lam)-clique over group 1 whose node a reads row a of r, Z2(r) one over
     group 2 whose node b reads column b of r, Z3(r) one over group 3 whose node c reads the
     fibre {(a,b): L(a,b)=c}.  Here we use the trivial rank decomposition of <D,D,D>
     (R = D^3 terms, l_{ijk}(A) = A_ij, m_{ijk}(B) = B_jk, n_{ijk}(C) = C_ki); any FMM
     decomposition has the same shape with R = D^{omega}.  So FMM = exponentially many terms,
     each a (g,lam)-clique:  e_{3g} <= (omega + e_g)/9.
"""
import itertools, random
random.seed(1)

def clique_value(K, D, T, edges):
    # T[a] : dict from tuple of labels (ordered by edge index at a) -> int
    idx = {e: i for i, e in enumerate(edges)}
    at = {a: [idx[e] for e in edges if a in e] for a in range(K)}
    total = 0
    for lab in itertools.product(range(D), repeat=len(edges)):
        p = 1
        for a in range(K):
            p *= T[a][tuple(lab[i] for i in at[a])]
            if p == 0: break
        total += p
    return total

def main():
    g, D = 2, 2
    K = 3*g
    edges = [(a, b) for a in range(K) for b in range(a+1, K)]
    at = {a: [e for e in edges if a in e] for a in range(K)}
    T = {a: {lab: random.randint(-2, 2) for lab in itertools.product(range(D), repeat=K-1)}
         for a in range(K)}
    V = clique_value(K, D, T, edges)
    G = [list(range(0, g)), list(range(g, 2*g)), list(range(2*g, 3*g))]

    def group_tensor(Gi, Gj, Gk):
        """M[p][q]: p = labels on Gi-Gk edges (ordered), q = labels on Gi-Gj edges; sum over internal."""
        ek = [e for e in edges if (e[0] in Gi and e[1] in Gk) or (e[1] in Gi and e[0] in Gk)]
        ej = [e for e in edges if (e[0] in Gi and e[1] in Gj) or (e[1] in Gi and e[0] in Gj)]
        ei = [e for e in edges if e[0] in Gi and e[1] in Gi]
        M = {}
        for p in itertools.product(range(D), repeat=len(ek)):
            for q in itertools.product(range(D), repeat=len(ej)):
                s = 0
                for z in itertools.product(range(D), repeat=len(ei)):
                    lab = dict(zip(ek, p)); lab.update(zip(ej, q)); lab.update(zip(ei, z))
                    pr = 1
                    for a in Gi:
                        pr *= T[a][tuple(lab[e] for e in at[a])]
                    s += pr
                M[(p, q)] = s
        return M, ek, ej

    # (a) trace(M1 M2 M3): M1[p,q] p: G1-G3, q: G1-G2 ; M2[q,s] q: G2-G1, s: G2-G3 ; M3[s,p]
    M1, e13, e12 = group_tensor(G[0], G[1], G[2])
    M2, e21, e23 = group_tensor(G[1], G[2], G[0])
    M3, e32, e31 = group_tensor(G[2], G[0], G[1])
    assert set(e13) == set(e31) and set(e12) == set(e21) and set(e23) == set(e32)
    def relab(src, dst, lab):   # reorder a label tuple from edge order src to edge order dst
        d = dict(zip(src, lab)); return tuple(d[e] for e in dst)
    tr = 0
    for p in itertools.product(range(D), repeat=len(e13)):
        for q in itertools.product(range(D), repeat=len(e12)):
            for s in itertools.product(range(D), repeat=len(e23)):
                tr += M1[(p, q)] * M2[(relab(e12, e21, q), s)] * M3[(relab(e23, e32, s), relab(e13, e31, p))]
    print("(a) trace(M1M2M3) == clique value:", "PASS" if tr == V else f"FAIL {tr} {V}")

    # (b) Latin square L(a,b) = (a+b) mod g ; triangle (a, g+b, 2g+L(a,b)).
    # trivial rank decomposition of <D,D,D>: r = (i,j,k); l(A)=A_ij, m(B)=B_jk, n(C)=C_ki, where the
    # MM factor for triangle (a,b,c) has A indexed by (p=x_{ac}, q=x_{ab}), B by (q=x_{ab}, s=x_{bc}),
    # C by (s=x_{bc}, p=x_{ac}).  So the term r_{ab}=(i,j,k) fixes x_{ac}=i, x_{ab}=j, x_{bc}=k:
    # Z1(r) = clique over G1 with node a's cross labels fixed by row a of r, etc.
    tri = {(a, b): (a, g+b, 2*g+(a+b) % g) for a in range(g) for b in range(g)}
    cross = {}
    for (a, b), (A_, B_, C_) in tri.items():
        cross[(a, b)] = ((min(A_, C_), max(A_, C_)), (min(A_, B_), max(A_, B_)), (min(B_, C_), max(B_, C_)))
    assert sorted(e for v in cross.values() for e in v) == sorted(e for e in edges if not any(e[0] in Gi and e[1] in Gi for Gi in G))

    def sub_clique(Gi, fixed):
        ei = [e for e in edges if e[0] in Gi and e[1] in Gi]
        s = 0
        for z in itertools.product(range(D), repeat=len(ei)):
            lab = dict(fixed); lab.update(zip(ei, z))
            pr = 1
            for a in Gi:
                pr *= T[a][tuple(lab[e] for e in at[a])]
            s += pr
        return s

    total = 0
    cells = list(tri.keys())
    for rs in itertools.product(itertools.product(range(D), repeat=3), repeat=len(cells)):
        fixed = {}
        for cell, (i, j, k) in zip(cells, rs):
            eac, eab, ebc = cross[cell]
            fixed[eac] = i; fixed[eab] = j; fixed[ebc] = k
        # Z1 depends only on labels of edges at G1 nodes, i.e. on row a of r (cells (a,.)), etc.
        total += sub_clique(G[0], fixed) * sub_clique(G[1], fixed) * sub_clique(G[2], fixed)
    print("(b) sum_r Z1(r)Z2(r)Z3(r) == clique value:", "PASS" if total == V else f"FAIL {total} {V}")
    print(f"    terms: R^(g^2) = {D**3}^{g*g} = {D**(3*g*g)} ; each term = three ({g},{1})-cliques;"
          f" brute force 2^{len(edges)} = {2**len(edges)} labellings")

if __name__ == "__main__":
    main()
