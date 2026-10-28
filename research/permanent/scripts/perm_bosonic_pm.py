#!/usr/bin/env python3
"""Local-product ("bosonic") blob network for #PM of a bipartite graph (exact integers).

Identity:  per(A) = [e_1...e_n z_1...z_n]  prod_{(i,j): A_ij = 1} (1 + e_i z_j)
in the commutative algebra Z[e, z]/(e_i^2, z_j^2).  (This is the Godsil-Gutman sign average
E_S det(A o S)^2 written out: averaging over independent signs leaves exactly this product with
e_i = psibar_i phibar_i, z_j = psi_j phi_j, which commute and square to zero.  No signs anywhere.)

Blob network, exactly as for Hamiltonian cycles (exact-hc-theorem.md s.4-5) but without the sign
rule: vertices (rows and columns) are partitioned into g blobs; an edge inside a blob is private; a
crossing edge (i, j) gets a 1-bit label l in {0,1} with pieces (1, 1) for l = 0 and (e_i, z_j) for
l = 1.  W_a(labels at a) = top coefficient, in the generators of blob a, of the product of the
internal factors (1 + e_i z_j) and of a's pieces of the crossing edges = number of perfect
matchings of blob a's leftover vertices once the l = 1 crossing edges are removed.  Value = sum
over labels of prod_a W_a = #PM.  Bits: c_ab = |E(a,b)| (one per crossing edge), U = 2 m_cross.

This is a *bijection-term* network (nonzero terms <-> perfect matchings; the labels are the matched
crossing edges).  For a sparse graph (m = O(n)) it gives #PM in 2^{O(m/sqrt(log n))} with a proof
simpler than the HC one; for a dense graph m_cross = Theta(n^2).

Run: python3 perm_bosonic_pm.py -> PASS/FAIL.
"""
import itertools, random, sys

def nmul(X, Y):
    """product in Z[gens]/(gen^2); monomials are bitmasks."""
    out = {}
    for m1, c1 in X.items():
        for m2, c2 in Y.items():
            if m1 & m2:
                continue
            out[m1 | m2] = out.get(m1 | m2, 0) + c1 * c2
    return {m: c for m, c in out.items() if c}

ONE = {0: 1}

def count_pm(A, rows, cols):
    rows, cols = list(rows), list(cols)
    if len(rows) != len(cols):
        return 0
    if not rows:
        return 1
    i = rows[0]
    return sum(count_pm(A, rows[1:], [c for c in cols if c != j]) for j in cols if A[i][j])

def network(A, blob):
    """blob: dict vertex -> blob id; vertices are ('r', i) and ('c', j)."""
    n = len(A)
    gen = {}
    for i in range(n):
        gen[('r', i)] = 1 << (2 * i); gen[('c', i)] = 1 << (2 * i + 1)
    edges = [(('r', i), ('c', j)) for i in range(n) for j in range(n) if A[i][j]]
    cross = [e for e in edges if blob[e[0]] != blob[e[1]]]
    blobs = sorted(set(blob.values()))
    tables = {}
    for a in blobs:
        verts = [v for v in gen if blob[v] == a]
        top = sum(gen[v] for v in verts)
        inc = [k for k, e in enumerate(cross) if a in (blob[e[0]], blob[e[1]])]
        base = ONE
        for (u, v) in edges:
            if blob[u] == a and blob[v] == a:
                base = nmul(base, {0: 1, gen[u] | gen[v]: 1})
        tab = {}
        for labs in itertools.product((0, 1), repeat=len(inc)):
            X = base
            for k, l in zip(inc, labs):
                if l:
                    u, v = cross[k]
                    mine = u if blob[u] == a else v
                    X = nmul(X, {gen[mine]: 1})
                    if not X:
                        break
            val = X.get(top, 0) if X else 0
            if val:
                tab[labs] = val
        tables[a] = (inc, tab)
    total = 0
    for labs in itertools.product((0, 1), repeat=len(cross)):
        w = 1
        for a in blobs:
            inc, tab = tables[a]
            w *= tab.get(tuple(labs[k] for k in inc), 0)
            if not w:
                break
        total += w
    U = 2 * len(cross)
    P = max(len(tables[a][0]) for a in blobs)
    return total, U, P

def main():
    rng = random.Random(5)
    ok = True
    for n, dens, g in [(4, 0.5, 2), (5, 0.5, 2), (6, 0.4, 2), (6, 0.4, 3), (7, 0.35, 3), (6, 1.0, 2), (7, 1.0, 2)]:
        A = [[1 if rng.random() < dens else 0 for _ in range(n)] for _ in range(n)]
        blob = {}
        for i in range(n):
            blob[('r', i)] = i * g // n; blob[('c', i)] = i * g // n
        val, U, P = network(A, blob)
        pm = count_pm(A, range(n), range(n))
        good = val == pm; ok &= good
        m = sum(map(sum, A))
        print(f"n={n} |E|={m} g={g}: #PM={pm} network={val} {'ok' if good else 'MISMATCH'}; U=2 m_cross={U}, P=max crossing edges at a blob={P}")
    print("U = 2 m_cross: linear in |E| (sparse: O(n)), Theta(n^2) for dense A.")
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
