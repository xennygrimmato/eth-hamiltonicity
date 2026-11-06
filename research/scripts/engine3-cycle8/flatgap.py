"""flatgap.py -- EXACT finite-size flattening test for a given ansatz  f = sum_t (network t)  at N = 2, one bit per edge.
For a contraction M (orientation o of a subset of the edges; X-end = tail string, Y-end = head string, unused strings fixed),
rank_{X|Y}(f contracted) = 2^{|E(M)|}, and a network under merge k with bond exponents e satisfies, for every cut S of its
groups,  rank <= 2^{e(delta S) + #misplaced} = 2^{|E(M)| - (n_S - e(delta S))}  (engine2-decorrelated §8.2).  Hence an ansatz
with terms t (merge k_t, bonds e_t) is IMPOSSIBLE (over any field) if some M has  sum_t 2^{-gap_t(M)} < 1,
gap_t(M) = max_S (n^{k_t}_S - e_t(delta S))  (S ranging over all subsets, incl. empty: gap >= 0).
Enumerates all reachable (n^G, n^H) states by DP (exact), so 'not excluded' is also exact for this family of tests."""
import itertools, numpy as np

def make(nodes, edges, merges):
    gid = [{v: i for i, g in enumerate(gs) for v in g} for gs in merges]
    def vec(e):
        u, v = e; out = []
        for k, gs in enumerate(merges):
            x = [0] * len(gs); x[gid[k][u]] += 1; x[gid[k][v]] -= 1; out += x
        return tuple(out)
    states = {(0,) * sum(len(g) for g in merges)}
    for e in edges:
        w = vec(e); states = {tuple(a + c * b for a, b in zip(s, w)) for s in states for c in (-1, 0, 1)}
    S = np.array(sorted(states))
    off = np.cumsum([0] + [len(g) for g in merges])
    blocks = [S[:, off[k]:off[k + 1]] for k in range(len(merges))]
    return blocks

def gaps(nblock, bonds):
    """nblock: (#states, r) group excesses; bonds: dict (i,j)->exponent for i<j.  returns gap per state."""
    r = nblock.shape[1]; best = np.zeros(len(nblock))
    for size in range(1, r):
        for Sset in itertools.combinations(range(r), size):
            cut = sum(e for (i, j), e in bonds.items() if (i in Sset) != (j in Sset))
            best = np.maximum(best, nblock[:, list(Sset)].sum(1) - cut)
    return best

def test(blocks, terms):
    """terms: list of (merge index, bonds dict). returns (excluded?, min over states of sum_t 2^-gap, witness index)."""
    tot = sum(2.0 ** (-gaps(blocks[k], b)) for k, b in terms)
    i = int(np.argmin(tot)); return tot[i] < 1 - 1e-12, tot[i], i

# ---------------------------------------------------------------- instances
dist8 = lambda i, j: min((j - i) % 8, (i - j) % 8)
C8 = dict(nodes=list(range(1, 9)), G=[[1, 2], [3, 4], [5, 6], [7, 8]], H=[[2, 3], [4, 5], [6, 7], [8, 1]])
E8_all = [(i, j) for i, j in itertools.combinations(range(1, 9), 2) if dist8(i, j) >= 2]
E8_two = [e for e in E8_all if dist8(*e) >= 3]
PR = dict(nodes='ABCDEF', G=[['A', 'B'], ['C', 'D'], ['E', 'F']], H=[['A', 'F'], ['B', 'C'], ['D', 'E']])
_pos = {'A': (1, 1), 'B': (1, 2), 'C': (2, 2), 'D': (2, 3), 'E': (3, 3), 'F': (3, 1)}
EPR = [(u, v) for u, v in itertools.combinations('ABCDEF', 2) if _pos[u][0] != _pos[v][0] and _pos[u][1] != _pos[v][1]]

def K4(adj, diag13, diag24):
    """bonds on K_4 groups 0..3 (cyclic order): adjacent pairs exponent adj, (0,2) diag13, (1,3) diag24."""
    return {(0, 1): adj, (1, 2): adj, (2, 3): adj, (0, 3): adj, (0, 2): diag13, (1, 3): diag24}
def K3(a, b, c): return {(0, 1): a, (0, 2): b, (1, 2): c}

if __name__ == '__main__':
    print("== 8-cycle, 12 two-cell edges: raw G-bonds = adjacent pairs 1 bit, diagonals 4 bits (total 12) ==")
    B = make(C8['nodes'], E8_two, [C8['G'], C8['H']])
    print("reachable states:", len(B[0]))
    # sanity: the raw network alone must not be excluded; the empty ansatz must be
    print(" sanity raw G-network alone excluded?", test(B, [(0, K4(1, 4, 4))])[0], "; bonds-0 alone excluded?", test(B, [(0, K4(0, 0, 0))])[0])
    for adj in (1,):
        for a, b in [(1, 1), (1, 2), (2, 2), (1, 3), (2, 3), (1, 4), (3, 3), (2, 4), (3, 4), (4, 4)]:
            cost = 4 * adj + a + b
            r = test(B, [(0, K4(adj, a, b)), (1, K4(adj, a, b))])
            r3 = test(B, [(0, K4(adj, a, b)), (1, K4(adj, a, b)), (0, K4(adj, a, b))])
            print(f" R+C, both K4 bonds adj={adj} diag=({a},{b}) [cost {cost}, criterion (cost+12)/2+1 = {(cost+12)/2+1}]:"
                  f" excluded={r[0]} (min sum 2^-gap = {r[1]:.4f});  R+C+R': excluded={r3[0]} ({r3[1]:.4f})")
    print(" bonds 2 on every K4 edge but adjacent 0 (i.e. R has only diagonals) :", test(B, [(0, K4(0, 1, 1)), (1, K4(0, 1, 1))])[:2])
    print("== 8-cycle, all 20 edges: raw G-bonds adj 1+2 ... computed below ==")
    B20 = make(C8['nodes'], E8_all, [C8['G'], C8['H']])
    print("reachable states:", len(B20[0]))
    print("== prism (9 edges), raw K3 bonds 3,3,3 ==")
    BP = make(list(PR['nodes']), EPR, [PR['G'], PR['H']])
    for bonds in [(1, 1, 1), (2, 2, 2), (1, 1, 2), (1, 2, 2), (2, 2, 3), (1, 2, 3), (3, 3, 3)]:
        r2 = test(BP, [(0, K3(*bonds)), (1, K3(*bonds))])
        r3 = test(BP, [(0, K3(*bonds)), (1, K3(*bonds)), (0, K3(*bonds))])
        print(f" prism R+C bonds 2^{bonds}: excluded={r2[0]} ({r2[1]:.4f});  R+C+R': excluded={r3[0]} ({r3[1]:.4f})")
