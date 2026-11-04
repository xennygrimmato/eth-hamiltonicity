"""Crossing grid H_{p,q}: rows R_a (paths r_{a,0..q-1}), columns C_b (paths c_{0..p-1,b}),
rungs r_{a,b}-c_{a,b}.  Max degree 3.  A directed cycle uses rungs ("corners"); the corner type is
kappa = (order H->V or V->H, horizontal direction +-1, vertical direction +-1): 8 types.
Search for a directed simple cycle in which every corner type occurs an even number of times
(the 'balanced' cycle needed by Theorem L in kstar.md)."""
import sys
def H(p, q):
    R = lambda a, b: a*q + b
    Cc = lambda a, b: p*q + a*q + b
    E = []
    for a in range(p):
        for b in range(q-1): E.append((R(a, b), R(a, b+1)))
    for b in range(q):
        for a in range(p-1): E.append((Cc(a, b), Cc(a+1, b)))
    for a in range(p):
        for b in range(q): E.append((R(a, b), Cc(a, b)))
    return 2*p*q, E, R, Cc
def info(v, p, q):
    if v < p*q: return ('r',) + divmod(v, q)
    return ('c',) + divmod(v - p*q, q)
def corner_types(cyc, p, q):
    L = len(cyc); out = []
    for i in range(L):
        u, v, w = cyc[i-1], cyc[i], cyc[(i+1) % L]
        tv, a, b = info(v, p, q)
        if tv != 'r': continue
        tu, tw = info(u, p, q)[0], info(w, p, q)[0]
        if tu == 'r' and tw == 'r': continue      # straight along row
        if tw == 'c':      # row -> column at (a,b): arrival from u, leave via c(a,b) to x
            hd = b - info(u, p, q)[2]; x = cyc[(i+2) % L]; vd = info(x, p, q)[1] - a
            out.append(('HV', hd, vd))
        else:              # column -> row: came from c(a,b), which came from y
            y = cyc[i-2]; vd = a - info(y, p, q)[1]; hd = info(w, p, q)[2] - b
            out.append(('VH', hd, vd))
    return out
def balanced(cyc, p, q):
    from collections import Counter
    c = Counter(corner_types(cyc, p, q))
    return all(x % 2 == 0 for x in c.values()), c
def search(p, q, maxlen=None):
    n, E, R, Cc = H(p, q)
    adj = [[] for _ in range(n)]
    for i, j in E: adj[i].append(j); adj[j].append(i)
    best = None
    def dfs(s, v, path, seen):
        nonlocal best
        for w in adj[v]:
            if w == s and len(path) >= 3:
                ok, c = balanced(path, p, q)
                if ok and sum(c.values()) > 0: best = list(path); return True
            elif w > s and not (seen >> w) & 1:
                if maxlen and len(path) >= maxlen: continue
                path.append(w)
                if dfs(s, w, path, seen | (1 << w)): return True
                path.pop()
        return False
    for s in range(n):
        if dfs(s, s, [s], 1 << s): return best
    return None
if __name__ == '__main__':
    for p, q in [(2,2),(2,3),(3,3),(3,4),(4,4)]:
        cyc = search(p, q)
        if cyc:
            print(p, q, 'balanced cycle found, len', len(cyc), [info(v,p,q) for v in cyc])
            print('  corners', balanced(cyc, p, q)[1]); break
        else: print(p, q, 'none')
