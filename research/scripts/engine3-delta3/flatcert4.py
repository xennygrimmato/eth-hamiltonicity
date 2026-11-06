"""flatcert4.py -- flattening certificate (exhaustive, 3 groups per merge: d_k = max |n_G|) for
 (a) AG(2,3) with the whole anti-diagonal class as configuration (three disjoint triangles, 9 nodes, 9 edges),
     merges = columns, rows, diagonals;  core floor there is 1/3 (one line = agreeing core with 3 of 9 edges);
 (b) the same with only two merges (columns, rows) -- the configuration then is 3 triangles inside the 3x3 grid.
Also prints, for each instance, the core floor max_H |E_cross(H)| / E over all node subsets H (join of restricted merges)."""
import itertools, numpy as np
def lp3(n): return max(abs(x) for x in n)
def certify(nodes, edges, merges, name):
    E=len(edges); nid={v:i for i,v in enumerate(nodes)}
    inc=np.zeros((len(nodes),E),dtype=int)
    for e,(u,v) in enumerate(edges): inc[nid[u],e]=1; inc[nid[v],e]=-1
    gm=[np.array([[1 if v in G else 0 for v in nodes] for G in groups]) for groups in merges]
    best=-1
    for orient in itertools.product((0,1,-1),repeat=E):
        o=np.array(orient)
        if not o.any(): continue
        flow=inc@o
        val=min(lp3(tuple(int(x) for x in (g@flow))) for g in gm)
        if val>best: best=val
    print(f"{name}: nodes {len(nodes)}, edges {E}, merges {len(merges)}: flattening D = {best} of {E} -> rho >= {best/E:.4f}")
def core_floor(nodes, edges, merges, name):
    best=(0,None)
    for r in range(1,len(nodes)+1):
        for H in itertools.combinations(nodes,r):
            Hs=set(H)
            # join of restricted partitions: union-find over nodes of H
            parent={v:v for v in H}
            def find(v):
                while parent[v]!=v: v=parent[v]
                return v
            for groups in merges:
                for G in groups:
                    GH=[v for v in G if v in Hs]
                    for v in GH[1:]: parent[find(v)]=find(GH[0])
            cross=sum(1 for u,v in edges if u in Hs and v in Hs and find(u)!=find(v))
            if cross>best[0]: best=(cross,H)
    print(f"  core floor: max_H |E_cross(H)| = {best[0]} of {len(edges)} -> rho >= {best[0]/len(edges):.4f}, H = {best[1]}")
pts=[(x,y) for x in range(3) for y in range(3)]
cls=lambda f: [[p for p in pts if f(p)==c] for c in range(3)]
cols=cls(lambda p:p[0]); rows=cls(lambda p:p[1]); diag=cls(lambda p:(p[0]-p[1])%3); anti=cls(lambda p:(p[0]+p[1])%3)
edges_anti=[(u,v) for L in anti for u,v in itertools.combinations(L,2)]
certify(pts,edges_anti,[cols,rows,diag],"AG(2,3) anti-diagonal class (3 triangles), merges cols/rows/diags")
core_floor(pts,edges_anti,[cols,rows,diag],"")
certify(pts,edges_anti,[cols,rows],"AG(2,3) anti-diagonal class, merges cols/rows only")
core_floor(pts,edges_anti,[cols,rows],"")
# core floors of the earlier instances
A=[('a',i) for i in range(3)]; B=[('b',i) for i in range(3)]
edgesC=[(('a',i),('a',j)) for i in range(3) for j in range(i+1,3)]+[(('b',i),('b',j)) for i in range(3) for j in range(i+1,3)]
mergesC=[[[('a',i),('b',(i+k)%3)] for i in range(3)] for k in range(3)]
print("C:"); core_floor(A+B,edgesC,mergesC,"")
nodesP=[(1,1),(1,2),(2,2),(2,3),(3,3),(3,1)]
edgesP=[(u,v) for u,v in itertools.combinations(nodesP,2) if u[0]!=v[0] and u[1]!=v[1]]
print("prism:"); core_floor(nodesP,edgesP,[[[v for v in nodesP if v[0]==r] for r in (1,2,3)],[[v for v in nodesP if v[1]==c] for c in (1,2,3)]],"")
g33=[(r,c) for r in (1,2,3) for c in (1,2,3)]
edges33=[(u,v) for u,v in itertools.combinations(g33,2) if u[0]!=v[0] and u[1]!=v[1]]
print("3x3 level:"); core_floor(g33,edges33,[[[v for v in g33 if v[0]==r] for r in (1,2,3)],[[v for v in g33 if v[1]==c] for c in (1,2,3)]],"")
n=list(range(1,9)); G=[[1,2],[3,4],[5,6],[7,8]]; H=[[2,3],[4,5],[6,7],[8,1]]
edges8=[(i,j) for i,j in itertools.combinations(n,2) if (j-i)%8 not in (1,7)]
print("8-cycle:"); core_floor(n,edges8,[G,H],"")
MUL=[[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]; p4=[(x,y) for x in range(4) for y in range(4)]
gs=lambda s:[[(x,y) for (x,y) in p4 if (y^MUL[s][x])==c] for c in range(4)]
edgesT=[((x,c),(x,c^1)) for x in range(4) for c in (0,2)]
print("T4:"); core_floor(p4,edgesT,[gs(0),gs(1),gs(2)],"")
L=[[(x,MUL[3][x]^c) for x in range(4)] for c in (0,1)]; n2=L[0]+L[1]
e2=[(u,v) for line in L for u,v in itertools.combinations(line,2)]
m2=[[[v for v in Gg if v in n2] for Gg in gs(s)] for s in (0,1,2)]
print("AG(2,4) two lines:"); core_floor(n2,e2,m2,"")
