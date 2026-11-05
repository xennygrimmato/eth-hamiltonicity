"""Pieces on Majdoddin's C built from the merge-1 pairing of a-edges with b-edges.
Pair j (j in Z3): a-edge {a_j,a_{j+1}}, b-edge {b_{j+1},b_{j+2}}; legs x=X_{j,j+1}@a_j, v=X_{j+1,j}@a_{j+1},
y=Y_{j+1,j+2}@b_{j+1}, u=Y_{j+2,j+1}@b_{j+2};  f_C = prod_j [x_j=v_j][y_j=u_j]  (a crossing per pair).
merge 1: pair j = bundle (G_j | G_{j+1}) with split {x,y}|{v,u}  (row split of the crossing)
merge 0: groups {x}@G_j, {y,v}@G_{j+1}, {u}@G_{j+2}   (refines the column split {x,u}|{y,v})
merge 2: groups {x,u}@G_j, {v}@G_{j+1}, {y}@G_{j+2}   (refines the column split)."""
import numpy as np, itertools
from lib import *

def leg_index(cfg):
    L = {}
    for l, (e, nd) in enumerate(cfg['legs']): L[(e, nd)] = l
    return L

def pair_legs(cfg, j):
    L = leg_index(cfg); ed = cfg['edges']
    ea = [i for i, (p, q) in enumerate(ed) if {p, q} == {('a', j), ('a', (j + 1) % 3)}][0]
    eb = [i for i, (p, q) in enumerate(ed) if {p, q} == {('b', (j + 1) % 3), ('b', (j + 2) % 3)}][0]
    x = L[(ea, ('a', j))]; v = L[(ea, ('a', (j + 1) % 3))]
    y = L[(eb, ('b', (j + 1) % 3))]; u = L[(eb, ('b', (j + 2) % 3))]
    return x, y, u, v

def assemble(cfg, pieces):
    """pieces[j]: 4-leg array indexed [x,y,u,v] for pair j.  Returns the 12-leg tensor."""
    order = []
    for j in range(3): order += list(pair_legs(cfg, j))
    T = np.einsum('abcd,efgh,ijkl->abcdefghijkl', *pieces)
    perm = np.argsort(order)  # axis order[i] of output gets T axis i
    return np.transpose(T, perm)

def single_bit_pieces():
    F = np.zeros((2,) * 4, dtype=np.int64); Pp = np.zeros_like(F); B = np.zeros_like(F)
    for x, y, u, v in itertools.product(range(2), repeat=4):
        F[x, y, u, v] = (x == v) * (y == u); Pp[x, y, u, v] = (x == u) * (y == v)
        B[x, y, u, v] = -(x != y) * (u != v) * (-1) ** (x + u)
    assert (F == Pp + B).all()
    return F, Pp, B
