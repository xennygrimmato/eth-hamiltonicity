"""blocks_C.py -- grouping the 405 Fourier pieces of family (C) (G = (Cyc_3^3)^2 x| Cyc_2 realising <8,8,8> under rows,
coordinatewise identification) into few blocks, as the poly(lambda)-pieces criterion requires.  For each block B:
construction bound c_row <= 3 log2 D(B), D(B) = sum_{rho in B} d_rho (block-diagonal row network), and the true flattening
ranks / D1 cut bounds under rows and columns.  Partitions: T=2 (by degree), T=4 (degree-1 block + degree-2 irreps split by
the first coordinate of alpha), T=4 random, T=8 random."""
import time, numpy as np, fourier_pieces as fp

t0 = time.time()
f = fp.f_delta()
MT = fp.build_mult_table()
S, T_, U = fp.cksu_subset(0), fp.cksu_subset(1), fp.cksu_subset(2)
CH = fp.chars_G()
w = fp.row_words(MT, S, T_, U, list(range(8)), list(range(8)), list(range(8)))
pieces = [((d / 1458) * chi[w], lab, d) for (lab, d, chi) in CH]
print("built 405 pieces", f"{time.time()-t0:.0f}s; sum == f:", np.allclose(sum(p[0] for p in pieces), f))

def report(name, blocks):
    print(f"\npartition {name}: T = {len(blocks)} blocks, 3/2 log2 T = {1.5*np.log2(len(blocks)):.2f}")
    worst = 0
    for bn, idx in blocks.items():
        B = sum(pieces[i][0] for i in idx)
        D = sum(pieces[i][2] for i in idx)
        B = B.real if np.allclose(B.imag, 0) else B
        rk = fp.ranks(B); cb = fp.cutbounds(rk)
        worst = max(worst, cb['row'] + cb['col'])
        print(f"  {str(bn):22s} |B|={len(idx):3d} D={D:4d} 3log2D={3*np.log2(D):6.2f} | rows {rk['rows']} cols {rk['cols']} "
              f"nodes min/max {min(rk['nodes'])}/{max(rk['nodes'])} | c_row>={cb['row']:.2f} c_col>={cb['col']:.2f}")
    print(f"  worst block c_row+c_col >= {worst:.2f}; criterion for any trade at N0=2 needs (c_row+c_col)/2 + 1.5 log2 T < 9: "
          f"{worst/2 + 1.5*np.log2(len(blocks)):.2f}")

deg1 = [i for i, p in enumerate(pieces) if p[2] == 1]; deg2 = [i for i, p in enumerate(pieces) if p[2] == 2]
report("by degree", {"deg 1": deg1, "deg 2": deg2})
byal = {}
for i in deg2:
    al = pieces[i][1][1]; byal.setdefault(al % 3, []).append(i)
report("deg-1 + deg-2 by alpha mod 3", {"deg 1": deg1, **{f"deg2 alpha%3={k}": v for k, v in byal.items()}})
rng = np.random.default_rng(7)
for T in (4, 8):
    lab = rng.integers(0, T, size=405)
    report(f"random T={T}", {f"rand{k}": [i for i in range(405) if lab[i] == k] for k in range(T)})
print(f"done {time.time()-t0:.0f}s")
