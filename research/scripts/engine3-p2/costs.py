"""Cost-model arithmetic [N] for the best designs (final_best.json): per-point log2 cost
  log2 C_q + (#rows) log2(#values per row) + log2(r) + s,   C_q = sum_{j<=q} 2^j C(n,j),
  q = ceil((M R + 1)/Q) - 1  (Hermite at Q points needs Q(q+1) >= MR + 1),
singleton rows take 2 values (l1 = 1).  Compared with n (brute force 2^n)."""
import json, os, math
D = os.path.dirname(os.path.abspath(__file__))
b = json.load(open(os.path.join(D, 'final_best.json')))
M = {'L3': 3, 'G3': 3, 'G4': 4}   # occurrences per variable
print("fam n r Q rho | R | q  log2C_q rows s | log2cost/pt  (n)")
for k, v in sorted(b.items(), key=lambda kv: eval(kv[0])):
    fam, n, Q, rho, r, fixed = eval(k)
    if fixed or Q not in (4, 8, 10) or v[0] == 99: continue
    R = v[0]; Mo = M[fam] * n; s = n // r
    q = max(0, math.ceil((Mo * R + 1) / Q) - 1)
    Cq = sum(2**j * math.comb(n, j) for j in range(min(q, n) + 1))
    rows = r * rho
    lc = math.log2(Cq) + rows + math.log2(r) + s
    print(f"{fam} {n} {r} {Q:2d} {rho} | {R} | {q:3d} {math.log2(Cq):6.1f} {rows:3d} {s} | {lc:6.1f} ({n})")
