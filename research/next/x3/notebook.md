# x3 notebook: hunting a √D-shortening of C_{D,m}

24 Nov 2026. Tags: [R] proved here, [K] known/cited, [N] computed, [C] conjecture. (Work in progress; sections fill in below.)

## 1. Definitions pinned down ([O] §2, Def. 2.1; [A] via two-proofs.md Prop. 1)

- **Bit tensor network.** Nodes with arbitrary local tables over a field K (algebraically closed of the given
  characteristic; exact identities may be reduced to a finite field/number field). Ports are bits. A *cable of width b*
  joins b port pairs (index dimension 2^b; widths are positive integers). Contraction = sum over joined bits.
- **Placement and cost.** Nodes are placed at points of the closed Euclidean unit ball B^D. Cost = Σ_cables width × Euclidean
  length, including the run from a node to an external terminal. Local reblocking at one point is free.
- **C_{D,m}.** 2D terminals at ±e_i, each carrying m bits (dimension n = 2^m). C_{D,m} = ⊗_{i≤D} I_n(e_i, −e_i): D identity
  wires of width m on the coordinate diameters. As a 2D-party tensor it has (2^m)^{2D} entries. Direct cost **2Dm**.
- **Shortening.** C_{D,m} = Σ_{a≤A} N_a, each N_a a network in the ball with cost ≤ w.
  - [O] strict shortening: w + 2D·log₂A < 2Dm.
  - [A]-side √D-shortening (two-proofs Cor. 1′): w + 2√D·log₂A < 2Dm. Proves Contracting.
  - Closure is allowed (fixed layouts, variable tables, Zariski closure; [O] converts it to an exact identity at the t-th tensor
    power with poly(t)·A^t terms of cost tw). So effectively the target is asymptotic: what matters is the
    **saving ratio σ = (2Dm − w)/log₂A**; need σ > 2√D ([A]) or σ > 2D ([O]).

### Smallest instances (explicit)
| (D,m) | tensor | entries | direct cost | √D target w < | [O] target w < |
|---|---|---|---|---|---|
| (2,1) | δ(x₁,x₁')δ(x₂,x₂'), 2×2×2×2 | 16 | 4 | 4 − 2.828·log A | 4 − 4 log A |
| (2,2) | same with x ∈ {0..3} | 256 | 8 | 8 − 2.828·log A | 8 − 4 log A |
| (3,1) | three qubit Bell pairs on 6 terminals | 64 | 6 | 6 − 3.464·log A | 6 − 6 log A |
| (3,2) | three 4-dim identity wires | 4096 | 12 | 12 − 3.464·log A | 12 − 6 log A |

A = 1 is always impossible: Crofton (random hyperplanes) + flattening rank ≤ 2^{crossing width} gives w ≥ 2Dm [R].

## 2. Verdict (short)

1. **No √D-shortening found.** Every candidate sits at or below the threshold; best explicit exact identity is Kauffman's skein
   relation, σ = 4 − 2√2 ≈ 1.17 per selector bit against the needed 2√2 ≈ 2.83 (D = 2).
2. **Engine pieces sit exactly on the threshold [R].** A two-hub network whose bond across the hub cut is β·m bits costs
   m·√2(β + √(4−β²)) on C_{2,m} (and m·[2√(1−1/D)√(D²−β²) + 2β/√D] for the D-dimensional half/half hub cut). This equals the direct
   cost 2Dm exactly at **β = √D** and is smaller for every β < √D. The engine/App. B crossing pieces have
   c_row = c_col = √2λ (ρ = 1/√2) with 2^{o(λ)} pieces, i.e. β = √2 = √D: first-order saving exactly zero. b2's flat floor
   (some piece has every merge cost ≥ Eλ/√p) is the same number. **So any improvement must come from a crossing family with
   min(c_row, c_col) ≤ (√2 − δ)λ, i.e. ρ_× < 1/√2;** with 2^{o(m)} pieces such a family wins for both thresholds (saving
   ≈ 0.875(√2−β)²m, table §5).
3. **Certificates (exact identities, D = 2) [R+N].** (2,1), (2,2), (2,3) are excluded for every A; (2,4) is open only for A ∈ {2,3}
   (√D target) and the [O] target is excluded for all m ≤ 5 (table §3). Asymptotically the only unconditional certificate is the
   line price, w ≥ √2(Dm − log A), which leaves a window whenever log A < (2−√2)Dm/(2√D−√2).
4. **The D = 2, A = 2 problem is a clean matrix question [R]:** SWAP_n = R + L with opSR(R) ≤ r, rank(L) ≤ s. Proven: r + s ≥ n.
   Numerics: min max(r,s) = 1, 3, 4, ≈7 for n = 2..5, consistent with ⌈n²/4⌉ [C], i.e. log r ≈ 2m − 2, far above the √2·m that a
   shortening needs. So two-term identities of hub type give nothing; FH would only predict ≥ √2m − O(√m).

## 3. Lower-bound certificates

**(i) A = 1 [R].** Crofton: cost = ½∫ Σ width·|⟨u,edge⟩| over random lines/hyperplanes; flattening rank across a hyperplane ≤
2^{crossing width}. Integrating gives w ≥ 2Dm. (Holds over every field.)

**(ii) Line price [R from K].** By b2 (§3(ii)), every finite subset of ℝ is a price over every field. Pull back along a 1-Lipschitz
f: B^D → ℝ with f(e_i) = 1/√2, f(−e_i) = −1/√2 (1-Lipschitz on P since |e_i − (−e_j)| = √2, extend by McShane). GHZ naming cost on a
line = span = √2. Gives **m·D√2 ≤ √2·log A + w** for any A-term identity. This is the best f with these values (for D=2, summing
the cross constraints gives Σ|Δf| ≤ D√2).
Window vs the √D target: nonempty iff log₂A < (2−√2)Dm/(2√D−√2): D=2: 0.83m; D=3: 0.86m. Vs [O]: log₂A < (2−√2)Dm/(2D−√2):
D=2: 0.45m.

**(iii) Exact identities, D = 2, per-network (code/cert_d2.py) [R].** For each network: integer min-cut widths k₁ (cut {e1,e2}|{−e1,−e2})
and k₂ (cut {e1,−e2}|{−e1,e2}). Crofton over all lines in the disc + min-cut gives cost ≥ (2−√2)(k₁+k₂) + 2(√2−1)·max(k₁,k₂).
Constraints: Σ_a 2^{k₁(a)} ≥ 4^m and Σ_a 2^{k₂(a)} ≥ 4^m (flattening subadditivity), and Σ_a min(2^{k₁(a)}, 2^{k₂(a)}) ≥ 2^m (SWAP lemma, §4).

| m | √D target (w < 4m − 2.83 log A) | [O] target (w < 4m − 4 log A) |
|---|---|---|
| 1, 2, 3 | excluded, all A | excluded, all A |
| 4 | open for A = 2, 3 only | excluded |
| 5 | open A ≤ 5 | excluded |
| 6 | open A ≤ 7 | open A ≤ 3 |

Smallest open instance: **(D,m,A) = (2,4,2)**, target w < 13.17, only surviving profile (k₁,k₂) = (3,8)+(8,3). That profile forces
SWAP₁₆ = R + L with r, s ≤ 8 (lemma allows it: 8+8 = 16). The two-hub realisation of bond 3 costs √2(0.75+√3.4375)·4 = 14.73 > 13.17,
so even a solution would need a better-than-hub layout. Numerics (§4) say r = s = 8 is far from possible at n = 16.
(m=3, A=2 needed SWAP₈ = R + L with r, s ≤ 2: excluded by r+s ≥ n.)

## 4. The two-term problem for D = 2

**Reduction [R].** A network N with cut-2 rank r is N = Σ_{b≤r} X_b(e1,−e2) ⊗ Y_b(−e1,e2), which in the cut-1 view ((e1,e2) → (−e1,−e2))
is (Σ X_b ⊗ Y_bᵀ)·SWAP. So C = Σ_a N_a with networks split into "cut-2-cheap" and "cut-1-cheap" ones is exactly
SWAP = R + L, opSR(R) ≤ Σ r_a, rank(L) ≤ Σ s_a.

**Lemma (r + s ≥ n) [R].** If SWAP = R + L, then for x ≠ 0 the space Y_x = {y : x⊗y ∈ ker L} has dim ≥ n − s, and for y ∈ Y_x,
y⊗x = R(x⊗y) = Σ_b X_b x ⊗ Y_b y ∈ span{X_b x} ⊗ ℂⁿ, so Y_x ⊆ span{X_b x}: n − s ≤ r. ∎ Corollary: for any identity
I = Σ_a N_a, Σ_a min(r_a, s_a) ≥ n.

**Lemma′ (E⊗F version) [R].** If E ⊗ F ⊆ ker L then R restricted to E⊗F is the swap E⊗F → F⊗E, whose operator-Schmidt rank is
dim E·dim F; restriction does not raise opSR, so r ≥ dim E·dim F. Taking dim F = f and E = ∩_c (W_c F)^⊥ (W_c spanning (ker L)^⊥ as
bilinear forms) gives **r ≥ max_f f(n − s f) ≥ n²/(4s)**, and by realignment duality s ≥ n²/(4r). In particular s = 1 forces
r ≥ n²/4. Balanced, this still only gives max(r,s) ≥ n/2, i.e. log ≥ m − 1, whereas a shortening needs ≤ (√2 − δ)m and the
numerics say ≈ 2m − 2. The window β = log r/m ∈ [1, √2) is the unproven part.

**Kauffman (n = 2) [R, exact, code/verify_kauffman.py]:** SWAP = I⊗I − 2ψ⁻ψ⁻ᵀ, i.e. C_{2,1} = (crossed pairing) + (ε⊗ε),
both terms of cost 2√2. Exact over ℤ, so over every field. σ = 1.17.

**Frontier (alternating projections, code/swap_split.py, frontier4.py, diag.py) [N]:** minimal s for given r
- n = 2: (1,1).  n = 3: (1,3), (2,3), (3,1).  n = 4: (1,6), (3,5), (4,4), (5,3), (6,1) (all residual < 1e−13).
- min max(r,s): n=2: 1, n=3: 3, n=4: 4, n=5: 7 (r=s=6: residual 1.8e−2; 7: 4e−4, slow convergence).
- Endpoints (1, C(n,2)) = I⊗I − 2P_anti and its realignment dual. [C] min max(r,s) = ⌈n²/4⌉, equivalently log r ≈ 2m − 2.

**The SWAP problem, stated cleanly [open].** Over an algebraically closed field, let S_n ∈ End(ℂⁿ⊗ℂⁿ) be the swap. Define
F(n) = min{max(r,s) : S_n = R + L, opSR(R) ≤ r, rank(L) ≤ s} (opSR = rank of the realignment; the problem is self-dual under
realignment, which fixes S_n and exchanges opSR and rank). Proven: r + s ≥ n and r·s ≥ n²/4 up to rounding (Lemmas), so F(n) ≥ n/2.
Numerics: F(2)=1, F(3)=3, F(4)=4, F(5)≈7 (alternating projections; r=s=6 stalls at 1.8e−2, r=s=7 reaches 4e−4 with slow convergence;
L-BFGS confirmed (4,4) at n=4 to 7e−15; runs at n ≥ 6 were stopped for time). [C] F(n) = ⌈n²/4⌉.
**Consequence:** a two-hub A = 2 √D-shortening of C_{2,m} exists iff F(2^m) ≤ 2^{βm} for some β < √2 with m·[4 − √2(β+√(4−β²))] > 2√2.
The proven bound only excludes β < 1.

**More terms (A = 3, 4).** If every term is "pure" (cheap across one diagonal cut), the terms add to a single split S_n = R + L with
r = Σ r_a, s = Σ s_a. So more terms never help on the matrix side and only add selector cost. Mixed terms (both cut ranks large) are
excluded by Crofton at A = 2: a term full on both cuts costs ≥ 4m − 2, a saving ≤ 2 < 2√2. For A = 3, 4 the certificate table (§3)
already covers m ≤ 4–5. So the picture does not change.

## 5. Candidates against the target (σ = saving per selector bit; need σ > 2√D, or > 2D for [O])

| candidate | instance | A | w | σ | verdict |
|---|---|---|---|---|---|
| product (rank) decompositions, incl. asymptotic rank / Zhou-type K_n results | any D | ≥ 2^{Dm} (flattening e_i vs −e_i) | 0 | ≤ 2 | below 2√D for D ≥ 2 [R] |
| cut k diameters, keep the rest | any | 2^{km} | 2(D−k)m | 2 | below [R] |
| Kauffman skein (exact, every field) | (2,1) | 2 | 2√2 | 1.17 | below [R,N] |
| entanglement swapping (Bell/Clifford, F₂) | (2,1) | 4 | 2√2 | 0.59 | below [R] |
| fast matrix multiplication (triangle grouping of C_{3,m}: parties {e1,−e3},{−e1,e2},{−e2,e3}) | (3,m) | n^ω | 3√2·m | (6−3√2)/ω ≤ 0.88 | below; dropped per x2 [R] |
| two-hub split S_n = R + L, A = 2 | (2,m) | 2 | √2(β+√(4−β²))m | needs β < √2 | numerics β ≈ 2 [N] |
| engine/App. B crossing pieces, ρ = 1/√2 | (2,m) | 2^{o(m)} | 4m − o(m) | 0 to first order | exactly on threshold [R] |

**Hub vocabulary for a sub-additive (x5 "β < 4") family.** I have not checked x5's normalisation. In this notebook's terms a winning
family is: 2^{o(m)} pieces summing to C_{2,m}, each a two-hub network (hubs at ±t(1,−1)/√2 holding {e1,−e2} | {−e1,e2}, or the
rotated pair) whose bond across its hub cut is b = β_h·m bits with **β_h < √2**. Its cost is √2(β_h + √(4−β_h²))·m < 4m, which beats
both thresholds once m is large. Degree = total energy (x5's β = 4) corresponds to c_row + c_col = 2√2λ with min(c_row, c_col) = √2λ,
i.e. β_h = √2: the hub sits at t = 0 and saves nothing. Any strict sub-additivity that lowers min(c_row, c_col) below √2λ moves the
optimal hub off the origin and gives a linear saving 4 − 2√2(ρ+√(1−ρ²)) per m, with ρ = β_h/2.
For general D the half/half hub cut has break-even bond √D·m, cost m[2√(1−1/D)√(D²−β²) + 2β/√D], which is b2's 1/√p again.

## 6. Conclusion

No identity found. The prize is equivalent, in the hub vocabulary, to beating bond √D·m with subexponentially many pieces. For
A = 2, D = 2 it is equivalent to F(2^m) ≤ 2^{(√2−δ)m}. Proven F(n) ≥ n/2, numerics suggest F(n) ≈ n²/4. Small instances
(2,1)–(2,3) are excluded unconditionally, and (2,4) is open only for A ≤ 3.

Code: code/{verify_kauffman.py (exact checker), cert_d2.py (certificate table), hub_cost.py, swap_split.py, frontier4.py,
diag.py, probe.py, lbfgs_split.py}, outputs diag.out, lbfgs.out.
