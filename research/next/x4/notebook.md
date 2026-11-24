# x4 notebook: a third merge for the counting engine (target ρ = 1/√3 on a squaring level)

24 Nov 2026. Tags: [R] proved here, [K] known/cited, [N] computed, [C] conjecture/heuristic.
Inputs: `engine3-STATUS.md`, `engine3-open-door.md` §1.6–1.7, 2.3–2.7, `vpvnp/b2/notebook.md`, `pieces.md`,
ETH paper App. B (Fock/Heisenberg form), VP≠VNP paper App. B (free-fermion determinant form, Prop. B.2),
`next/ideas-dichotomy.md` Ideas 1 and 5.

## 0. Status (final)

**Bottom line.** No three-merge family with ρ < 1/√2 was constructed; no exponent improvement. Findings:
(i) [R] coordinate grids cannot help (α′ ≤ 1 always; 1/2 at the flat floor for plane merges), §2;
(ii) [R] the "sphere law" (single A₂/three-flavour quadratic conservation, Idea 5 / Route 1 as stated) is refuted
unconditionally on the three-wire cube B3 by a segment price b = (1,1,3), |b|² = 11 > 9, §4;
(iii) [N/C] on Δ₃ every price found (segment, star, Euclidean m ≤ 4) lies inside or *on* the sphere c_r²+c_c²+c_d² = (9λ)²,
so Δ₃ remains the right target and Route 1's surface is consistent there, §5;
(iv) the step of App. B that does not extend: the determinant/Schur-complement gives only bipartition ranks; a
three-group merge needs a triangle (trace) factorization, §8; (v) "charge sectors" of a product basis never trade.

## 0′. Early status

- Two-merge mechanism understood and restated as one principle (§1): **one grading X, two cuts, complementary
  by reflection X ↦ 1/X**; the √ comes from ln P(E) ~ κ√E with additive energy.
- **[R] Coordinate grids never pass 1/log K (§2).** For the d-dimensional grid, any merges of the form
  "fix a set S of coordinates" (planes, lines, ...), and the 2^d-box configurations, a single flattening shows
  ρ ≥ |S|/d = 1/β, so α′ = log(1/ρ)/log β ≤ 1. Plane merges in 3D (β = 3) at the flat floor 1/√3 give
  α′ = log√3/log 3 = 1/2: **no gain over App. B**, even if the floor were attained. So the "3D grid with
  three axis merges" is dead as an engine level; only AG(2,q)-type levels (β = 2, Δ₃-type configurations) remain.
- §3: Δ₃ in coordinates: nodes = {α+β+γ = 0} ⊂ Z₃³, edges n → n+(1,1,1), merges = the three coordinate
  projections; the rectangle is Z₂² with n ~ n+(1,1). "Balanced" instances (edges per bond = p) are exactly
  the ones where the flat floor equals the "Fock-fused" bond weight: rectangle (p = 2) and Δ₃ (p = 3).
- §4: where the third merge breaks (obstruction, precise form below).

## 1. How App. B reaches 1/√2 (the mechanism, both versions) [K, restated]

**Fock form (ETH paper App. B).** V = Q[t₁,t₂,…] graded by weight, dim V_E = p(E), log p(E) ≈ c√E. Operators
a[r] : V_E → V_{E+r} (Heisenberg modes). Strings: x, v label operators of weight h (a_x, b_v), y, u label states
of weight h; λ = log p(h) ≈ c√h. The piece A_s = ⟨u| Q_s(a_x, b_v) |y⟩ with
Q_s = Σ_{i=0}^{2h} (−1)^i C(H,i) a[s−h+i] b[h−s−i] — and **locality** (Lemma 9(a)): the same Q_s is the sum with
the two operators exchanged. Order b·a factors (x,y)|(u,v) (row) through a_x[·]|y⟩ ∈ V_{s+i}; order a·b factors
(x,u)|(y,v) (column) through b_v[·]|y⟩ ∈ V_{2h−s−i}. Σ_s Q_s = (a[−h]b)·Id gives Σ A_s = h![x=v][y=u] (Lemma 10).

**Determinant form (VP paper Prop. B.2).** Ψ(X) = det M(X), M a matrix over Z[X] indexed by the levels of four
Frobenius symbols (one per party), D = diag(X^{2r+1}) the level propagator.
- At X = 1 the determinant is the crossing.
- Small X: the off-pair blocks are ≡ F·D·G mod X^{2R} (F on {a,d}, G on {b,c}) by the truncated Meixner
  orthogonality (B.1); a Schur complement expands the coefficient of X^N over level sets T of energy ≤ N:
  rank_{ad|bc} Ψ_N ≤ (N+1)P(N).
- Reflection X ↦ 1/X with a rescaling exchanges b and d: X^Θ Ψ(1/X) = Ψ(X) with b↔d, Θ = 2(e₁+e₂). Hence
  rank_{ab|cd} Ψ_N ≤ (N′+1)P(N′), N′ = Θ − N.

**One principle.** Pieces Ψ_N with cut energies (N, Θ−N), cost κ√(energy) per cut. The worst piece is N = Θ/2:
c_row + c_col = 2κ√(e₁+e₂) = 2‖(λ₁,λ₂)‖₂. Each single Fock term would cost only √(s+i)+√(2h−s−i) ≤ 2√h (ρ = 1/2);
the spread over i (equivalently the degree Θ) is what costs the √2, and b2 shows it is forced under PH.

**Accounting (STATUS / Def. 7).** |I| = Θ+1 = poly(λ), so naming is o(λ); E = 2, raw 2λ per merge;
c_row + c_col ≤ 2√2 λ + O(log λ) ⇒ ρ = 1/√2, α′ = 1/2 with squaring (K → K²·polylog).

## 2. Grids of higher dimension: β kills the gain [R]

Level: nodes [g]^d, K = g^d. Merge M_S (S ⊂ [d], |S| = s): group = nodes agreeing on the coordinates in S; g^s
groups, so the merged instance has K^{s/d} nodes, **β = d/s**. Configurations: boxes {a_i, a_i′}^d with their
2^{d−1} long diagonals (n ~ n̄); all but an O(d/g) fraction of edges are long diagonals of exactly one box.

**Claim.** For any set of merges M_{S_1},…,M_{S_p} with |S_k| = s, every identity on the box has game value
V ≥ (s/d)·Eλ − o(λ). Hence ρ ≥ 1/β and α′ ≤ 1.

*Proof.* For a coordinate l, the cut {c_l = 0 | c_l = 1} is a union of groups of M_S whenever l ∈ S, and every long
diagonal crosses it, so rank across it of f_C is N^E. Cut bound + pigeonhole: some piece has c_k ≥ Eλ − log|I| for
every k with l ∈ S_k. Adversary mixes these pieces with weight 1/d on each l: every merge k gets
≥ (|S_k|/d)Eλ − o(λ). ∎

Instances: plane merges in 3D (s = 1, β = 3): ρ ≥ 1/3 (pigeonhole), ≥ 1/√3 under FH (b2 Thm 3 applies: two groups
per merge, every edge crosses every merge), so α′ ≤ log₂√3/log₂3 = **1/2 exactly — App. B's value**. Line merges in
3D (s = 2, β = 3/2): ρ ≥ 2/3 unconditionally, α′ ≤ 1. Checked by hand: the 1D far-leg price on the line-merge box
gives Σ_k b_k = 8 = (4,4,0) (a cut metric, i.e. the flattening above).
**Corollary.** On coordinate grids "more merges" and "smaller β" exactly cancel. The flat floor 1/√p can beat the
engine only at β = 2 with p ≥ 3, i.e. AG(2,q)-type levels (Latin-square merges), which is Δ₃/Δ_q.

## 3. Δ₃ in coordinates, and "balanced" configurations [R]

Write a node of the 3×3 grid as n = (α,β,γ) ∈ Z₃³ with α+β+γ = 0 (α = row, β = −column, γ = column−row). The
anti-diagonal triangles are the cosets of ⟨(1,1,1)⟩, and each edge goes n → n+(1,1,1): under each merge (coordinate
projection) it goes from group g to g+1. Each node holds an out-string and an in-string. Under merge k the bond
(g, g+1) carries the 3 edges whose start has k-th coordinate g. The rectangle is the same picture for Z₂² with
n ~ n+(1,1) and two merges.

Flat floor per bond: (edges on bond)·λ/√p; in Fock units (cost κ√energy, string energy e) this is energy
(edges)²e/p. The "fused" energy (sum of the crossing strings' energies, as App. B's worst piece has: row bond
energy 2h = x and y fused) is (edges)·e. They agree iff edges-per-bond = p: **rectangle (2 = 2) and Δ₃ with three
merges (3 = 3)**. So Δ₃ is the exact three-merge analogue of the crossing, and the floor-matching target is
"every bond of every merge carries one Fock space of energy 3e" — a three-cut version of App. B.

## 4. Where a third merge breaks: the sphere law is refuted on the three-wire cube [R + N]

**The two-merge law.** App. B's pieces have cut energies (N, Θ−N), so every piece satisfies
c_row² + c_col² ≤ κ²Θ = 2(λ₁² + λ₂²) (+o), a *single quadratic conservation law* ("sphere law"). For λ₁ = λ₂ = λ the
circle has radius 2λ = Eλ. Ideas-dichotomy Idea 5 and ideas-3sat Route 1 propose the p = 3 analogue: three gradings
(an A₂ charge) with c₁² + c₂² + c₃² ≤ (Eλ)², whose balanced piece costs Eλ/√3 per merge (the flat floor).

**Test of the law against unconditional prices.** A segment (1D) price is a price over every field (b2 §3(ii)). In the
far-leg limit it yields a vector b with: *every identity has a piece with c_k ≥ λb_k − o(λ) for all k at once*. A
family obeying the sphere law needs |b|² ≤ E² for every such b. Script `lineprice_sphere.py` enumerates all 1D far-leg
prices (hubs at vertices of [0,1], all edge orientations) [N, exhaustive]:

| configuration | E | p | max \|b\|² (1D prices) | sphere E² | verdict |
|---|---|---|---|---|---|
| rectangle (App. B) | 2 | 2 | 4, at b = (0,2) | 4 | touches the circle: consistent |
| **B3 = three of the four long diagonals of the cube, plane merges** | 3 | 3 | **11, at b = (1,1,3)** | 9 | **sphere law refuted** |
| box (all four long diagonals) | 4 | 3 | 16 at (0,0,4); max Σb = 6 at (2,2,2) | 16 | touches |
| Δ₃ (rows, cols, diags) | 9 | 3 | 48 at (4,4,4) (the flattening floor) | 81 | not refuted |

**Proposition 4.1 [R, from b2's segment prices].** For B3 (wires 000–111, 100–011, 010–101; merges = the three
coordinate cuts) every identity has a piece with cost vector ≥ (λ, λ, 3λ) − o(λ) up to permuting merges; hence no family
of pieces has all cost vectors in the ball c₁² + c₂² + c₃² ≤ (3λ)² + o(λ²). In particular no "three-flavour" grading with
a single quadratic conservation law (Idea 5 / Route 1 as literally stated) exists on B3, over any field.
*Hand check.* Hubs of every merge at 0 (side containing 000) and 1; orient all three wires from the 000-side end. The
displacements are (1,1,1), (−1,1,1), (1,−1,1); with u_e = +1, b = (1,1,3). ∎
The bound is attained [N]: at N₀ = 2 the alternating-projection search (`ap_search.py b3 2 '8,2,2;2,8,2;2,2,8'`) finds
three pieces with cut ranks (8,2,2), (2,8,2), (2,2,8), i.e. bit costs (3,1,1) and rotations — exactly b. (Also two
pieces of ranks (4,4,4) each exist.) Neither trades after naming (ρ ≥ 1 with ν log T), as expected at N₀ = 2.
Also unconditional for B3: mixing the three rotations of b gives **ρ_B3 ≥ 5/9 > 1/2** (and ≥ 2/3 under PH, §5).

**What exactly fails.** In two dimensions the cut-metric (flattening) vector (0, 2) lies *on* the Pythagorean circle;
this is the precise sense in which "one charge" suffices: the flattening corner and the Fock rotation agree. With three
cuts the flattening corner (1,1,3) lies *outside* the sphere |c| = Eλ (11 > 9). So a three-merge family cannot be
spherical; at best its cost surface is a non-quadratic surface through (√3,√3,√3)λ that also dominates the corners
(1,1,3)λ. A grading by a single A₂ charge with energy additivity w₁ + w₂ + w₃ = const produces a sphere, hence is
impossible on B3. This is a statement about cost vectors, independent of the algebra used.

**Δ₃ escapes this test.** On Δ₃ the corners are (4,4,4) (segment prices, |b|² = 48) and (9,0,0) (star price,
Theorem 1; |b|² = 81, on the sphere). So the A₂ sphere law c_r² + c_c² + c_d² ≤ (9λ)² is *not* refuted by any
unconditional price I know; Δ₃ (three bonds per merge) behaves like the rectangle, B3 (one bond per merge) does not.
Euclidean prices: see §5.

**A second, independent obstruction for "charge sectors" [R, = STATUS Theorem 2].** If the pieces are sub-sums of the
expansion of the wire product in a product basis (f = Σ_μ Π_w e_{μ_w}(x_w)e*_{μ_w}(x_w′), e.g. occupation-number or
Fourier/character bases, grouped by a charge), then for any cut that separates the two ends of every wire the side
restrictions of distinct terms are linearly independent, so every cut rank equals the number of terms: no trade at
all (ρ = 1). App. B's A_s are *not* sectors of f: they are coefficients of an interpolating determinant
(Ψ(1) = f, Ψ_N ≠ f|_sector). So Route 1's "charge-s sector of the wire product" cannot even reproduce the
calibration; the charge must live on the interpolation variable (X in Prop. B.2), not on the basis.

## 5. Euclidean prices and the sphere on Δ₃ [N, heuristic optimisation]

`euclid_sphere.py` / `euclid_sphere_d3.py`: SLSQP over far-leg Euclidean prices in ℝ^m (hub distances ≤ 1 per merge,
u_e unit, b ≥ 0), maximising |b|². Results are filled in below when the runs finish. Reference points: b2's planar
equilateral price gives b = (3√3,3√3,3√3), |b|² = 81 = E²: **the extremal price lies exactly on the A₂ sphere**, as on
the rectangle (App. B's worst piece (√2,√2)λ and the flattening corner (0,2)λ are both on the circle).

**Δ₃ [N]** (`euclid_d3.out`, 12 SLSQP restarts each): max |b|² = 81.000 for m = 2, 3, 4, attained at (0,0,9), (0,9,0)
and at the non-corner point (0.450, 0.481, 8.976) (|b|² = 81.00). Every local optimum lands **on** the sphere |b| = 9,
none outside. Together with §4: segment prices inside (48), star prices on (81), Euclidean prices on (81).
**[C] On Δ₃ the Euclidean price envelope is exactly the A₂ sphere c_r² + c_c² + c_d² = (9λ)²**, as the circle is for
the rectangle. So Route 1's target surface is consistent with every price known, conditional or not, and b2's floor
1/√3 is the balanced point of that sphere. Δ₃ is the right instance; B3 is not (§4).

**B3 [N]** (`euclid_b3.out`, m = 2, 4, 6): max |b|² = 12 at b = (2,2,2) (planar already). So on B3 even the *sum*
Σ_k b_k = 6 exceeds the Theorem-3 value 3√3 ≈ 5.196: **ρ_B3 ≥ 2/3 under PH**, b2's orthogonal construction is not
optimal there, and B3 is far from the sphere (12 > 9 and the unconditional 11 > 9). Contrast Δ₃, where b2's 9√3 and
the sphere both survive every search.

## 6. Task 3: ALS / feasibility searches [N]

- Δ₃ at N₀ = 4 has 4¹⁸ ≈ 6.9·10¹⁰ entries (N₀ = 8: 8¹⁸): dense ALS as in `engine3-delta3-3m/als3.py` is impossible;
  only N₀ = 2 (done before, residuals ≥ 0.63) is feasible. I did not rerun it.
- B3 (6 strings) is the smallest three-cut crossing and is searchable: `ap_search.py` (alternating projections onto
  "Σ = f" and onto cut-rank sets). Calibration: rectangle N₀ = 2 App. H profile (4,1),(1,4) found to 10⁻¹³; rectangle
  N₀ = 4 (tensor square of App. H, profile (16,1),(4,4),(4,4),(1,16)) **not** found (best residual 0.11 after
  8×4000 sweeps). So the solver is unreliable from N₀ = 4 on, and I did not report N₀ = 4, 8 searches for B3 as
  evidence. At N₀ = 2: (8,2,2)+rotations found (= the segment-price corner, so optimal for that shape); (4,4,4)×2 found;
  (8,1,1)+rotations not found (residual 0.71; it is excluded by Prop. 4.1, consistent).
- Seeding by "the two-merge construction" is not meaningful at fixed N₀: App. B is not a tensor power of fixed types
  (its pieces need P(N) ~ 2^{κ√N} with N → ∞), and at N₀ ≤ 8 Fock spaces have dimension ≤ 7 per weight. The
  fixed-N₀ accounting (naming ν log T per block) cannot exhibit any Fock gain at these sizes.

## 7. Task 4: what any ρ would give end to end [R, from K]

- Level: AG(2,q), merges rows/cols/diagonals, β = 2 (K → K², open-door §2.7). α′ = log₂(1/ρ_level), and
  ρ_level → ρ_C if every non-merge parallel class is covered by configurations with parameter ρ_C. Δ₃ covers only
  one class, and only for q = 3^k (direction (1,−1); the copies are the subgrids {r+ia}×{c+ja}, i,j ∈ Z₃, whose
  anti-diagonal triangles are cosets of {0,a,2a}(1,−1), which needs 3a = 0; they partition that class); the other q − 3 classes need Δ_q (or other) pieces with the same ρ, or they drag ρ_level up.
- #3-SAT time from Theorem A's arithmetic: 2^{O(n/(log n)^{α′})}. ρ = 1/√2 → α′ = 1/2 (both labs' current record);
  ρ = 1/√3 → α′ = 0.792; any ρ < 1/√2 strictly improves. Overheads: the D1 triangle-network cost and the hyperedge
  naming ν₃ = 3/2 enter only as o(λ) for poly(λ) pieces, so a Fock-type family (poly(λ) pieces) would plug in with the
  same overheads as App. B; a fixed-N₀ type family pays ν₃ log T per block (open-door §1.7).
- **Achieved here: nothing below 1/√2.** So no new exponent. The grid results of §2 show that changing the level
  geometry instead (3D grids, plane or line merges) cannot help either: α′ ≤ 1 always, and = 1/2 at the flat floor for
  plane merges.

## 8. The construction attempt for Δ₃, written as requirements (Task 1) [R for the reductions, C for existence]

What Prop. B.2's proof uses, and what a three-merge version must supply:
1. **Interpolation.** A matrix M over Laurent polynomials in (X₁, X₂, X₃), X₁X₂X₃ = 1, with det M = f at X = (1,1,1).
   (B.2: X = 1 kills the (y − 1) entries and leaves a block-triangular matrix.)
2. **One frame per merge.** For each k a monomial gauge after which M is a polynomial in X_k (other variables as
   bounded-support Laurent coefficients) and every block between parties in different k-groups is ≡ F·D(X_k)·G mod
   X_k^{2R} with D = diag(X_k^{2r+1}). Then the Schur-complement expansion bounds the coefficient of X^N by
   poly·P(N_k) across each bipartition (k-group | rest); the extra splits of the other exponents cost only poly(λ)
   because the support is bounded. (I checked this step: it goes through verbatim with spectator variables.)
3. **Complementarity.** In B.2, frame 2 is frame 1 composed with X ↦ 1/X (the involution b ↔ d), so N_col = Θ − N_row
   comes for free. For Δ₃ one needs the cyclic symmetry (α,β,γ) ↦ (β,γ,α) of §3 to act by X_k ↦ X_{k+1}, giving
   N₁ + N₂ + N₃ = Θ′ with Θ′ = 27e (bond energy 3e each, §3). This is exactly the A₂ grading of Route 1.
4. **Three groups per merge.** Step 2 controls only the three bipartition ranks rk(R_g | rest). The D1 cost needs a
   triangle network; ½Σ_g log rk(R_g | rest) is a lower bound for it, not an upper bound. A three-group version of the
   Schur complement (eliminate the R_g blocks one at a time, each step factoring through D(X_k)) would give a path
   network R₀–R₁–R₂, whose bond (R₀R₁) carries the levels of 6 strings, not 3. Accounting: if such a path piece carried
   only the fused energy 6e per bond it would cost 2κ√(6e) = 2√6λ ≈ 4.90λ < 3√3λ, below the flat floor, so under FH a
   path version must carry more energy than fused; the triangle network with bond energies 3e each is what the floor
   requires. **This is the step I could not extend**: the determinant gives two-sided factorizations (bipartitions),
   and a triangle network needs three pairwise propagators D(X_k) between the three groups with the cyclic
   consistency Tr(D₀₁D₁₂D₂₀) — a "torus" (trace) version of the expansion, not a Schur complement.
5. **Precise obstructions recorded.** (a) Sphere law impossible on B3 (Prop. 4.1, unconditional). (b) Charge sectors
   of a product basis never trade (STATUS Thm 2). (c) Bipartition-only control is insufficient for r = 3 groups
   (step 4). None of these excludes Δ₃: its price envelope is the sphere (§5).
