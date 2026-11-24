# x4 notebook: a third merge for the counting engine (target ρ = 1/√3 on a squaring level)

24 Nov 2026. Tags: [R] proved here, [K] known/cited, [N] computed, [C] conjecture/heuristic.
Inputs: `engine3-STATUS.md`, `engine3-open-door.md` §1.6–1.7, 2.3–2.7, `vpvnp/b2/notebook.md`, `pieces.md`,
ETH paper App. B (Fock/Heisenberg form), VP≠VNP paper App. B (free-fermion determinant form, Prop. B.2),
`next/ideas-dichotomy.md` Ideas 1 and 5.

## 0. Status (early report, updated at the end)

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
