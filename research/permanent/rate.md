# Where the 1/√log comes from, and whether α > 1/2 is possible in Anthropic's framework

Date 28 Oct 2026. Workspace `/home/user/anth-build` (Lean v4.33.1); Lean paths are relative to `proof/`.
Paper text: `/tmp/claude-0/-home-user-lean-code/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/anth/fm/paper.txt`
(Definitions 1–4 and Lemma 1 at l.755–889, Prop. 3 at l.989, Def. 7/Lemma 8/Theorem A at l.1510–1720,
Appendix B at l.1723–2016, Appendix H at l.2837–3013). Earlier notes: `research/pieces.md` (the pieces as a
tensor/sum-of-squares problem), `research/permanent/anthropic-m-independence.md` (how U enters).
Tags: **[R]** rigorous (checked against the Lean statements or a short calculation), **[C]** heuristic.

## 0. Summary

* **The exponent is α' = log₂(1/ρ), not "√" of anything.** The recursion of Theorem A squares the clique
  size at every level (K_{ℓ+1} = g_ℓ² ≥ K_ℓ²) and multiplies the exponent e by ρ (plus negligible
  terms). So after ℓ levels log K_ℓ ≈ 2^ℓ·const and e_ℓ ≈ ρ^ℓ = (2^ℓ)^{−log₂(1/ρ)} = (log K_ℓ)^{−α'}.
  With ρ = 1/√2, α' = 1/2. The depth is log log K, not √log K; each level saves the constant factor
  ρ; the "√" is 2^{−1/2}. Lean: `Levels.Gen.K`, `Levels.Gen.e` (`statements/LevelsStatement.lean`),
  `GeneralPieces.PartA.rho_pow_eq` / `rho_pow_le` (`rates/GeneralPieces/Num/PartA.lean` l.241–265),
  `GeneralPieces.Num.Asymptotic.alpha_half` (log₂(1/(1/√2)) = 1/2).
* **ρ = 1/√2 is the "doubling ratio" of the partition function.** A piece A_s passes row-wise through
  the weight spaces V_{s+i}, i = 0..2h, and column-wise through V_{2h−s−i}; the factorization cost is
  the *max* over i, i.e. log p(2h+s) + log p(2h−s) with log p(E) ≈ c_HR√E, while a label has
  λ = log p(h) bits. So c^row_s + c^col_s ≤ c_HR(√(2h+s) + √(2h−s)) ≤ 2c_HR√(2h) = 2√2·λ = 4ρλ.
  In general ρ = f(2h)/(2f(h)) where f(E) = log dim V_E; for f = E^β this is 2^{β−1}, so **α' = 1 − β**.
  The paper says so itself (App. H, l.2995–2997). Lean: `AppHalfPieces.Rrow`/`Rcol`
  (`statements/AppHalfPiecesStatement.lean` l.207–210), `ClauseBound.Inst.Half.Cst.caps`
  (`rates/ClauseBound/Inst/HalfIfc.lean` l.71–74, the inequality ≤ 4(1/√2)λ + c·log(2λ)), proved in
  `GeneralPieces.Half.Consts.exists_cst2` from the Hardy–Ramanujan bounds `Partitions.Bounds`
  (`statements/PartitionStatement.lean`; `ClauseBound.Part.Upper.p_le_exp`, `ClauseBound.Part.Lower.exists_le_p`).
* **Two rigid facts bound what Theorem A can ever give.** (i) Every piece needs c^row + c^col ≥ 2λ − O(log λ)
  (ρ ≥ 1/2; rank argument, `pieces.md` (2.1), also App. H l.2975–2978), so α' ≤ 1: **2^{O(U/log U)} is
  the ceiling of the framework, with any pieces.** (ii) The grid is two-dimensional, so K_{ℓ+1} ≥ K_ℓ²
  cannot be relaxed (§3.3–3.4 below): the per-level exchange rate is "square the node count, save ρ".
* **Verdict.** α' > 1/2 is *not* ruled out, and the framework needs exactly one new theorem: pieces with
  ρ < 1/√2 (`PiecesCounted.IsPieces ρ c D Alg` for some ρ < 1/√2 in place of `PiecesCounted.halfPieces`;
  Theorem A, `ExplicitCost.recursionSolves`, is already proved for every ρ ∈ [1/2, 1)). But: every
  construction I can analyse that follows the two-order (vertex-algebra) pattern is pinned at β = 1/2,
  and ρ → 1/2 would imply sum-of-squares formulas of size N^{1+o(1)} over ℂ (`pieces.md` (2.2)), a
  result that would kill the Hrubeš–Wigderson–Yehudayoff route to non-commutative lower bounds. So
  α = 1 is at least as hard as an open and probably false-leaning algebraic statement; α ∈ (1/2, 1)
  needs a graded "two-order" structure of growth exp(E^β), β < 1/2, which no vertex algebra has.

## 1. The bottleneck, precisely

### 1.1 The engine in three statements (all general, nothing CNF-specific)

1. **Grouping (Lemma 1 / Lemma 8).** A network on g nodes with total U (sum of shared bits, both
   ends), node length ≤ P, is evaluated by a (K, L)-clique with L = ⌈(U + 2ζgP)/K²⌉ at the price of
   2^{2gP/K}·poly per table entry. Lean: `Printed.groupingLemma`/`Printed.ComputesNetworks`
   (`statements/PrintedStatement.lean` l.149), `ExplicitCost.groupingExplicit`
   (`rates/ExplicitCost/GroupingDefs.lean` l.180, `AppRunningTime.Lof`). The grouping is *lossless* in U
   (K²L ≈ U) and only balances.
2. **One level (Prop. 3 / Theorem A(b) step).** A (g², λ)-clique is a g×g grid; its N = g⁴λ shared
   bits consist of straight edges (≈ N/g) and |R| ≈ g⁴/4 rectangles of two crossing equalities
   [x=v][y=u] (4λ bits each). Expand Π_q (Σ_i A_i) = Σ_ι Π_q A_{ι(q)}; for each ι the term is the value
   of a *row* network on g nodes (total ≈ Σ_q c^row_{ι(q)}) and of a *column* network on g nodes (total
   ≈ Σ_q c^col_{ι(q)}). Pick the smaller: min(U_row, U_col) ≤ ½(U_row + U_col) ≤ N(ρ + 1/g) + O(g⁴ log λ)
   (display (36)/(41)). Lean: `SecLevel_Grid.eqMinTotal_chain`/`eqMinTotal` (`networks/Eight/SecLevel_Grid.lean`
   l.159, l.191; ρ = 11/12) and, for general pieces, `GeneralPieces.Rec.Chain.total_eq_min`, `U_le_ubar`,
   `ubar_le_first`, `ubar_le_second` (`rates/GeneralPieces/Rec/Chain.lean` l.40–93). Then group the
   g-node network into K groups (case (ii) of Lemma 8, `GeneralPieces.Rec.Level.cases_ii`, `Lof_le_lamNext`).
3. **The schedule (Theorem A(a)).** K_0 = 2^{x₀}, g_ℓ = 2^{3ℓ+x₀}K_ℓ, K_{ℓ+1} = g_ℓ², e_0 = 1/2,
   e_{ℓ+1} = (ρ + 3·2^{−ℓ−5}) e_ℓ + 3/K_ℓ. Hence log K_ℓ = (3x₀+6)2^ℓ − 6ℓ − 2x₀ − 6 and
   ½ρ^ℓ ≤ e_ℓ ≤ 0.85ρ^ℓ ≤ 0.85((3x₀+6)/log K_ℓ)^{α'}, α' = log₂(1/ρ). Lean: `Levels.Gen.PartA`,
   `GeneralPieces.PartA.thmRunningTime_a`; at ρ = 1/√2: `PairsToBound.thetaOfThePairs`
   (`variables/PairsToBound/Pairs.lean` l.177, e_ℓ = Θ((log K_ℓ)^{−1/2})), `CountedRoute.onTheCountedRecursion`
   (e_ℓ ≤ (3x₀+6)/√log K_ℓ).

The exponent in m then is 2e_ℓ·km with K_ℓ ≈ m^{1/9}: 2^{O(km/(log m)^{α'})} (Theorem A(c), (45)).

### 1.2 The trade-off equation [R]

The one-level recurrence is e(K_{ℓ+1}) = ρ·e(K_ℓ) + o(e) with K_{ℓ+1} = K_ℓ^{2+o(1)}. Writing e as a
function of x = log K: e(2x) = ρ e(x) ⇒ e(x) = x^{log₂ ρ}. **α' = ln(1/ρ)/ln 2.** More generally a
recursion with K_{ℓ+1} = K_ℓ^{β} and saving ρ_β per level gives α' = ln(1/ρ_β)/ln β (§3.3). The two
ingredients that fix the numbers are (a) β = 2 (grid), (b) ρ = 1/√2 (pieces).

### 1.3 Why the pieces cost 1/√2 and not 1/2 [R]

Appendix B (l.1723–2016), in the operator language of App. H: V = ℚ[t₁, t₂, …] graded by weight,
dim V_E = p(E), labels x ∈ {0,1}^λ ↔ partitions μ(x) of h with p(h) ≥ 2^λ, so λ ≈ c_HR√h. For
a ∈ V_{≤h}, b ∈ V_h the operator Q_s(a,b) = Σ_{i=0}^{2h} (−1)^i C(2h,i)·a⟨i⟩[s−h+i]·b[h−s−i] on V_h:

* **Lemma 9(a)** (locality): the same sum with the two factors exchanged in *all* products at once.
* **Lemma 9(c)** + **Lemma 10**: Σ_s Q_s(a_μ, b_ν) = h!·[μ=ν]·Id (nondegenerate top pairing a[−h]b).

Piece s = ⟨e_{μ(u)}, Q_s(a_{μ(x)}, b_{μ(v)}) e_{μ(y)}⟩. In the order (a first) term i passes through
V_{s+i}; in the order (b first) through V_{2h−s−i}. Term by term the two pass-through weights add up to
2h, so **a single term costs ≈ c_HR(√w + √(2h−w)) ≤ 2c_HR√h = 2λ, i.e. ρ = 1/2**. But the row
factorization of the *piece* is the concatenation over i (R^row_s = Σ_i p(s+i) ≈ p(2h+s)) and the
column one likewise (R^col_s ≈ p(2h−s)); the maxima sit at opposite ends i = 2h and i = 0. Hence
c^row_s + c^col_s ≈ c_HR(√(2h+s) + √(2h−s)) ≤ 2c_HR√(2h) = 2√2 λ, worst at s = 0 (display (56),
`Cst.caps`). The spread H = 2h of the sum is forced: H is the locality order, and the top pole
a[−h]b must be a nondegenerate pairing on V_h × V_h, so H = wt a + wt b = 2h. Splitting the sum over i
is impossible because Lemma 9(a) is not termwise (a[r]b[−r] ≠ b[−r]a[r]). `pieces.md` §3 checked
numerically (h ≤ 6) that the true ranks equal these counts up to small factors: the √2 is sharp for
this construction.

Reading of the constant: ρ = f(2h)/(2f(h)) for f(E) = log dim V_E. Concavity of f is the whole gain
(f linear ⇒ ρ = 1, no gain); f = E^β ⇒ ρ = 2^{β−1}; f = log E ⇒ ρ → 1/2 but then |I| = 4h+1 = 2^{Θ(λ)}
pieces (§3.1 for why that kills it).

### 1.4 Side facts about the clique model [R]

* Trivial lower bound: the value depends on all K·2^{(K−1)λ} table entries, so T ≥ K2^{(K−1)λ}, i.e.
  e_K ≥ (K−1)/K² ≈ 1/K. Nothing in the query model forbids e_K = (log K)^{−1} or far less; the barrier
  is in the recursion, not the model.
* Fast matrix multiplication gives a constant e for every K: split [K] into three parts; the clique
  value is a trace of a product of three 2^{K²λ/9}-dimensional matrices, so e_K ≤ max(ω/9, 5/18) < 0.28
  (the 5/18 is for forming the matrices). The paper's base case uses e_0 = 1/2. This only improves constants.

## 2. Literature map

| where "√log"/"log" savings arise | mechanism | relation to the engine |
|---|---|---|
| Williams STOC'14 APSP n³/2^{Ω(√log n)}; Chan–Williams SODA'16 deterministic APSP, OV counting in n^{2−1/O(log c)}, #k-SAT in 2^{n−n/O(k)} [CW] | Razborov–Smolensky probabilistic polynomials: an OR of s predicates has probabilistic degree ≈ log(1/ε); sparsity s^{d} of the symmetrized polynomial balanced against 2^{d}-ish table size gives d ≈ √log n; multiplicative savings 1 − 1/polylog or 2^{−√log} *factors* | different in kind: those bounds are 2^{n(1−o(1))}/n^{2−o(1)} (polynomial savings), never 2^{o(n)}. The gadget (OR ≈ low degree) has no analogue: the network value is a sum of *products of exact equalities*, degree-additive; error is fatal for exact counting of 2^{Ω(U)} terms, and the equality matrix has full rank over every field (no low-rank approximation of [θ=θ']). The "polynomial method barrier" for OV (n^{2−1/O(log c)} is the limit of degree-d approximations, since d must be ≥ Ω(log c) to be correct) is a statement about approximation degree and does not transfer. |
| Four Russians / Arlazarov et al.; recursive tabulation | tabulate all 2^{s} words, s = log n | Lemma 1/8 *is* a Four-Russians step (group 2g/K nodes, tabulate 2^{2gP/K} settings); it costs the additive 2/K and is lossless in U. The saving comes only from the pieces. |
| Williams' Max-2-SAT 2^{ωn/3}, Björklund et al. | split variables into 3 parts, fast MM | the (K,λ)-clique is a tensor-network contraction of K_K with bond dimension 2^λ; MM gives constant e (§1.4) |
| Hurwitz's problem / Hurwitz–Radon; HWY JAMS'11 "Non-commutative circuits and the sum-of-squares problem"; Hrubeš CCC'24 σ_ℂ(n) ≤ O(n^{1.62}) (prev. O(n²/log n)); Rossman–Zhu 2025 (no lower bound beyond Ω(n) over ℂ); Zhang–Zhu 2026 (field dependence) | (Σx²)(Σy²) = Σ_{k≤s} f_k² with bilinear f_k; the crossing is the non-commutative polynomial Σ x_i y_j x_i y_j (HWY (1.4)) | the exact algebraic home of the pieces (App. G/H). Pieces with ρ give σ_ℂ(N) ≤ N^{2ρ}·polylog (`pieces.md` (2.2)); ρ = 1/√2 gives N^{√2+o(1)}, *better than Hrubeš's N^{1.62}*. ρ → 1/2 ⇔ (one direction) σ_ℂ(N) = N^{1+o(1)}, which would end the HWY approach (they need N^{1+ε} for exponential non-commutative lower bounds). No known lower bound excludes it. |
| Vertex algebras: Zhu modularity, Gaberdiel–Neitzke/Dong–Mason: c_eff ≥ 0 with equality iff V = ℂ; growth log dim V_E ~ 2π√(c_eff E/6) | characters are (vector-valued) modular forms | the pieces are matrix coefficients of the Heisenberg vertex algebra (App. H, l.3003–3011); Lemma 9(a) is locality. **Every C₂-cofinite VOA has β = 1/2 exactly** (c_eff > 0), so ρ = 1/√2 for all of them; the constant c_HR cancels. |
| Hrubeš–Wigderson–Yehudayoff Ω(n^{6/5}) for SOS with integer coefficients | number-theoretic | the pieces are integer-valued, but they give a *bilinear product* identity Σ f_k g_k, not squares, so the 6/5 bound does not apply as is. If an integral version for products existed it would give ρ ≥ 3/5, α' ≤ 0.737 for integer pieces. Unchecked lead. |

## 3. Attempted improvements

### 3.1 Sub-√ growth, and why "polynomially many pieces" is not the real constraint [R]

Suppose a graded space with log dim V_E = f(E) carried the two-order structure of §1.3 (Lemma 9(a),(c),
Lemma 10 for some families a_μ, b_ν indexed by a basis of V_h). Then

    ρ(λ) = f(2h)/(2f(h)),   |I| = 4h + 1,   λ = f(h).

Accounting in Theorem A's proof (display (44)): the number of ι is |I|^{|R|}, |R| ≈ g⁴/4 = N/(4λ), so
the pieces count enters the next exponent **additively**: e' = ρ e + log|I|/(4λ) + 3/K. Consequences:

* f(E) = E^β, 0 < β < 1/2: |I| = 4(λ)^{1/β} + 1 is polynomial, Definition 7(c) holds as stated, ρ = 2^{β−1},
  **α' = 1 − β**. This is the clean target: nothing in Theorem A changes. (Checked: β = 0.4 → ρ = 0.660,
  α' = 0.6; β = 0.25 → ρ = 0.595, α' = 0.75.)
* f(E) = d·log E (polynomial growth): ρ = 1/2 + O(d/λ) but |I| = 2^{λ/d+2}, additive loss 1/(4d) per level:
  the recursion stalls at e ≈ 1/(2d). Useless unless d grows with the level, and d ≫ 1/e_ℓ.
* f(E) = (log E)^γ, γ > 1: ρ = 1/2 + O(γ/λ^{1/γ}), log|I| = λ^{1/γ}, additive loss λ^{1/γ−1}/4. At the top
  level λ = L ≈ 2km/K² ≥ m^{7/9}, and λ only grows going down (L ≥ ρg²λ), so both corrections are
  m^{−Ω(1)} ≪ 1/log m and **α' = 1 would follow** — with a modified Definition 4 (e allowed to depend
  on λ, `CliqueLevels.Solves` only for λ ≥ λ₀(ℓ)) and a re-proof of Theorem A(b) with |I| = 2^{o(λ)}.
  So the polynomial bound |I| ≤ (2λ)^c in Definition 7(c) / `PiecesCounted.Data.Is.card` is a
  convenience, not a barrier; the barrier is the growth rate f alone.

Why no such f < √ is available: the structure needs (i) a grading with operators raising/lowering weight,
(ii) a nondegenerate pairing a[−h]b on V_h, which in the vertex-algebra reading is a_{(2h−1)}b ∈ V_0 and
forces locality order 2h, (iii) dim V_h ≥ 2^λ. Any vertex algebra with a nonzero top pole contains
the modes of a weight-h field acting freely enough to generate partition-like growth; C₂-cofinite ones
have c_eff > 0, hence f ≍ √E (Dong–Mason, Gaberdiel–Neitzke); commutative vertex algebras have all
poles zero (pairing degenerate). The known sub-√ graded algebras (polynomial growth: finitely
generated commutative, or Gelfand–Kirillov finite) have no two-order identity with a nondegenerate top
pole. I could not find, nor rule out, an *abstract* two-order structure (not a vertex algebra) with
β < 1/2. **This is the precise open problem; everything else is downstream.**

### 3.2 Splitting the sum over i (breaking the "max over i") [R, fails]

The piece Q_s costs log p(2h+s) + log p(2h−s) because the maxima over i sit at opposite ends. Term i alone,
T_{s,i} = (−1)^i C(2h,i) a⟨i⟩[s−h+i] b[h−s−i], costs log p(s+i) + log p(2h−s−i)·?? — no: T_{s,i} has a
row factorization through V_{s+i} but **no** column factorization short of 2λ, because the exchanged
order b[h−s−i]a⟨i⟩[s−h+i] is a different operator; only the full alternating sum is order-free (Lemma 9(a)
= (ω₁−ω₂)^{2h}[Y(a,ω₁),Y(b,ω₂)] = 0 coefficientwise). Partial sums Σ_{i≤i₀} inherit the problem: the
identity transfers Σ_{i>i₀}(ab-terms) = Σ_{all}(ba-terms) − Σ_{i≤i₀}(ab-terms), and the second summand
is still one-sided. Reweighting Σ_s g(s)Q_s to drop the expensive s ≈ 0 pieces: Σ_s s^k Q_s is a lower
mode a_{(2h−1−k)}b, so a multiple of the identity needs g(0) ≠ 0 (`pieces.md` §3). **Dead.**

### 3.3 Changing the shape of the recursion: d-dimensional grids [R, fails]

A (g^d, λ)-clique as a d-dimensional grid has d "hyperplane" networks on g nodes each; K_{ℓ+1} = K_ℓ^d
and α' = ln(1/ρ_d)/ln d, so d = 3 would beat d = 2 iff ρ_3 < 3^{−1/2} = 0.577. With the 2-way pieces
available: a box has 2^{d−1} diagonals, which pair into 2^{d−2} rectangles after choosing two coordinates
(1,2); for such a rectangle the split along coordinate 1 is the row split and the split along *every*
other coordinate is the column split (checked on the corner labels for d = 3). So a rectangle with piece s
costs (r_s, c_s, c_s, …, c_s), sum r_s + (d−1)c_s, and with r_s = √2λ√(1+t), c_s = √2λ√(1−t)
(t = s/2h), max_t = 2λ√(1+(d−1)²) by Cauchy–Schwarz, against the trivial 2dλ:

    ρ_d = √(1+(d−1)²)/d:   ρ_2 = 0.707 (α' = 0.5),  ρ_3 = 0.745 (α' = 0.268),  ρ_4 = 0.791 (α' = 0.170).

Strictly worse: 2-way pieces only distinguish two of the d directions. A genuine d-way piece
decomposition of the box crossing (d cost parameters) would need its own algebra; its trivial lower
bound is Σ_j c^{(j)} ≥ 2^{d−1}λ, i.e. again ρ_d ≥ 1/d and α' ≤ 1. No gain in the ceiling either.

### 3.4 Asymmetric or partial grids, K_{ℓ+1} = K_ℓ^β with β < 2 [R, fails]

The pairing of cross edges into rectangles needs two partitions 𝒜 (rows), 𝒥 (columns) of the node set
with every cell 𝒜(a) ∩ 𝒥(j) nonempty; a cell of size r ≥ 1 gives r²·r² pairable edges per pair of cells
(any bijection works), so K' = g_r·g_c·r ≥ g_r g_c. Both networks must have ≥ K nodes (each is recursed
on for the ι where it is the cheaper one, and balancing needs g ≥ K·polylog), so **K' ≥ K² is forced**.
With empty cells (random occupancy δ) a cross edge is pairable with probability δ², unpaired cross edges
cost λ on average per network vs ρλ for paired ones: ρ_eff = 1 − δ²(1−ρ), while K' = δg²; for
K' = K^β one needs δ = K^{β−2} and then ρ_eff = 1 − K^{2β−4}(1−ρ) ≈ 1. Dead. Non-uniform edge lengths
(skipping the regrouping, so that g = K exactly) are handled by rectangular pieces of cost
2√(λ₁²+λ₂²) (`pieces.md` (2.3)) but the max/average gap of the row costs over pairs of rows is Θ(1) for
adversarial ι, which is exactly what the random regrouping (Chebyshev in Lemma 1, Hoeffding in Lemma 8)
repairs at the price g ≥ K·polylog; it changes constants only.

So the exchange rate "β = 2 nodes-exponent for a factor ρ" is rigid, and the target α' = 1 reads
ρ_β = 1/β: a K^β-clique must become a K-node network with 1/β of the shared bits. At β = 2 this is the
trivial bound ρ ≥ 1/2 of the pieces. (Grouping alone is β arbitrary, ρ = 1.)

### 3.5 Polynomial method / probabilistic polynomials over F₂ inside the framework [R, fails]

Z = Σ_z Π_a W_a(z_a) Π_{a<b} Ψ_{a,b}(z_a,z_b) with Ψ = equality on c_{a,b} bits (after grouping, every
Ψ is an equality [θ = θ'] and the W absorb the f's). Razborov–Smolensky lowers the degree of an OR/MAJ of
many predicates at the price of an error probability; here the predicate structure is a *product* (AND)
of equalities, whose exact degree λ per edge is additive and whose matrix [θ=θ'] is the identity of rank
2^c over every ring, so no exact low-rank/low-degree representation exists, and the result must be exact
(a sum of up to 2^{U} signed terms; one wrong term is fatal). Chan–Williams' deterministic *counting*
(modulus-amplifying polynomials, small-bias sets) still counts only with an error that is then removed by
the structure of OV (a single OR per pair); it does not give exact evaluation of Π equality. CRT over
small primes does not change ranks. **No entry point.** What *does* play the role of the "low-degree
representation" is the pieces decomposition: a rank-N² permutation matrix written as a few terms whose
row- and column-ranks multiply to N^{4ρ}; that is an exact identity, and its limits are §1.3.

## 4. Verdict

* **Within Theorem A as proved: α' = log₂(1/ρ), full stop.** The grid (K ↦ K²) and the min-over-two-
  networks step are rigid; the only free parameter is ρ, and ρ ≥ 1/2 caps the framework at
  2^{O(U/log U)} (α = 1). Lean-wise, `ExplicitCost.recursionSolves` and `GeneralPieces.PartA` are already
  general in ρ; `Levels.Gen.e` carries ρ; `rho_pow_le` turns it into α' = `Real.logb 2 (1/ρ)`.
* **What one would have to prove for α > 1/2:** `PiecesCounted.IsPieces ρ c D Alg` (equivalently
  `AppRunningTime.IsPieces`/`Exist ρ c`) **for some ρ < 1/√2**, i.e. functions A_i : ({0,1}^λ)⁴ → ℤ,
  |I| ≤ (2λ)^c, Σ_i A_i = d[x=v][y=u], with factorizations through c^row_i + c^col_i ≤ 4ρλ + c log 2λ bits,
  computable in 2^{cλ} operations; plus the `Proviso` (`VariablesFixedWidthStatement.Proviso`: a number
  in [0.85ρ^ℓ, ρ^ℓ] computable in poly(K_ℓ), trivial for algebraic ρ) and the replacement of
  `fractionHalf`/`GeneralPieces.Between` at the top (`CountedInstance`, `PairsToBound`). Nothing else
  changes; the m-bound becomes 2^{O(km/(log m)^{α'})} and the n-bound 2^{O(k²n log log n/(log n)^{α'})}.
* **Is it plausible?** In the two-order (vertex-algebra) pattern the answer is no: the growth exponent
  β = 1/2 is a theorem for C₂-cofinite VOAs and matches every known example, and ρ = 2^{β−1}. Outside
  that pattern, the question "F = Σ_{poly} T_i with rank(T_i)·OSR(T_i) ≤ N^{4ρ}" is a Hurwitz-type
  problem where upper bounds are hard (the pieces already beat the best published SOS bound) and lower
  bounds beyond ρ ≥ 1/2 are unknown even for the much weaker SOS version (Rossman–Zhu 2025). My honest
  estimate: α' ∈ (1/2, 1) would need a new graded algebra with sub-√ growth and a nondegenerate top
  pole — I know of no candidate and expect none among vertex algebras; α' = 1 would additionally give
  σ_ℂ(N) = N^{1+o(1)}, which I would bet against. **Most valuable next step:** try to prove ρ ≥ ρ₀ > 1/2
  for *graded* two-order decompositions (weight conservation w_row + w_col = 2h per term, max over the
  terms), where the spread argument of §1.3 suggests ρ ≥ 1/√2 exactly; that would close the question for
  the whole family of constructions the paper's Appendix H describes.

## Scripts / checks

Numbers in §3.1 and §3.3 were checked with a 10-line Python computation (max_t √(1+t) + (d−1)√(1−t)
= √(2(1+(d−1)²)); ρ = 2^{β−1}). Lean names were verified by `grep` in `/home/user/anth-build/proof`;
no Lean was built.
