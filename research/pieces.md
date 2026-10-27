# Track H: pieces of the crossing (the exponent ρ of Theorem A)

Date 27 Oct 2026. Source: Anthropic, "A 2^{o(n)} time algorithm for 3-SAT", Def. 7, Thm A, Lemma 2,
App. B, App. G/H. Scripts are in `research/scripts/pieces_*.py`. Tags: **[R]** rigorous,
**[N]** numerical, **[C]** conjectural/heuristic.

## 0. Summary

* I found no construction with ρ < 1/√2, and I proved no lower bound above the trivial ρ ≥ 1/2.
* **[R] New corollary.** Pieces with parameter ρ give `P(N) ≤ N^{2ρ}·polylog N`, where P(N) is
  Naslund's / Hrubeš–Wigderson–Yehudayoff's width. With App. B this gives `P(N) ≤ N^{√2+o(1)}`, so the
  sum-of-squares composition number over ℂ is at most `N^{1.4143}`. Hrubeš (CCC'24) has `N^{1.62}`.
  The construction is explicit and its coefficients are integers.
* **[R] Consequence for the two directions.** ρ → 1/2 would give P(N) = N^{1+o(1)}, which answers
  Naslund's Problem 12 negatively. Any lower bound P(N) ≥ N^{1+ε} gives ρ ≥ (1+ε)/2. The converse
  fails: P(N) small does not seem to give pieces. So lower bounds on ρ are implied by HWY-type
  sum-of-squares lower bounds, but they may be easier than those.
* **[R/N] Natural classes.** Commutative tensor-power classes are exactly solvable by a quantile
  formula (generic-flag lemma). The bit-symmetric `span{I,SWAP}` class has optimum
  **ρ = 0.86936…**, better than the paper's 0.8962 for the same class but far above 0.7071. The
  Bell/Pauli class is better at every λ I computed, but it is still ≥ 0.80 under the generic model.
* **[R] Rectangular norm.** Two-sided cost function c(λ1,λ2) with 2‖λ‖_∞ ≤ c ≤ 2‖λ‖_2. Fock pieces
  are second-order tight at the axes. So any lower-bound argument must be global; local
  perturbative arguments near the axes give nothing.

## 1. Clean formulation

Write `N = 2^λ` and `F = SWAP` on `ℂ^N ⊗ ℂ^N`, the operator with `⟨x,y|F|u,v⟩ = [x=v][y=u]`.
The row flattening (x,y)|(u,v) is the operator itself, so `c_row = log rank T`. The column flattening
(x,u)|(y,v) is the realignment, so `c_col = log OSR(T)`, the operator-Schmidt rank:
`T = Σ_{k ≤ OSR} A_k ⊗ B_k`. The third flattening (x,v)|(y,u) is the partial transpose, and there F
has rank 1.

**Problem.** Find `F = Σ_{i ≤ poly(λ)} T_i` with `rank(T_i) · OSR(T_i) ≤ N^{4ρ} poly(λ)`.

Equivalent form: decompose the transpose map `Z ↦ Z^T` on M_N into poly(λ) linear maps Φ_i with
`(rank of Φ_i as a linear map) × (Kraus rank of Φ_i) ≤ N^{4ρ}`. The map Φ_T sends Z(u,v) to
Σ T(x,y,u,v)Z(u,v). Its map rank is rank T, its Choi matrix is the (u,x)|(v,y) flattening, so its
Kraus rank is OSR(T).

Notes.
* The rank-only relaxation over ℚ (no bit or time bounds) is the natural object. All known
  constructions satisfy the integrality conditions, and so do all lower-bound arguments below.
  Norm or potential arguments are useless here. Definition 7 allows values up to 2^{poly λ}, so
  cancellations of huge coefficients are allowed, and only algebraic invariants (ranks,
  supports) can give lower bounds.
* Without the poly(λ) bound on the number of terms the problem is trivial: N² terms
  |xy⟩⟨yx| each have rank·OSR = 1. So any lower bound must use that there are few terms.
* **Symmetries.** T ↦ (U⊗V)T(V⁻¹⊗U⁻¹) fixes F and preserves both ranks. The swap y↔u exchanges
  rank and OSR and fixes F. The only operators invariant under the full group are multiples of F,
  so plain twirling gives nothing. Partial (finite-group) twirls are used in §4.

## 2. Rigorous facts

**(2.1) Trivial lower bound [R].** Contract y with β and u with a. For F this gives
`⟨β|a⟩·I_N` on (x,v). For any piece T the contracted x|v matrix has rank ≤ min(rank T, OSR T).
So `Σ_i min(r_i, o_i) ≥ N`. Hence some piece has both r_i and o_i ≥ N/|I|, which gives ρ ≥ 1/2.
I found no algebraic invariant that improves this. The contraction bounds are additive
(r + o ≥ N), and every product-type bound I tried reduces to open sum-of-squares questions.

**(2.2) Pieces ⇒ P(N) [R].** Put the pieces with `c_col ≤ θ` into R, and the rest, which have
`c_row ≤ 4ρλ + c log 2λ − θ`, into C. Then `dF = R + C`, with OSR(R) ≤ |I|·2^θ and
rank(C) ≤ |I|·2^{4ρλ+c log 2λ−θ}. Take θ = 2ρλ + (c/2) log 2λ:

    P(N) ≤ 2 (2λ)^{1.5c} N^{2ρ}.

* App. B (ρ = 1/√2, |I| = O(λ²), c_row + c_col ≤ 2√2 λ + O(log λ)) gives `P(N) ≤ N^{√2} (log N)^{O(1)}`.
* With HWY Prop. 4.1 (s ≤ P(N) ≤ 4s), the bilinear identity `(Σx_i²)(Σy_j²) = Σ_k f_k f'_k` over ℚ
  holds with N^{√2+o(1)} products. Over ℂ we have `f f' = ((f+f')/2)² + (i(f−f')/2)²`, so the
  complex sum-of-squares composition number is `σ_ℂ(N) ≤ N^{√2+o(1)}`, against Hrubeš's N^{1.62}.
  The paper (App. G) only uses the opposite direction, Hrubeš ⇒ ρ ≈ 0.905.
* Rectangular version: `[n1,n2,s]` formulas with `s ≤ 2^{√(λ1²+λ2²)+o(λ)}`, where `n_i = 2^{λ_i}`
  (see 2.3). For example `[n^γ, n, n^{√(1+γ²)+o(1)}]`.
* So ρ < 1/2 + ε/2 would refute "P(N) ≥ N^{1+ε}" (Naslund's Problem 12). Conversely, any
  superlinear lower bound for P(N) gives ρ > 1/2. By HWY, such P(N) bounds would also give
  exponential lower bounds for non-commutative circuits. I see no converse: P(N) ≈ N does not
  obviously give pieces with ρ < 3/4, because two-term tensor powers give ρ ≥ 3/4.
* The construction also gives the whole trade-off curve `F = R_θ + C_θ` with
  OSR(R_θ)·rank(C_θ) ≤ N^{4ρ}·poly for every θ.

**(2.3) Rectangular cost function [R].** Let `F_{n1,n2} = [x=v][y=u]` with x,v ∈ [n1] and y,u ∈ [n2],
and let `c(λ1,λ2)` be the best exponent of max_i (c_row + c_col).
* `F_{n1,n2} ⊗ F_{n2,n1} = F_{n1n2,n1n2}`, so `4ρ(λ1+λ2) ≤ c(λ1,λ2) + c(λ2,λ1)`. Tensor products of
  boundedly many families are subadditive.
* Lower bound `c ≥ 2 max(λ1, λ2) − O(log)`, by the contraction in (2.1) in both ways.
* Upper bound `c ≤ 2√(λ1² + λ2²) + O(log)`. Use App. B with labels x,v of weight h and vectors y,u
  of weight E. Lemma 9 holds on every V_E. The row middle weights are ≤ E+h+s and the column ones
  ≤ E+h−s, so `c_row + c_col ≤ 2 c_HR √(E+h) + O(log) = 2‖(λ1,λ2)‖₂ + O(log)`.
* So ρ ∈ [1/2, 1/√2] is the value on the diagonal of a sublinear function squeezed between 2‖·‖_∞
  and 2‖·‖_2. Fock gives `c(1,ε) = 2 + O(ε²)`. Since `c(1,1) ≥ [c(1,ε) − 2(1−ε)]/ε`, any lower bound
  must beat Fock at second order near the axes. This rules out "perturbative" lower bounds.

## 3. Why App. B stops at 1/√2 (heuristic [C], checked [N])

* Piece A_s is a signed sum over i ∈ [0, 2h] of products. In one order the product passes through
  weight s+i, in the other through 2h−s−i. **Each single i would cost √(s+i) + √(2h−s−i) ≤ 2√h,
  which is ρ = 1/2.** The loss comes only from the spread of i: the row rank is dominated by
  i = 2h (weight 2h+s) and the column rank by i = 0 (weight 2h−s). Only the full sum over i can be
  written in both orders (Lemma 9(a)).
* The spread equals the locality order H = 2h of the Heisenberg vertex algebra. It is forced:
  a_{(H−1)}b must be the nondegenerate pairing [x=v], so the OPE has a pole of order 2h.
* Could one reweight Σ_s g(s)Q_s to avoid the bottleneck at s ≈ 0? Σ_s s^k F_s is given by the
  fields a_{(H−1−k)}b. Getting a multiple of the identity requires g to be a polynomial of low
  degree with g(0) ≠ 0, so the expensive pieces near s = 0 cannot be dropped.
* Any VOA-type replacement needs log dim V_E ~ E^α with α < 1/2, and then ρ = 2^{α−1}. For
  C2-cofinite VOAs, Zhu modularity plus Cardy asymptotics give α = 1/2 exactly. For Heisenberg,
  lattice and affine VOAs the growth is also exp(c√E). So the VOA route is pinned at 1/√2 unless a
  VOA (or locality structure) of sub-√ growth with a nondegenerate top pole exists.
* [N] `pieces_fock_ranks.py` builds the App. B pieces exactly for h ≤ 6 (N = p(h) ≤ 11) and checks
  `Σ_s A_s = h![x=v][y=u]`. True ranks are close to the paper's count where that count is below N²
  (h=5, s=−3: 40 vs 45; h=6, s=−2: 116 vs 139). There are no hidden rank savings, so the 1/√2
  count is essentially sharp for this construction.

## 4. Commutative tensor-power classes: exact solution

**Setting.** Fix a local algebra 𝒮 ∋ F_d with a "direct" basis {E_a}, whose ranks add, of ranks r_a,
and a basis {G_b} whose realignments are direct, of OSRs o_b. Take the S_λ-symmetric part of
𝒮^{⊗λ}. Its elements are indexed by types (poly(λ) many). rank T = Σ over E-types in its support,
OSR T = Σ over G-types in its support. The best piece at given costs is V_S ∩ W_J, where V_S and
W_J are coordinate subspaces of two flags ordered by cost.

**Generic-flag lemma [R].** Two complete flags in opposite (generic) position have a common adapted
basis with `A_a ∩ B_b = ⟨v_{n−b+1},…,v_a⟩`. The pieces therefore span F, assuming F has full
support, iff the intervals cover [1,n]. Hence

    4ρλ = max_i ( q1[i] + q2[n−1−i] ),     q1, q2 = sorted lists of type costs.

Generic position is the *best* case. For any relative position w, the bound becomes
max_i (q1(i) + q2(π(i))), and the anti-sorted pairing minimises it (rearrangement). So the
formula is a lower bound whenever F has full support in the doubly adapted basis.
Asymptotically, `4ρ = max_x (Q1(x) + Q2(1−x))` with Q_j the quantile functions of the per-block
cost under the **uniform measure on the type simplex**, not the entropy-weighted one.

**Qubit class** (𝒮 = span{I, SWAP}, i.e. the U⊗U-commutant per bit, bit-symmetric; this is the
class of the paper's 0.896):
* E: P_anti (rank 1) / P_sym (rank 3). G: I ↔ Q (OSR 1) / SWAP − I/2 ↔ G (OSR 3).
* Elements are binary forms of degree λ, with F = (X−Y)^λ, X' = X+Y, Y' = X−3Y.
* [N] The exact optimum mod p (`pieces_qubit_class_fast.py`) equals the generic formula exactly
  for λ = 32, 64, 128, 256: 0.82578, 0.84406, 0.85512, 0.86162. A random basis change gives the
  same values (`pieces_qubit_generic.py`). Nonzero minors mod p imply nonzero minors over ℤ, so
  the Krawtchouk flags are generic for these λ.
* **Limit ρ_qubit = q(1/2)/2 = 0.869362**, where q(1/2) is the median of
  H(κ) + (1−κ) log₂3 for κ ~ U[0,1] (`pieces_quantile_formula.py`). The paper's grouping (monomials
  t^c X'^{λ−c}) gives log₂12/4 = 0.8962. The optimum also uses pieces supported on low *and* high
  antisymmetric counts.
* The same formula for the 2-dimensional Hurwitz classes gives N=4: 0.9347 and N=8: 0.9006. The
  latter matches the paper's 10.81/12.

**Bell/Pauli class** (𝒮 = Bell-diagonal operators; rank-1 Bell projectors / OSR-1 σ_a⊗σ_a; the
transform is the Fourier transform on (ℤ₂²)^λ and F ↔ the bent function (−1)^{#zeros}):
* Twirling by the global S_3 (permuting X,Y,Z) is free, because the max-over-types cost is
  invariant. Reduced code: `pieces_bell_reduced.py`.
* [N] Exact values: λ = 8, 12, 16, 20 give 0.5706, 0.6284, 0.6717, 0.7018 (qubit class at λ = 16:
  0.7954).
* The Krawtchouk structure is *not* generic here: exact > generic by 0.06–0.07, and the gap is
  not shrinking.
* The generic continuum value is 0.8042 (median entropy of Dirichlet(1,1,1,1)). By the
  rearrangement remark, the true limit is probably ≥ 0.80 [C].
* Finer local algebras push the type-entropy towards its maximum, so they get worse. Coarser ones
  have larger local dims. I expect commutative classes to stay ≥ about 0.8 [C].

**Non-symmetric (2^λ-dimensional) version** of the qubit class, under the generic model: needs
|S|, |J| ≥ 2^λ/poly, which gives log₂12/4 again. Any gain must come from non-generic (tensor)
structure.

## 5. Assessment

* ρ < 1/√2 would improve the paper's √log. It would also give σ_ℂ(N) < N^{1.414}, a new
  sum-of-squares upper bound, and it seems to need a locality structure of sub-√ growth.
  Commutative or symmetric tensor constructions are stuck around 0.8–0.87.
* ρ ≥ ρ0 > 1/2 in general: open. Every lower bound must survive the Fock near-axis tightness
  (§2.3) and cannot use norms. The obvious routes (product bounds rank·OSR ≳ N² for two-term
  splittings) give only 1/2. Lower bounds on P(N) would suffice, but those are HWY-hard.
* Most promising next steps:
  1. Prove the asymptotic Bell-class value. It needs a description of the multivariate Krawtchouk
     relative position, so that one can get beyond the generic formula.
  2. Look for a graded algebra with log dim V_E = o(√E) carrying operators with a two-order
     identity like Lemma 9 and a nondegenerate top pairing like Lemma 10. A W-type or
     non-C2-cofinite VOA with c_eff → 0 is one candidate.
  3. Try a lower bound for "graded" decompositions: pieces that pass through a graded space with
     weight conservation w_row + w_col = const. The spread argument of §3 suggests 1/√2 there.

## Scripts

| script | purpose |
|---|---|
| `pieces_qubit_class.py`, `pieces_qubit_class_fast.py` | exact optimum of the bit-symmetric span{I,SWAP} class |
| `pieces_qubit_generic.py` | the same with a random basis change (genericity test) |
| `pieces_qubit_inspect.py` | which pieces (supports) the optimum uses |
| `pieces_quantile_formula.py` | generic-flag closed form; qubit limit 0.86936; Hurwitz N=4, 8 classes |
| `pieces_bell_generic.py`, `pieces_bell_exact.py`, `pieces_bell_reduced.py` | Bell/Pauli class: generic formula, exact optimum, S_3-reduced exact optimum |
| `pieces_fock_ranks.py` | App. B pieces for small h: identity check and true ranks vs bounds |
