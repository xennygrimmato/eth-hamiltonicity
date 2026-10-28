# Is ρ ≥ 1/√2 forced? Lower bounds for the "pieces" constant of Anthropic's engine

Date 28 Oct 2026. Follows `rate.md` (the bottleneck analysis) and `research/pieces.md` (the tensor
formulation). Lean paths are relative to `/home/user/anth-build/proof/`; paper line numbers refer to
`.../scratchpad/anth/fm/paper.txt` (Definition 7 l.1510, Appendix B l.1723–2016, Appendix H
l.2837–3013). Scripts: `research/permanent/scripts/rho_*.py`, outputs `rho_*.out`.
Tags: **[R]** proved here (or checked against the Lean statements), **[K]** known theorem cited,
**[N]** numerical, **[C]** heuristic.

## 0. Summary (verdict first)

* **Definition.** §1 states `PiecesCounted.IsPieces ρ c D Alg` as pure mathematics. The only
  consequences of clauses (a), (b) that a lower bound can use are rank inequalities for the two
  flattenings of each piece (§1.3); the definition never asks for minimal ranks, symmetry, positivity,
  or any relation between the pieces beyond Σ_i A_i = d·[x=v][y=u].
* **Proved [R] (§3, Theorem 3.2 and Corollary 3.4).** For *graded two-order decompositions* — pieces
  that are the weight-conserving slices Q_s of a locality identity of order H on a graded space with
  log dim V_E = f(E), costed, as in Appendix B, by the dimensions of the spaces the products pass
  through ("max over the terms") — the certified cost of the slice s is at least
  f(2h+s) + f(2h−s) when H = 2h, hence at least 2f(2h) at s = 0. With f = log p (Fock space) and
  the Hardy–Ramanujan bounds this gives **ρ ≥ 1/√2 − O((c+1)·log λ/λ)**: the √2 is exactly the price of
  the max over the terms, and no reweighting or sub-family of the slices avoids it (§3.5: the 4h+1
  pieces of Theorem B satisfy exactly one linear relation, Σ_s s·A_s = 0, so every representation of
  the crossing by them uses A_0 with a nonzero coefficient; [R]+[N]).
* **The two hypotheses that carry the theorem are both genuinely needed and both unproved in general:**
  (H) the spread of the slices is H = 2h, which in a vertex algebra with V_0 = ℂ follows from the
  pairing being the *top* pole a_{(2h−1)}b (Lemma 4.1, [R]); a lower-order locality H = 2h − w would
  put the pairing into the zero mode of a weight-w vector ("zero-mode loophole", §4.2), which is not
  excluded by anything I can prove, but a dimension count says it costs more than it saves [C];
  (G) the growth f(2h) ≥ √2·f(h)(1−o(1)), i.e. β := lim log f(E)/log E ≥ 1/2. This is where every
  construction is pinned: a field that is nontrivially local has modes at all but finitely many
  integer degrees (Proposition 5.1, [R]), a free field with a nonzero top pole therefore has a Fock
  subspace of partition growth (Proposition 5.2, [R]), and every C₂-cofinite vertex algebra has
  exactly β = 1/2 (modularity, [K]). Nothing proves β ≥ 1/2 for an abstract two-order structure.
* **Not proved, and not provable by counting:** ρ ≥ ρ₀ > 1/2 for arbitrary pieces. The three rank
  inequalities that follow from (a), (b) are satisfied by a fake "profile" at ρ = 1/2 (§2.2); any
  stronger bound must use the matrices themselves, and already for two pieces this is the
  Hurwitz/HWY problem. One new rigorous crumb: a piece of operator-Schmidt rank 1 forces the
  remaining pieces to carry rank ≥ N(N−1)/10 (Proposition 2.3, [R]), so the simplest ρ = 1/2
  profiles ((N²,1)+(1,N²)+…) are impossible.
* **Break attempts (§6).** Every candidate structure fails for one of three reasons: β = 1/2
  (all free fields, lattice/affine/W/minimal-model VOAs, q-deformations — the constant in f cancels,
  only the exponent counts); β = 1 (anything ungraded taken to tensor powers: Clifford/octonions,
  group algebras, Pauli/Fourier, codes, Hadamard — these give constants 0.80–0.92, never below
  3/4 asymptotically); or no two-order identity with poly(λ) terms (sparse Fock spaces with
  β = 1/3 or polylog growth, Weyl algebras in finitely many variables, commutative algebras: the
  naive Leibniz identity has p(w)² terms per slice and gives ρ → 1; a commutative pairing forces
  |I| ≥ 2^{λ/O(1)} pieces). **Verdict: open**, with the precise open statement and the minimal
  counterexample structure in §7.
* **Numerics [N].** True ranks of the Theorem-B pieces for h ≤ 10 (N = p(h) ≤ 42, matrices up to
  1764×1764) equal the paper's counts to within 3–7 % wherever the count is below N² (`rho_fock_pieces_*.out`);
  single terms of a slice are never two-order (`rho_single_terms.out`); Id ∈ o(V_w)|V_h for all
  2 ≤ w ≤ 8, h ≤ 6 (`rho_zero_mode.out`), so the loophole of §4.2 is not closed by the zero
  modes alone; the counted ρ at practical sizes is 0.75 at λ = 128 and 0.83 at λ = 32
  (`rho_growth_law.out`), converging to 1/√2 like 1 + O(log λ/λ).

## 1. The definition, exactly (Task 1)

### 1.1 Data at one λ [R]

Fix λ ≥ 1, N = 2^λ, labels x, y, u, v ∈ {0,1}^λ. The crossing is F(x,y,u,v) = [x=v][y=u]
(`Pieces.cross`). A *family at λ* (`Pieces.Family lam`) is

    d ∈ ℤ,   I ⊂ ℤ finite,   A_i : ({0,1}^λ)^4 → ℤ (i ∈ I),   c^row_i, c^col_i ∈ ℕ (i ∈ I).

Two flattenings of A_i (`Pieces.rowwise`, `Pieces.colwise`):

    A_i^row [(x,y),(u,v)] := A_i(x,y,u,v)   (an N²×N² matrix, rows (x,y), columns (u,v)),
    A_i^col [(x,u),(y,v)] := A_i(x,y,u,v)   (rows (x,u), columns (y,v)).

"F factors through c bits" (`Pieces.FactorsThrough F c b`, Definition 1 with a size bound) means:
there are integer functions f, f' with F(z,z') = Σ_{θ∈{0,1}^c} f(z,θ)·f'(z',θ) and |f|, |f'| < b.

### 1.2 Pieces with parameters (ρ, c) [R]

`PiecesCounted.Data` is a family for every λ together with the four factor functions
`D.fn lam tr side i z θ` (tr = row/col, side = first/second factor). `D.Is ρ c` is the conjunction of

| Lean field | statement |
|---|---|
| `rho_ge`, `rho_lt`, `c_pos` | 1/2 ≤ ρ < 1 (real), c ≥ 1 (integer) |
| `d_pos` | d ≥ 1 for every λ ≥ 1 |
| `sum` (a) | Σ_{i∈I} A_i(x,y,u,v) = d·[x=v][y=u] for all x,y,u,v |
| `row` (b) | A_i(x,y,u,v) = Σ_{θ∈{0,1}^{c^row_i}} fn(row,1,i,(x,y),θ)·fn(row,2,i,(u,v),θ) |
| `col` (b) | A_i(x,y,u,v) = Σ_{θ∈{0,1}^{c^col_i}} fn(col,1,i,(x,u),θ)·fn(col,2,i,(y,v),θ) |
| `caps` (b) | c^row_i + c^col_i ≤ 4ρλ + c·log₂(2λ) for every i ∈ I |
| `card` (c) | \|I\| ≤ (2λ)^c |
| `size_d`, `size_I`, `size_A`, `size_f` (c) | d, \|i\|, \|A_i(…)\|, \|fn(…)\| < 2^{(2λ)^c} |

`IsPieces ρ c D Alg` adds: `polyTimeSteps` (one step machine `Alg` with polynomial-time steps) and
`computes` (`Alg` answers every question — d, the sorted list I, c^row_i or c^col_i, a value
A_i(x,y,u,v), a value of one of the four factor functions — within 2^{cλ} steps on states of size
≤ `room c λ`). `Exist ρ c := ∃ D Alg, IsPieces ρ c D Alg`. Theorem B is `Exist (1/√2) c` for some c,
with the explicit data of Appendix B (`HalfPieces`). What is **not** required: no symmetry of the
A_i, no positivity, no bound on c^row_i, c^col_i separately (`mayAssume` adds ≤ 2λ at the price
c ↦ c+2), no relation between different λ beyond uniform computability, no minimality of the
numbers c^row_i, c^col_i (they are any numbers for which an integer factorization is exhibited).
The parameter ρ enters only through `caps`; so

    ρ* := inf { ρ : Exist ρ c for some c },     known: 1/2 ≤ ρ* ≤ 1/√2.

(ρ ≥ 1/2 is part of the definition; it is also a theorem, see 1.3.) The question is whether ρ* < 1/√2.

### 1.3 What a lower bound may use: ranks [R]

**Lemma 1.1.** If an integer matrix M factors through c bits (over ℤ, or over any field) then
rank_ℚ M ≤ 2^c. *Proof.* M = Σ_θ f(·,θ)f'(·,θ)^T is a sum of 2^c rank-one matrices. ∎

So `row`, `col`, `caps` imply, with r_i := rank A_i^row and o_i := rank A_i^col (over ℚ),

    log₂ r_i + log₂ o_i ≤ 4ρλ + c log₂(2λ)   for every i ∈ I.                        (1.1)

Conversely an integer matrix of rank r factors over ℤ through ⌈log₂ r⌉ bits (Smith normal form), but
the factor values need not satisfy the size bound of (c); for lower bounds only Lemma 1.1 matters.
In the language of `pieces.md`: A_i^row is the operator T_i on ℂ^N⊗ℂ^N with ⟨x,y|T_i|u,v⟩ = A_i,
r_i = rank T_i and o_i = OSR(T_i) is its operator-Schmidt rank; Σ_i T_i = d·SWAP.

## 2. What clauses (a) and (b) alone give, and why it stops at 1/2

### 2.1 The three rank inequalities [R]

**Proposition 2.1.** For every family satisfying (a):

    (R1) Σ_i r_i ≥ N²,   (R2) Σ_i o_i ≥ N²,   (R3) Σ_i min(r_i, o_i) ≥ N.

*Proof.* (R1), (R2): F^row and F^col are permutation matrices of size N², so d·N² = rank(dF^row)
≤ Σ_i rank A_i^row by subadditivity; same for col. (R3): fix α = β = e_0 ∈ ℚ^N and contract,
C_i(x,v) := Σ_{y,u} α_u β_y A_i(x,y,u,v). Then C_i = (I_N⊗β)^T A_i^row (α⊗I_N) and also
C_i = (I_N⊗α)^T A_i^col (β⊗I_N), so rank C_i ≤ min(r_i, o_i); and Σ_i C_i = d⟨α,β⟩·I_N has rank N. ∎

**Corollary 2.2 (ρ ≥ 1/2).** max_i (log r_i + log o_i) ≥ 2(λ − log₂|I|); with |I| ≤ (2λ)^c and
(1.1): ρ ≥ 1/2 − (3c/4)·log₂(2λ)/λ. (The definition's `rho_ge` is consistent with this.)

### 2.2 The inequalities are satisfiable at ρ = 1/2 [R]

The "profile" {(r,o)} = {(N², 1), (1, N²), (N, N)} satisfies (R1)–(R3) and has max(log r + log o) = 2λ.
Hence **no argument that uses only (a) and the ranks of the individual flattenings can give ρ > 1/2.**
A lower bound beyond 1/2 must use the actual matrices, i.e. it is a statement of Hurwitz type:
for two pieces, dF = R + C with OSR(R) ≤ M and rank(C) ≤ M is exactly the sum-of-squares
composition problem of Hurwitz–Radon / Hrubeš–Wigderson–Yehudayoff (App. H, (71)–(72)), where
nothing beyond M ≥ N is known over ℂ (`pieces.md` §2.2). This is the barrier of `rate.md` §4.

### 2.3 A small rigorous step past the profile: OSR-1 pieces are useless [R]

**Proposition 2.3.** Let 𝔽 be a field of characteristic 0, F = SWAP on 𝔽^N⊗𝔽^N, and A, B ∈ M_N(𝔽)
arbitrary. Then rank(F − A⊗B) ≥ N(N−1)/10.

*Proof.* Put R := F − A⊗B, M := rank R; extend 𝔽 to its algebraic closure (ranks do not change).
Since F(X⊗Y)F = Y⊗X for all X, Y, we have B⊗A = F(A⊗B)F = F(F−R)F = F − FRF, so

    (A⊗B)(B⊗A) = (F−R)(F−FRF) = I − 2RF + RFRF  ⇒  rank(AB⊗BA − I) ≤ 2M.          (2.1)

Write C := AB, D := BA. The kernel of C⊗D − I lies in ⊕_{γγ'=1} V_γ(C)⊗V_{γ'}(D) (generalized
eigenspaces; on V_γ⊗V_{γ'} with γγ' ≠ 1 the operator C⊗D has the single eigenvalue γγ' ≠ 1).
On V_γ(C)⊗V_{1/γ}(D) the operator C⊗D is γ^{-1}C|⊗γD| = U⊗U' with U, U' unipotent, and the fixed
space of U⊗U' on P⊗P' ≅ Hom(P'^*, P) is the space of intertwiners between two unipotent operators,
of dimension Σ_{blocks} min(size_a, size_b) ≤ (number of Jordan blocks of U)·dim P'
= dim ker(U−I)·dim P'. Summing over γ,

    N² − 2M ≤ dim ker(C⊗D − I) ≤ max_γ dim ker(C − γI) · Σ_γ dim V_{1/γ}(D) ≤ N·max_γ dim ker(C − γI),

so there is γ ≠ 0 with rank(AB − γI) ≤ 2M/N; write AB = γI + L, rank L ≤ 2M/N. In particular
rank B ≥ rank AB ≥ N − 2M/N. Now compute (A⊗B)(B⊗I) in two ways: it is AB⊗B = γ(I⊗B) + L⊗B, and
it is (F−R)(B⊗I) = (I⊗B)F − R(B⊗I). Hence

    (I⊗B)(F − γI) = L⊗B + R(B⊗I),   rank ≤ rank(L)·N + M ≤ 3M,

and rank((I⊗B)(F−γI)) ≥ rank(F−γI) − dim ker(I⊗B) ≥ rank(F−γI) − N·(2M/N). So rank(F−γI) ≤ 5M.
But F has the eigenvalues +1 (multiplicity N(N+1)/2, on Sym²) and −1 (multiplicity N(N−1)/2, on Λ²),
so rank(F−γI) ≥ N(N−1)/2 for every γ. Hence 5M ≥ N(N−1)/2. ∎

**Corollary.** In any family with (a), a piece with o_i = 1 (a product operator A⊗B, after scaling by
d) forces Σ_{j≠i} r_j ≥ N(N−1)/10; in particular for |I| = 2 the other piece has
rank ≥ N(N−1)/10 and OSR ≥ N² − 1 (F^col is a permutation matrix of rank N²), cost ≥ 4λ − O(1):
two-piece decompositions with a product piece gain nothing (ρ → 1). The same argument does not extend
to OSR(T_1) = k ≥ 2 (the trick (2.1) uses the product structure); for k ≈ N² it is the open
Hurwitz problem.

## 3. Graded two-order decompositions: the spread lemma (Task 2)

### 3.1 The structure, abstractly [R]

**Definition 3.1 (two-order piece on a graded space).** Let V = ⊕_{E∈ℤ} V_E be a graded vector
space over a field, D(E) := dim V_E < ∞, D(E) = 0 for E < 0, f(E) := log₂ D(E). Let h ≥ 0 and
let y ↦ e_y be an injection of {0,1}^λ into a basis 𝔅 of V_h, with e_u^* the dual functionals (so
D(h) ≥ N). A *two-order piece* consists of a finite set T of terms, degrees r_j ∈ ℤ (j ∈ T), and for
every label x and v operators

    X_x^{(j)} ∈ Hom(V_h, V_{h+r_j}),  Y_v^{(j)} ∈ Hom(V_{h+r_j}, V_h),
    X'^{(j)}_x ∈ Hom(V_{h−r_j}, V_h),  Y'^{(j)}_v ∈ Hom(V_h, V_{h−r_j}),

with the **two-order identity**  P(x,v) := Σ_{j∈T} Y_v^{(j)} X_x^{(j)} = Σ_{j∈T} X'^{(j)}_x Y'^{(j)}_v
as operators on V_h. Its matrix is A(x,y,u,v) := e_u^*(P(x,v) e_y). A *graded two-order
decomposition* is a family of such pieces P_i, i ∈ I, with Σ_i A_i = d·[x=v][y=u].

In Appendix B: V = ℚ[t_1,t_2,…], D = p, e_y = t^{μ(y)}, the piece s has T = {0,…,2h}, r_i = s−h+i,
X_x^{(i)} = a_{μ(x)}^{⟨i⟩}[s−h+i], Y_v^{(i)} = b_{μ(v)}[h−s−i] (and X' = X, Y' = Y: the same
operators in the other order), and the identity is Lemma 9(a). In Appendix H's words: "the two
directions are the two orders of multiplying two operators".

**Lemma 3.2 (certified costs).** A two-order piece factors row-wise through
R^row := Σ_{j∈T} D(h+r_j) terms and column-wise through R^col := Σ_{j∈T} D(h−r_j) terms:

    A(x,y,u,v) = Σ_j Σ_{τ ∈ basis of V_{h+r_j}} e_τ^*(X_x^{(j)} e_y) · e_u^*(Y_v^{(j)} e_τ),
    A(x,y,u,v) = Σ_j Σ_{τ ∈ basis of V_{h−r_j}} e_τ^*(Y'^{(j)}_v e_y) · e_u^*(X'^{(j)}_x e_τ).

The first is a function of (x,y) times a function of (u,v), the second of (y,v) times (x,u).
Over ℤ whenever the operators have integer matrices (Appendix B: (O1), `PieceFacts.int_a/int_b`).
The *certified* costs are c^row := ⌈log₂ R^row⌉, c^col := ⌈log₂ R^col⌉ (Theorem B uses exactly
these: `D.cap lam false s = Nat.clog 2 (Rrow h s)`). They are upper bounds on the true ranks.

### 3.2 The spread lemma [R]

**Theorem 3.3.** For a two-order piece with degrees r_j, j ∈ T, put r_max := max{r_j : D(h+r_j) > 0}
and r_min := min{r_j : D(h−r_j) > 0}. Then

    c^row + c^col ≥ f(h + r_max) + f(h − r_min).                                       (3.1)

For the slices of a locality identity of order H with degrees r_i = s − h_0 + i, i = 0..H
(Appendix B: h_0 = h, H = 2h), the slice s satisfies, whenever both weights are ≥ 0,

    c^row_s + c^col_s ≥ f(h − h_0 + s + H) + f(h + h_0 − s),                           (3.2)

in particular for h_0 = h, H = 2h and |s| ≤ 2h:  c^row_s + c^col_s ≥ f(2h+s) + f(2h−s), and
c^row_0 + c^col_0 ≥ 2 f(2h).

*Proof.* log₂ Σ_j D(h+r_j) ≥ max_j f(h+r_j) ≥ f(h+r_max), same for the columns. ∎

This is the "max over terms" in the task's words: in the row order the largest passing space is the
one of the top term i = H, in the column order that of the bottom term i = 0, and the two maxima
sit at opposite ends. **A single term costs f(h+r) + f(h−r) ≤ 2f(h) = 2λ when f is concave** (as
c√E is, and log p is log-concave from E = 26 on by DeSalvo–Pak), i.e. ρ = 1/2 — the whole loss comes
from the spread H. Single terms are not two-order: for the pieces of
Theorem B this is checked numerically in `rho_single_terms.out` (h = 4,5,6, s = 0: the term i has
column rank ≤ p(2h−i) as constructed, but row rank ≈ N² ≫ p(i); e.g. h = 6, i = 4: 99 versus p(4) = 5).

**Corollary 3.4 (the general law).** If 0 ∈ S (the slice s = 0 is used), λ ≤ f(h), and the pieces
have parameters (ρ, c) with the certified costs, then

    4ρλ + c log₂(2λ) ≥ 2 f(2h),   i.e.   ρ ≥ f(2h)/(2f(h)) − c log₂(2λ)/(4λ).

If f(E) = κE^β(1+o(1)) then ρ ≥ 2^{β−1}(1 − o(1)): β = 1/2 gives 1/√2, β = 1 gives 1 (no gain), and
only β < 1/2 would give ρ < 1/√2 (App. H l.2995–2997 states the same law without proof).

### 3.3 The Fock space: ρ ≥ 1/√2 − O(log λ/λ) [R]

**Corollary 3.5.** For the pieces of Theorem B (any dual families a_μ, b_ν, any h with p(h) ≥ 2^λ,
S ∋ 0), with the certified costs,

    ρ ≥ 1/√2 − [ √2·C_HR + log₂(2h) + C_HR + (c/2)·log₂(2λ) ] / (2λ),   h ≤ ((λ + C_HR)/c_HR)² + 1,

so ρ ≥ 1/√2 − O((c+1) log λ/λ).  *Proof.* By (3.2) at s = 0 and (46): 4ρλ + c log₂(2λ) ≥ 2 log₂ p(2h)
≥ 2(c_HR√(2h) − log₂(2h) − C_HR), and 2^λ ≤ p(h) ≤ 2^{c_HR√h + C_HR} gives √h ≥ (λ − C_HR)/c_HR;
the bound on h is the minimality of h (p(h−1) < 2^λ with the lower bound of (46)). ∎

The paper's `GeneralPieces.Half.Consts.exists_cst2` proves the matching upper bound
c^row_s + c^col_s ≤ 4(1/√2)λ + c·log(2λ) (`ClauseBound.Inst.Half.Cst.caps`); so for the certified
costs the value 1/√2 is **exact**, and the finite-size behaviour is 1/√2 + Θ(log λ/λ)
(`rho_growth_law.out`: 1.06 at λ = 8, 0.91 at 16, 0.83 at 32, 0.78 at 64, 0.75 at 128).

### 3.4 Certified versus true costs [N]

Theorem 3.3 bounds the costs that the two-order structure *certifies*. The Lean `caps` is about the
numbers c^row_i for which a factorization is exhibited, and a cleverer factorization could exist if
the true rank is smaller. For Theorem B's pieces the true ranks were computed exactly for h ≤ 9
(N = p(h) ≤ 30, matrices up to 900×900, ranks mod 2^61−1, `rho_fock_pieces_3_7.out`,
`rho_fock_pieces_8_10.out`, extending `pieces_fock_ranks.py` from h ≤ 6):

| h | N | pieces with count < N² | true/count (row rank, uncapped s) | worst-case ratio |
|---|---|---|---|---|
| 7 | 15 | s ≤ −3 | 182/195, 131/139, 92/97, 64/67, 44/45 | 0.93 |
| 8 | 22 | s ≤ −3 | 353/373, 259/272, 187/195, 134/139, 94/97 | 0.95 |
| 9 | 30 | s ≤ −3 | 653/684, 488/508, 360/373, 264/272, 190/195 | 0.95 |
| 10 | 42 | s ≤ −2 | 1513/1597, 1166/1212, 884/915, 664/684, 495/508 | 0.95 |

(By the symmetry s ↔ −s the column ranks behave the same: at h = 10, s = 3: 1166/1212.) The true
rank is 93–97 % of the count wherever the count is below N², the ratio increasing with h; for
|s| ≤ 1 the true rank is N² = p(h)², the cap (at these sizes Σ_{i≤2h} p(i) > p(h)², which persists
up to h ≈ 15, beyond exact computation: at h = 10 the matrices are 1764×1764 and the build took 19
minutes; the family-independence check of §3.5 at h = 10 exceeded memory and was done for h ≤ 9).
The identity Σ_s A_s = h!F, Lemma 9(a) (both orders give the same tensor) and `terms` were
re-verified for h ≤ 10. So for this construction the certified
costs are the true costs up to O(1) bits [N]; a rigorous rank lower bound for the specific
matrices (x,y)×(u,v) ↦ ⟨t^{μ(u)}, Q_s(a_{μ(x)}, b_{μ(v)}) t^{μ(y)}⟩ is **not** provided here (it would
need a triangularity argument isolating the top term i = 2h; none of the natural statistics —
number of parts, largest part — is monotone across the terms).

### 3.5 No reweighting and no sub-family helps [R]+[N]

For the pieces of Theorem B, Σ_s s^k Q_s(a,b) = (ω_1∂_{ω_1})^k F|_{ω_1=ω_2=1} for the Laurent polynomial
F = Σ_s F_s ω_1^s ω_2^{−s} of the paper's proof, and (1/j!)∂_{ω_1}^j F(w,w) is the weight-conserving part
of Y(a_{(2h−1−j)}b, w) by the n-th product formula (proof of Lemma 4.1 below with n = 2h−1−j); so
Σ_s s^k A_s is a linear combination of the zero modes o(a_{(2h−1−j)}b), j ≤ k, with nonzero coefficient
at j = k.
Numerically: the 4h+1 tensors A_s span a space of dimension exactly 4h for every h ≤ 9; the unique
relation is Σ_s s·A_s = 0 (verified directly for h ≤ 6; it is the zero mode of V_1 = ℚt_1, which is
α_0 = 0 on the Fock space); Σ_s s²A_s = g(x,v)[y=u]
with g not a multiple of [x=v] (zero mode of V_2 ∋ ω: a multiple of L_0 = h·Id); Σ_s s³A_s is not of
the form g[y=u] (`rho_moment_relations.out`). Consequently every representation
Σ_s g(s)A_s = d'·F has g(s) = (d'/h!)(1 + κ s), hence g(0) ≠ 0: **the most expensive slice s = 0 cannot
be dropped or down-weighted**, and no proper sub-family of the slices is a multiple of the crossing
(a sub-family would give a second relation). Regrouping (pieces that are sums of several A_s) only
adds ranks in the certified count; a true-rank drop in a sum is not excluded but was not seen.

## 4. Hypothesis (H): why the spread is 2h

### 4.1 The sum of the slices is the zero mode of the top pole [R]

Setting: a vertex algebra V = ⊕_{E≥0} V_E (any field of characteristic 0), Y(a,z) = Σ_n a_{(n)} z^{−n−1},
a ∈ V_{h_a}, b ∈ V_{h_b}, and the paper's modes a[r] := a_{(h_a−1−r)} of degree r (so
Y(a,z) = Σ_r a[r] z^{r−h_a}). For an integer H ≥ 0 define the slices (display (48) for homogeneous a)

    Q_s^{(H)}(a,b) := Σ_{i=0}^{H} (−1)^i C(H,i) · a[s−h_a+i] · b[h_a−s−i]        (s ∈ ℤ),

and Q'_s with the two factors exchanged in every product.

**Lemma 4.1.** Suppose a and b are mutually local of order H: (z−w)^H[Y(a,z),Y(b,w)] = 0,
equivalently a_{(n)}b = 0 for all n ≥ H. Then on every V_E:
(a) Q_s^{(H)}(a,b) = Q'_s^{(H)}(a,b) for all s;
(b) Σ_s Q_s^{(H)}(a,b) = o(a_{(H−1)}b), where o(c) := c_{(wt c − 1)} is the weight-preserving mode.
In particular, if H = h_a + h_b then a_{(H−1)}b ∈ V_0; if V_0 = 𝔽·1 then Σ_s Q_s = (a_{(H−1)}b)·Id,
which is Lemma 9(c). If H > the true locality order then a_{(H−1)}b = 0 and Σ_s Q_s = 0.

*Proof.* Let 𝔉(z,w) := (z−w)^H Y(a,z)Y(b,w) = (z−w)^H Y(b,w)Y(a,z) (equal by locality). On a fixed
matrix coefficient between V_E and V_{E'}, 𝔉 lies in both V((w))((z)) and V((z))((w)) and has, by
weight, finitely many terms: it is a Laurent polynomial. Its weight-preserving part is
z^{H−2h_a} w^{h_a−h_b} Σ_s Q_s (z/w)^s, and the same expansion of the other product gives Q'_s: this is
(a). For (b) use the n-th product formula, valid in every vertex algebra (Lepowsky–Li, *Introduction to
vertex operator algebras*, §3.1; Kac, *Vertex algebras for beginners*, §4.6): Y(a_{(n)}b, w) = Res_z [ι_{z,w}(z−w)^n Y(a,z)Y(b,w) − ι_{w,z}(z−w)^n Y(b,w)Y(a,z)]. With
n = H−1 both products are (z−w)^{−1}𝔉 expanded in the two domains, so
Y(a_{(H−1)}b, w) = Res_z δ(z−w)·𝔉(z,w) = 𝔉(w,w). The weight-preserving part of Y(c,w) is o(c)·w^{−wt c}
with wt c = h_a + h_b − H, and 𝔉(w,w)'s weight-preserving part is w^{H−h_a−h_b} Σ_s Q_s. ∎

(The paper proves (a), (b) for the Heisenberg algebra directly: "F = Σ_s F_s ω_1^s ω_2^{−s},
F(1,1) = Σ_s F_s" at l.1900, and "F(1,1) = μ!ν!Γ_{μ,ν}[σ = σ']" with Γ = a[−h]b.)

**Corollary 4.2.** In a vertex algebra with V_0 = 𝔽·1, a decomposition of the crossing by slices
Q_s^{(H)}(a_x, b_v) with **the pairing given by the top pole** (a_x[−h]b_v = d[x=v], as in Lemma 10)
has H = 2h, so (3.2) applies with spread 2h: c^row_s + c^col_s ≥ f(2h+s) + f(2h−s). [R]

### 4.2 The zero-mode loophole [R for the constraints, C for the verdict]

Corollary 4.2 does not exclude H = 2h − w with w > 0: then Σ_s Q_s(a_x,b_v) = o(c_{x,v}) with
c_{x,v} := a_{x,(H−1)}b_v ∈ V_w, and the pieces would need o(c_{x,v})|_{V_h} = d[x=v]·Id on the labels.
What this requires:

1. a_{x,(n)}b_v = 0 for all n ≥ H and all x, v (locality of order H). For n = 2h−1 this says that
   the spans A = ⟨a_x⟩, B = ⟨b_v⟩ ⊂ V_h are orthogonal for the top-pole form a[−h]b, which is
   nondegenerate on V_h (Lemma 10: ⟨t^μ, t^ν⟩ = z_μδ_{μν}); and nondegeneracy of the pieces forces
   dim A = dim B = N (a relation Σc_x a_x = 0 would give Σ_x c_x[x=v] = 0). So p(h) ≥ 2N: λ ↦ λ+1,
   harmless. For n ∈ [H, 2h−2] the conditions are bilinear maps β_n: V_h⊗V_h → V_{2h−1−n} vanishing
   on A⊗B; their total target dimension is Σ_{k<w} p(k) ≈ p(w).
2. Id_{V_h} must lie in o(V_w)|_{V_h}. Numerically this holds for all 2 ≤ w ≤ 8 and h ≤ 6
   (`rho_zero_mode.out`: dim o(V_w)|_{V_h} grows from 1 at w = 2, where o(t_1²) = 2h·Id, towards
   p(h)²; Id ∈ span in every case with w ≥ 2, and o(V_1) = 0). So the loophole is **not** closed by the zero modes.
3. The gain: with spread H = 2h − w the certified cost at s = 0 is 2f(2h − w/2) instead of 2f(2h).

Dimension count [C]: a pair (A, B) of N-dimensional subspaces of V_h with D ≈ p(w) generic bilinear
forms vanishing on A⊗B exists only if 2N(p(h) − N) ≥ DN², i.e. p(h) ≥ N(1 + p(w)/2), i.e. the label
weight h' satisfies f(h') ≥ λ + f(w) − 1. Writing w = θh' and f = c√E: λ ≈ c√h'(1 − √θ) and the cost
is 2c√h'·√(2 − θ/2), so ρ ≈ √(2 − θ/2)/(2(1 − √θ)), which is 1/√2 at θ = 0 and *increases* with θ.
Under genericity the loophole loses more in labels than it gains in spread. The forms a_{(n)}b of the
Heisenberg algebra are not generic (for monomials they are contraction rules with coefficients
C(−k−1, μ_i−1), C(l−1, μ_i−1)), and for monomial-spanned A, B the conditions are very restrictive
(a single-part a = t_h has only its top pole with any monomial having a part in (0,h)); I could neither
prove that no asymptotically useful isotropic pair exists nor find one. **Status: open, expected useless.**

## 5. Hypothesis (G): why the growth is √

### 5.1 Local fields are not sparse [R]

**Proposition 5.1.** Let a(z) = Σ_{n∈ℤ} a_n z^{−n−1} and b(w) be formal distributions with
coefficients in End(V), local of order H ((z−w)^H[a(z),b(w)] = 0) and not commuting ([a(z),b(w)] ≠ 0).
Then a_n ≠ 0 for all but at most H−1 integers n. The same holds for the modes of b.

*Proof.* By the decomposition theorem for local formal distributions (Kac, *Vertex algebras for
beginners*, Thm 2.3), [a(z),b(w)] = Σ_{j=0}^{H−1} c^j(w)·∂_w^j δ(z−w)/j! with c^j(w) = Res_z (z−w)^j[a(z),b(w)].
The coefficient of z^{−n−1} in ∂_w^jδ(z−w)/j! is C(n,j)w^{n−j}, so [a_n, b(w)] = w^n Σ_j C(n,j) c^j(w) w^{−j}.
Let j_0 be the largest j with c^j ≠ 0 and pick a matrix coefficient and a power w^{m_0} where c^{j_0}
has a nonzero coefficient γ. The coefficient of w^{n+m_0−j_0} in Σ_j C(n,j)c^j(w)w^{−j} is a polynomial
in n of degree j_0 with leading coefficient γ/j_0! ≠ 0; it vanishes for at most j_0 ≤ H−1 values of n.
For every other n, [a_n, b(w)] ≠ 0, hence a_n ≠ 0. ∎

So **any graded space carrying a locality identity of some order between nontrivially non-commuting
fields has operators of every degree n (outside a finite set)**. A "sparse" Heisenberg algebra
(oscillators ∇_{±k} only for k in a sparse set K, Fock space ℚ[t_k : k ∈ K] with restricted-partition
growth) has no local fields: the field Σ_{k∈K} ∇_k z^{−k−1} is not local with anything it does not
commute with. The delta-function identity (49) of the paper's proof, Σ_k k ω_1^{−k−1}ω_2^{k−1} = ∂_{ω_2}ε_+,
is where all k are used.

### 5.2 A free field with a nonzero top pole has partition growth [R]

**Proposition 5.2.** Let V = ⊕_{E≥0} V_E over a field of characteristic 0, 1 ∈ V_0, and let operators
a_n: V_E → V_{E−n} (n ∈ ℤ) satisfy [a_m, a_n] = κ_m δ_{m+n,0}·Id with κ_m ≠ 0 for m ≥ m_0, and a_n 1 = 0
for n ≥ 0. Then the vectors v_λ := a_{−λ_1}⋯a_{−λ_k}1, λ = (λ_1 ≥ … ≥ λ_k ≥ m_0) a partition of E, are
linearly independent, so dim V_E ≥ p_{≥m_0}(E) (partitions into parts ≥ m_0) and
log dim V_E ≥ c_HR√E − O(m_0 log E).

*Proof.* Induction on E. Suppose Σ_λ c_λ v_λ = 0 with some c_λ ≠ 0; let m be the largest part
occurring among the λ with c_λ ≠ 0 and t the largest multiplicity of m among those. a_m commutes
with a_{−n} for n ≠ m, and a_m w = 0 for w a product of a_{−n}, n < m, applied to 1. Hence
a_m^t v_λ = t!κ_m^t v_{λ∖{m^t}} if mult_m(λ) = t and 0 if mult_m(λ) < t. Applying a_m^t to the
relation gives a nontrivial relation among the v_{λ∖{m^t}} of weight E − tm (distinct for distinct λ),
contradicting the induction hypothesis (E = 0: v_∅ = 1 ≠ 0). The growth statement is the standard
asymptotic of restricted partitions (the generating function differs from P(q) by the polynomial
Π_{k<m_0}(1−q^k), which does not change the dominant singularity). ∎

In a vertex algebra, a, b ∈ V_h with a_{(2h−1)}b = 1 give, by the commutator formula,
[a[r], b[−r]] = C(r+h−1, 2h−1)·Id + Σ_{j<2h−1} C(r+h−1,j)·o(a_{(j)}b): a Heisenberg-type central term
plus zero modes of the lower poles. When the lower poles vanish (generalized free field: bosons,
fermions, the βγ system, lattice vertex operators with the Heisenberg they generate), Proposition 5.2
applies and β = 1/2. When they do not, the PBW argument fails — in the (2,5) minimal model
L_{−2}²1 and L_{−4}1 are dependent — and the growth is still exp(c√E) with c_eff > 0 but the proof is
modular invariance:

**[K] Zhu / Gaberdiel–Neitzke / Dong–Mason.** For a C₂-cofinite vertex operator algebra V ≠ ℂ of
CFT type, log dim V_E = 2π√(c_eff E/6)(1+o(1)) with c_eff = c − 24h_min > 0. Hence β = 1/2 and, by
Corollary 3.4, **every decomposition by locality slices in a C₂-cofinite VOA has ρ ≥ 1/√2 − o(1)**
regardless of c_eff (the constant cancels in f(2h)/(2f(h))).

What is **not** available: a proof that an arbitrary ℕ-graded vertex algebra with V_0 = 𝔽1 and a
nonzero top pole between weight-h vectors has log dim V_{2h} ≥ (√2 − o(1)) log dim V_h; and a fortiori
nothing for abstract two-order structures that are not vertex algebras. This is the open core.

### 5.3 The general law, numerically [N]

`rho_growth_law.out`: f(2h)/(2f(h)) for f = log₂ p is 0.7277 at h = 1000 and 0.7151 at h = 10^4
(→ 0.7071); for partitions into squares (β = 1/3) it is 0.676, 0.654, 0.643 at h = 10³, 10⁴, 10⁵
(→ 2^{−2/3} = 0.630); for binary partitions (β → 0) 0.614, 0.586, 0.569 (→ 1/2). These are the values
ρ **would** take if the corresponding Fock spaces carried locality-type two-order structures; by
Proposition 5.1 they do not.

## 6. Break attempts (Task 3)

For each candidate: the grading and β, whether a nondegenerate pairing of 2^λ labels is available,
whether a two-order identity with poly(λ) terms per piece exists, and the resulting ρ.

| structure | grading, β | pairing | two-order with poly terms | ρ | why it fails |
|---|---|---|---|---|---|
| Heisenberg Fock space ℚ[t_1,t_2,…] (Theorem B) | weight, p(E), β = 1/2 | top pole z_μδ_{μν} | locality, 2h+1 terms per slice | 1/√2 | (G) and (H) both hold; this is the extremal case of §3 |
| n-colour bosons, free fermions / infinite Clifford algebra (parts distinct), βγ system | β = 1/2 (constants differ) | top pole | locality | 1/√2 | Prop. 5.2; the constant cancels |
| lattice, affine, Virasoro, W-algebras, minimal models, any C₂-cofinite VOA | β = 1/2 | top pole | locality | 1/√2 | [K] modularity, c_eff > 0 |
| q-analogues (q-Heisenberg, quantum affine), Hall algebras | same graded dimensions as q = 1 | yes | locality (deformed) | 1/√2 | characters are q-independent; quantum groups at roots of unity are finite-dimensional (ungraded) |
| finite Clifford algebras, octonions (eight squares, Def. 5) | ungraded; tensor powers: f linear in #blocks, β = 1 | Hurwitz–Radon (74) | yes but each product in one order only | 11/12 counted, 10.81/12 by ranks | β = 1: 2^{β−1} = 1; the gain is a constant from the commutation structure, not from growth |
| group algebras, Pauli/Weyl–Heisenberg, Fourier/Hadamard | ungraded; SWAP = (1/N)Σ_{a,b} X^aZ^b ⊗ (X^aZ^b)^† | yes | N² terms of OSR 1 and rank N; grouping m terms costs log m in both directions | → 1 | no grading: all terms pass through spaces of dimension N; symmetrized (type) classes give 0.80–0.87 (`pieces.md` §4) |
| binary codes, lattices as combinatorial gradings (Hamming weight) | f(E) = log C(λ,E) = λH(E/λ): linear in λ at fixed ratio, β = 1 | yes | tensor-power type | ≥ 0.80 | same as above |
| sparse Fock space ℚ[t_k : k ∈ K], K = squares / powers of 2 | restricted partitions, β = 1/3 / polylog | top pole z_μδ_{μν} nondegenerate | **no**: no local fields (Prop. 5.1); the naive Leibniz identity b(∇)a(t) = Σ_{ν'}(1/ν'!)M_{∇^{ν'}a}∘(∂^{ν'}b)(∇) has p(w)² terms at contraction weight w and gives pieces of cost up to 4λ | ≈ 1 (naive) | **this is the structure a counterexample needs** (§7) |
| Weyl algebra in n variables, V = ℚ[t_1..t_n] by total degree | f = (n−1)log E, β → 0 | Fischer pairing | Leibniz only, C(w+n−1,n−1) terms per contraction weight; slices indexed by w ∈ [0,h] | ≈ 1, and \|I\| = h+1 = 2^{λ/(n−1)} | no fields in one variable; the slice count is exponential in λ (`rate.md` §3.1's "f = d log E" case is not realizable as a locality structure) |
| commutative graded algebras (polynomial rings, Reed–Solomon evaluation, orthogonal polynomials of one variable) | polynomial growth | a_x b_v = [x=v]·1 forces a_x to be units ⇒ monomials ⇒ one label per degree | trivial (XY = YX) | 1/2 + o(1) | \|I\| ≥ N pieces, violating (c) by 2^{Θ(λ)} |
| free fields in d > 2 dimensions (higher-dimensional vertex algebras) | oscillator multiplicity n^{d−2}, β = (d−1)/d | top pole | locality | 2^{β−1} > 1/√2 | more modes per weight: worse |

Two structural facts behind the table: (i) **grading is what lets 2^λ labels share poly(λ) passing
spaces** — ungraded algebras pay log(#terms) in both directions; (ii) **the repackaging of all
contraction patterns into O(h) operators a[r] indexed by one integer is locality**: the generating
functions (49)–(51) need the delta function, hence all modes (Prop. 5.1), hence partition growth for
free fields (Prop. 5.2). A sub-√ graded space would have to be reached by a different mechanism.

## 7. Verdict (Task 4)

**Proved.** (i) Rank inequalities (R1)–(R3), ρ ≥ 1/2, and their insufficiency beyond 1/2 (§2.1–2.2);
rank(F − A⊗B) ≥ N(N−1)/10 (Prop. 2.3). (ii) The spread lemma: for graded two-order decompositions
with certified costs, c^row_s + c^col_s ≥ f(h−h_0+s+H) + f(h+h_0−s) (Thm 3.3), hence
ρ ≥ f(2h)/(2f(h)) − c log(2λ)/(4λ) when H = 2h and 0 ∈ S (Cor. 3.4), and ρ ≥ 1/√2 − O((c+1)log λ/λ)
for every decomposition by locality slices on the Fock space (Cor. 3.5) and, by [K], on every
C₂-cofinite vertex operator algebra. (iii) H = 2h whenever the pairing is the top pole (Lemma 4.1,
Cor. 4.2); for Theorem B's pieces the slice s = 0 cannot be dropped or down-weighted (§3.5).
(iv) Local fields are never sparse (Prop. 5.1) and free fields with a nonzero top pole have
partition growth (Prop. 5.2).

**The exact statement that remains open.** Let ρ* = inf{ρ : `PiecesCounted.Exist ρ c` for some c}.
Is ρ* < 1/√2? Restricted to graded two-order decompositions (Def. 3.1) with certified costs,
Theorem 3.3 reduces this to the disjunction:

 (O-H) a locality-type decomposition with spread H ≤ (1−ε)·2h, i.e. the zero-mode loophole of §4.2
   realized with o(a_{x,(H−1)}b_v)|_{labels} = d[x=v]Id, a_{x,(n)}b_v = 0 for n ≥ H, and labels of
   weight h with f(h) ≤ (1+o(1))λ; or
 (O-G) a graded space with max_{E≤2h} log dim V_E ≤ (√2 − ε) log dim V_h ≥ (√2 − ε)λ carrying,
   for 2^λ labels of weight h, two-order identities with poly(λ) terms per piece and poly(λ)
   pieces whose sum is a nondegenerate pairing times the identity; or
 (O-T) pieces with true ranks far below their certified counts (not seen for h ≤ 9), or pieces
   that are not of the graded two-order form at all (the unrestricted problem of §2.2, HWY-hard).

**Minimal counterexample structure.** The cheapest target is (O-G) on the sparse Fock space
ℚ[t_k : k ∈ K] with K = {k²} (β = 1/3, so ρ would be 2^{−2/3} = 0.63 and α' = 2/3; |I| ≈ λ³ is still
polynomial): the pairing z_μδ_{μν} is there, the operators ∇_{±k²} are there, what is missing is a
replacement for the two-variable generating-function identity (49)–(51) — some family of operators
X_x^{(j)}, Y_v^{(j)} indexed by j in a set of size poly(λ) (not by partitions, which is what the naive
Leibniz expansion gives) such that Σ_j Y_v^{(j)}X_x^{(j)} = Σ_j X'^{(j)}_x Y'^{(j)}_v for each slice.
Proposition 5.1 says this family cannot come from local fields in one formal variable; it would
have to be a new kind of identity in U(sparse Heisenberg). I found none and know no obstruction
beyond Proposition 5.1. If it exists, Theorem A as proved (`ExplicitCost.recursionSolves`, general
in ρ) gives 2^{O(U/(log U)^{1−β})} at once, and with β = 1/3 the dense permanent/HC bound becomes
2^{O(n²/(log n)^{2/3})}.

**My estimate.** (O-H) is a dimension-count loser [C]; (O-G) would contradict the pattern of every
known graded algebra with a nondegenerate top pairing (all have β = 1/2 or worse), but no theorem
excludes it; (O-T) is the unrestricted Hurwitz problem. So **ρ ≥ 1/√2 is a theorem for the family
Appendix H describes (locality slices with top-pole pairing on any space of √ growth, in
particular all C₂-cofinite VOAs and all free fields), and open outside it.**

## Scripts

| script | what it does | output |
|---|---|---|
| `rho_fock_lib.py` | exact implementation of (47) via (O2), the families of Lemma 10, the pieces (53) in either order | — |
| `rho_fock_pieces.py` | identity Σ_s A_s = h!F, Lemma 9(a), true row/column ranks vs counts, linear (in)dependence of the A_s, ρ_true, ρ_count, the law, h ≤ 10 | `rho_fock_pieces_3_7.out`, `rho_fock_pieces_8_10.out` |
| `rho_single_terms.py` | ranks of the single terms T_{0,i}: column rank ≤ p(2h−i), row rank ≈ N² | `rho_single_terms.out` |
| `rho_moment_relations.py` | Σ_s s^k A_s for k = 1, 2, 3 (the relation Σ_s sA_s = 0; zero modes of V_2, V_3) | `rho_moment_relations.out` |
| `rho_zero_mode.py` | dim o(V_w)\|_{V_h} and whether Id is in it (loophole precondition) | `rho_zero_mode.out` |
| `rho_growth_law.py` | exact p(E) to 2·10⁴; counted max_s(c^row_s+c^col_s)/(4λ) for λ ≤ 128; f(2h)/(2f(h)) for p, square partitions, binary partitions | `rho_growth_law.out` |

All ranks are computed modulo 2^61−1 (a lower bound on the rank over ℚ; equality is generic and the
counts are upper bounds, so the comparison "true ≤ count" is exact and "true ≈ count" is safe).
