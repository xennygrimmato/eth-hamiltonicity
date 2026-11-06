# Δ_3: what can be proved about the three transversal triangles under rows and columns

6 Nov 2026. Read for this note: `engine3-open-door.md` §1.6–1.7, §2.3, §3.1–3.2a, §4; `engine3-delta3.md`; `engine3-delta3b.md`;
`engine2-decorrelated.md` §7–8 (Theorem 5, lossy lemma, Conjecture 8.1, §8.6, §8.7); Majdoddin arXiv 2610.41622 §4.4 (Example
4.10, Lemma 4.11, rectangle-content conjecture), §4.8. Scratch computations (ALS at N₀ = 2 with the project's `d3lib.py` and `als_runs.py` from `scripts/engine3-delta3/`, and a
small rank search), copied to `research/scripts/engine3-delta3-proof/` (`als_*.out`, `alsL_*.out`, `analyze*.py`, `cyc.py`;
run from a directory containing `d3lib.py`). Tags: **[R]** proved here, **[K]** known (source named), **[N]** numerical / exact
computation, **[C]** conjectured or open.

## 0. Verdict

The task asked for (A) no trade at all, (B) `max_i (c_row + c_col) ≥ 9λ − o(λ)`, or (C) an improvement of the flattening floor
`4λ` for the cheapest-merge cost. Exact status:

* **(B) is proved, but it is trivial and it is not the statement the notes call "ρ_Δ ≥ 1/2" (Theorem 1 [R]).** The uniform
  quantum functional on the three row groups gives, for every family of `T` pieces summing to `f_Δ`, a piece with
  `c_row ≥ 9λ − (3/2)log₂T`; hence `c_row + c_col ≥ 9λ − (3/2)log₂T` for that piece. The same holds for every two-merge
  configuration whose edges all cross both merges, hyperedge pieces included: the **game value** of §1.7 satisfies
  `V ≥ Eλ/2` always, i.e. **ρ ≥ 1/2 in the sense of Theorem A for every two-merge configuration under the D1 cost.** This is
  Majdoddin's two-merge floor (Prop. 4.8) extended to hyperedge configurations. Consequences: the §1.7 criterion
  "`c_1 + c_2 + 3log₂T < 9m₀`" is unsatisfiable at **every** `N₀` and every `T` (the exact refutations of `engine3-delta3b.md`
  §1 and `engine3-open-door.md` §3.2a are instances; the planned `N₀ = 8` enumeration is unnecessary), and a two-merge identity
  on Δ_3 can never give `α′ > 1` in Theorem A's recursion. What *is* open on Δ_3 is the **min-floor**
  `φ := liminf max_i min(c_row(A_i), c_col(A_i))/λ` (the quantity behind Conjecture 8.1 and the `Σ_t 2^{min cost}` framework of
  `engine2-decorrelated.md` §8), for which `4 ≤ φ ≤ 9` is all that is known; §1 states the three quantities and their relations
  exactly (`(A) ⟹ φ ≥ 6`).
* **(A) and (C) remain open [C], and this note records precisely why: every tool tried (ideas (1)–(5) of the task) is a
  functional of node-locally processed tensors bounded by flattening ranks, and the flattening world certifies exactly 4
  (`flatcert4.out`).** §4 gives the exact form that an argument beyond 4 must take and the exact form a counterexample must have
  (a two-piece operator statement: a row-structured operator within rank `2^{aλ}` of a leg-permutation operator).
* **New partial results [R].** (i) *Diagonal pieces do not trade at all* (Theorem 2): if every piece has the form
  `r_i(x)·[x = y]` (every block decomposition of `⟨N³,N³,N³⟩` along bond values, every bond-value indicator ansatz, and anything
  diagonal in a common edge-wise basis), then every piece has `c_row, c_col ≥ log₂|supp r_i|` (Loomis–Whitney) and some piece has
  both `≥ 9λ − log₂T`: `φ = 9` and (A) hold on this class, over every field. (ii) *Partial fixings cannot beat the core floor*
  (Lemma 3.4): fixing any set of legs and then bounding the column piece as a row network ("hub routing") gives at most
  `|E′| − L_off ≤ 3`. (iii) *Reduction lemmas* (§3.1–3.2): the sum of row networks is a row network with summed bonds; the
  two-piece operator form `J = R′ + L`, `rank L ≤ 2^{aλ}`.
* **New construction-side facts.** (iv) The "straightened-edge" family (§5 [R]): replacing the three edges of one column pair by
  horizontal edges gives `f_Δ = R + C` with `c_row(R) = 6λ` exactly and `c_col(C) = 6λ + log₂((2N³ − 2N)/3) = 9λ − log₂(3/2) +
  log₂(1 − N⁻²)`: a **constant** gain of 0.585 bits on the min-floor at every `N`, the first exact non-diagonal two-piece identity
  on Δ_3 (the diagonal trick gives only `log₂(1 − 1/N) → 0`). (v) ALS at `N₀ = 2` [N]: the exact two-piece identities it finds
  at costs (6, 8) and (7, 8) are exactly this family (verified by edge-cut ranks); every two-piece shape tested with both costs ≤ 7
  fails (residuals 0.52–0.71 after 1500 sweeps). `min rank(Π_σ − A⊗B⊗C) = (2N³−2N)/3` at `N = 2, 3` [N], attained by
  `A = B = C = I` [R].

---------------------------------------------------------------------------------------------------

## 1. Setting, exact definitions, and the three quantities

**Configuration.** Nodes `(r,c) ∈ Z_3²`; edges `(r,c)–(r′,c′)` with `r + c ≡ r′ + c′`, `r ≠ r′`: three disjoint triangles
`T_s = {(0,s),(1,s−1),(2,s−2)}`, each meeting every row and every column once. Every node has two legs (one per incident edge),
each of dimension `N = 2^λ`; `f_Δ = ⊗_e I_e` (18 legs, `N^{18}` entries). **Latin-square labelling [R]:** every edge lies in exactly
one row pair `ρ ∈ {01,02,12}` and one column pair `γ ∈ {01,02,12}`, and the map `e ↦ (ρ(e), γ(e))` is a bijection onto the nine
pairs (the edge `(r,c)–(r′,c′)` has `ρ = {r,r′}`, `γ = {c,c′}`; two edges with the same `(ρ,γ)` would lie in the same triangle,
which has only one edge per row pair). So `f_Δ` is a 3×3 array of `N`-dimensional identities; under rows the bond `ρ` carries the
three edges of array row `ρ`, under columns the bond `γ` carries the three edges of array column `γ`. This is the statement
"every edge is the lone diagonal of its rectangle" (`d = 1, a = 0`).

**Row and column networks (D1 cost).** With `V_r = ⊗_c V_{rc}` (dimension `N⁶`) the row-group spaces, a row network with bonds
`d = (d_01, d_02, d_12)` is `R = Σ_{i,j,k} W_0(i,j) ⊗ W_1(i,k) ⊗ W_2(j,k)`, `W_0(i,j) ∈ V_0` etc.; equivalently **`R` is a
restriction of the matrix-multiplication tensor `⟨d_01,d_02,d_12⟩`** (viewed in `C^{d_01 d_02} ⊗ C^{d_01 d_12} ⊗ C^{d_02 d_12}`)
by the three linear maps `W_r`. Cost `c_row(R) = log₂(d_01 d_02 d_12)`, minimised over representations. Cut bound [K, §1.6]:
`rk(R; V_r | rest) ≤ d_{rr′} d_{rr″}`, so `Π_r rk_r(R) ≤ 2^{2c_row(R)}`. Column networks likewise on `V_c = ⊗_r V_{rc}`. Under rows
`f_Δ = ⟨N³,N³,N³⟩` (raw cost `9λ`), under columns the same. Any tensor on the 18 legs is a row network of cost `≤ 12λ` (hub with
bonds `(N⁶, N⁶, 1)`), so the trivial upper bound on every other-merge cost is `12λ`.

**Three quantities** for a family `A_1, …, A_T` with `Σ A_i = f_Δ` (`T = 2^{o(λ)}` throughout):

1. the **game value** `V = max_{x∈Δ_T} min_k Σ_i x_i c_k(A_i) = min_{q∈Δ_2} max_i ⟨q, c(A_i)⟩` (§1.7), which governs a Theorem-A
   level in which the family is used independently on many configurations (the worst term mixes pieces in proportion `x`);
   `ρ := V/(9λ)`;
2. the **sum criterion** `Σ := max_i (c_row(A_i) + c_col(A_i))`; `V ≤ Σ/2` (take `q = (½,½)`), and "no trade" (A) is `Σ ≥ 18λ − o(λ)`;
3. the **min-floor** `M := max_i min(c_row(A_i), c_col(A_i))`, which governs `Σ_t 2^{min cost}` (one level, one configuration,
   each term contracted under its own cheaper merge: `engine2-decorrelated.md` §8.1, Conjecture 8.1); `M ≤ V`.

Relations [R]: `M ≤ V ≤ Σ/2 ≤ 12λ`; `Σ ≥ 18λ − o(λ)` forces `min(c_row, c_col) ≥ 6λ − o(λ)` for the maximising piece (each cost is
`≤ 12λ`), so **(A) ⟹ `M ≥ 6λ − o(λ)`**; the flattening floor `4λ` and the core floor `3λ` are bounds on `M`; the Conjecture-8.1
analogue on Δ_3 is `M ≥ 4.5λ − o(λ)` ("`Σ_t 2^{min cost} ≥ N^{4.5}`"); the trivial decomposition gives `M = 9λ`.

---------------------------------------------------------------------------------------------------

## 2. Theorem 1: the two-merge floor holds for hyperedge configurations; (B) is trivial [R]

**Theorem 1.** Let `C` be any configuration under two merges whose groups are `P_1, P_2`, with `E` edges all crossing both
merges, raw cost `Eλ` under each merge, and let `Σ_{i≤T} A_i = d·f_C` (`d ≠ 0`), the `A_i` arbitrary tensors with D1 costs
`c_k(A_i)` (merge `k` has `r_k ≤ 3` groups meeting `C`; for `r_k = 2` read `ν = 1`, for `r_k = 3` read `ν = 3/2` below). Then for
each `k` some piece has `c_k(A_i) ≥ Eλ − ν_k log₂T`. Consequently
`max_i (c_1(A_i) + c_2(A_i)) ≥ Eλ − ν log₂T` and `V ≥ Eλ/2 − (ν/2)log₂T`, i.e. `ρ ≥ 1/2 − o(1)`.

*Proof.* Under merge `k` with three groups, `f_C` is the graph tensor of a 3-vertex multigraph with `E` edges, i.e.
`⟨N^{e_01}, N^{e_02}, N^{e_12}⟩` with `e_01 + e_02 + e_12 = E`. The uniform quantum functional `F = F^{(1/3,1/3,1/3)}` of
Christandl–Vrana–Zuiddam [K] is monotone under restriction, subadditive (`F(S + T) ≤ F(S) + F(T)`, since `S + T` is a restriction of
`S ⊕ T`), satisfies `F(T) ≤ Π_x rk_x(T)^{1/3}`, and equals `N^{2E/3}` on `f_C` (a free tensor; its support functional is
`2^{(1/3)Σ_x H(P_x)}` maximised by the uniform distribution on the `N^E` support points, each marginal uniform on `N^{e_x}` values with
`Σ_x e_x = 2E`). For a piece, by the cut bound `F(A_i) ≤ (Π_r rk_r(A_i))^{1/3} ≤ 2^{2c_k(A_i)/3}`. Subadditivity:
`N^{2E/3} ≤ Σ_i F(A_i) ≤ T·2^{(2/3)max_i c_k(A_i)}`, so `max_i c_k(A_i) ≥ Eλ − (3/2)log₂T`. (For two groups use the flattening rank
`N^E` of `f_C` and `rk ≤ 2^{c_k}`: `max_i c_k ≥ Eλ − log₂T`.) The piece full under merge 1 has `c_1 + c_2 ≥ Eλ − ν log₂T`. For the
game value, let `i_1, i_2` be the full pieces and `x = (½ on i_1, ½ on i_2)`: `Σ_i x_i c_k(A_i) ≥ ½(Eλ − ν log₂T)` for both `k`, so
`V ≥ Eλ/2 − (ν/2)log₂T`. ∎

*Remarks.* (a) Over `C` by CVZ; over an arbitrary field the same argument runs with Strassen's upper support functional
`ζ^θ` [K, Strassen 1991], which is monotone, subadditive and equals `N^{2E/3}` on the oblique tensor `f_C` — stated here with that
caveat. For `(B)` over every field without functionals: the flattening pigeonhole gives only `c_row ≥ 6λ − log₂T` for some piece.
(b) **Correction to the notes.** `engine3-open-door.md` §1.7 states "ρ < 1/2 on C ⟺ poly(λ) pieces, every one with
`c_1 + c_2 < Eλ − o(λ)`", §3.1 identifies Conjecture 8.1 with "ρ ≥ 1/2", and §3.2 calls Δ_3 "the smallest open instance for
ρ < 1/2" with "window [4/9, 1]". By Theorem 1 the sum criterion is never satisfiable with two merges (this is exactly §1.7's own
sentence "impossible for p = 2 (Prop. 4.8)" applied to the hyperedge case), and the window `[4/9, 1]` is a window on the **min-floor**
`M/(9λ)`, not on `V/(9λ)`. A gain in `M` does not propagate through a Theorem-A level built from independent copies of the
family (the half–half mixture of the two full pieces costs `≥ 9λ/2` per configuration); it is a gain only in the `Σ_t 2^{min cost}`
accounting of a single level, or for correlated decompositions of the tensor power `f_Δ^{⊗n}` treated as one configuration
(whether `M(f_Δ^{⊗n}) < n·M(f_Δ)` is a further open question). With **three** merges (rows, columns, diagonals) the pigeonhole gives
only `V ≥ Eλ/3`, and there `ρ < 1/2` is a genuine question; the flattening floor with three merges is also 4 of 9
(`engine3-delta3.md` Q3). (c) At fixed `N₀` with `T` types the same computation gives `V(τ) ≥ 9m₀/2 − (3/4)log₂T + (3/2)log₂T ≥
9m₀/2`: the criterion `V < 9m₀/2` of `engine3-delta3b.md` is unsatisfiable for every `N₀`, every `T`, every shape, without any
enumeration.

---------------------------------------------------------------------------------------------------

## 3. Reductions and the two-piece operator form [R]

### 3.1 Sums of networks

**Lemma 3.1.** If `R_t` are row networks with bonds `d^{(t)}`, `Σ_t R_t` is a row network with bonds `Σ_t d^{(t)}` (block-diagonal
bond indices: `W_r(i,j) = W_r^{(t)}(i,j)` when both indices lie in block `t`, zero otherwise; mixed blocks contribute nothing since
every product `W_0(i,j)W_1(i,k)W_2(j,k)` needs `i, j, k` in one block). Hence `c_row(Σ_t R_t) ≤ Σ_ρ log₂ Σ_t d_ρ^{(t)} ≤ 3log₂T +
Σ_ρ max_t log₂ d_ρ^{(t)}`. ∎

The last bound is `≤ 3log₂T + 3·max_t c_row(R_t)` in general and `≤ 3log₂T + max_t c_row(R_t)` when all `R_t` have the same bond
shape up to constants (`log₂d_ρ^{(t)} = x_ρ λ + O(1)`). **Consequence.** Grouping the row-cheap pieces of a family by bond shape on a
grid of resolution `λ/log λ` (`O(log³λ)` classes) and the column-cheap pieces likewise, any family with `M ≤ aλ` yields a family of
`O(log³λ)` pieces of pairwise distinct shapes with `M ≤ aλ + O(λ/log λ)`. The min-floor problem is therefore a problem about
`polylog(λ)` pieces of distinct shapes, and for a single shape class it is exactly the **two-piece problem**: does `f_Δ = R + C`
hold with `c_row(R) ≤ aλ`, `c_col(C) ≤ aλ`? This is the asymptotic form of the `N₀ = 2` "`T ≥ 4` types" question of
`engine3-delta3b.md` §2; the type-grouping charge `(3/2)log₂T` per block that kills the finite-`N₀` version is `o(λ)` here.

### 3.2 Near-fullness and the operator form

Let `f_Δ = R + C` with `c_row(R) ≤ aλ`, `c_col(C) ≤ aλ`, `a < 9`.

**Lemma 3.2 (near-fullness).** `F_col(R) ≥ N⁶ − 2^{2aλ/3}`, hence every column cut of `R` has rank `≥ N⁶(1 − 3·2^{2aλ/3 − 6λ})`;
symmetrically every row cut of `C` is full up to the same factor. *Proof.* `F_col(f_Δ) = N⁶ ≤ F_col(R) + F_col(C)` and
`F_col(C) ≤ 2^{2aλ/3}`; `F_col(R) ≤ Π_c rk_c(R)^{1/3}` with each factor `≤ N⁶`. ∎
So the row-cheap piece is column-full and vice versa: both pieces are "hubs" in the other merge, which is why no cut of the other
merge constrains them (this is Example 4.10's phenomenon with three groups).

**Lemma 3.3 (operator form).** Write `X_r := V_{r0}` (the two legs of node `(r,0)`), `Y_r := (r,1)^+ ⊗ (r,2)^−`, where `(r,c)^+`
is the leg of `(r,c)` toward row `r+1` (its partner is `(r+1,c−1)^−`). Let `J : X_0⊗X_1⊗X_2 → Y_0⊗Y_1⊗Y_2` be the leg permutation
`(r,0)^+ ↦ (r+1,2)^−`, `(r,0)^− ↦ (r−1,1)^+` (so `Y_r` receives one leg from `X_{r+1}` and one from `X_{r−1}`). Then `f_Δ = R + C`
with `c_row(R) ≤ aλ`, `c_col(C) ≤ aλ` implies
`N·J = Σ_{i,j,k} A_{ij} ⊗ B_{ik} ⊗ C_{jk} + L`, `A_{ij} ∈ Hom(X_0,Y_0)`, `B_{ik} ∈ Hom(X_1,Y_1)`, `C_{jk} ∈ Hom(X_2,Y_2)`,
`(i,j,k) ∈ [d_01]×[d_02]×[d_12]`, `d_01d_02d_12 ≤ 2^{aλ}`, `rank L ≤ 2^{aλ}`.
*Proof.* Flatten the identity across `(C_0 | C_1C_2)`: `rk(C; C_0|rest) ≤ e_01e_02 ≤ 2^{aλ}` (cut bound). The `Y`-side legs not in
`Y_0Y_1Y_2` are the six legs of the three edges between columns 1 and 2, `(r,1)^− ~ (r+1,2)^+`; contract them with the row-local
vector `⊗_r u_r`, `u_r = I` on `(r,1)^− ⊗ (r,2)^+`. This is a row-local restriction, so `R` stays a row network with the same bonds,
the rank bound on `C` persists, and `f_Δ` becomes `tr(I·I·I)·J = N·J` (the three identities form a closed 3-cycle through
`u_0, u_1, u_2`). ∎

Equivalently `J^{⊤}R′ = N·I_X + (rank ≤ 2^{aλ})`: **a row-structured operator is a low-rank perturbation of a leg-permutation
operator.** As a 3-party tensor on the rows (party `r` holding `X_r^*⊗Y_r`, dimension `N⁴`) `J` is `⟨N²,N²,N²⟩` (two legs cross
each row pair), a row network of cost `6λ`; `R′` has cost `≤ aλ`; `L` has operator rank `≤ 2^{aλ}` but unconstrained row cuts. Every
rank or functional argument on this form is again blocked by the straddling of `L` (operator rank versus row cuts); the form is
recorded because it is the smallest exact statement of the problem and because the same shape appears in the construction of §5
(`Π_σ − A⊗B⊗C` with `N³` in place of `N⁶`).

### 3.4 Partial fixings cannot beat the core floor [R]

**Lemma 3.4 (hub routing).** Fix any set of legs of Δ_3 to values; let `E′` be the edges with both legs free, `L_{rc}` the number of
free legs at `(r,c)`, and let `C′` be the restriction of a column network `C` with bonds `e`. For any choice of a hub row `h(c)` per
column, `C′` is a row network with bonds
`b_{rr′} = N^{Σ_{c: h(c)=r} L_{r′c} + Σ_{c: h(c)=r′} L_{rc}} · Π_{γ=(c,c′): {h(c),h(c′)}={r,r′}} e_γ`,
hence `c_row(C′) ≤ L_off(h)·λ + c_col(C)`, `L_off(h) :=` number of free legs at non-hub nodes.
*Proof.* Expand each `V′_c(bonds)` in a basis of the legs at the two non-hub nodes of column `c`: `V′_c = Σ_{α,β} X^c_{αβ}(bonds) ⊗
e_α ⊗ e_β`. Put `X^c` into row `h(c)` and `e_α, e_β` into their rows; the indices `α, β` and the column bonds between hubs in
different rows are the row bonds. ∎

Applying `F_row` to `f′ = R′ + C′` (`F_row(f′) = N^{2|E′|/3}`, `F_row(R′) ≤ 2^{2aλ/3}`, `F_row(C′) ≤ 2^{(2/3)(aλ + L_off λ)}`) gives
`a ≥ |E′| − L_off(h) − o(1)`. Each kept edge contributes `+1` and each of its free legs at a non-hub node `−1`; the hub set has one
node per column, so an edge contributes `+1` only if both ends are hubs, `0` if one is, `−1` if none. The hub set is a transversal of
the columns; the edges inside it are those of a triangle at most, so `max (|E′| − L_off) = 3` (hubs `= T_s`, all other legs fixed):
exactly the core floor. Non-uniform `θ` gives the same 3 (the bound on `C′` is then a weighted product of its row cuts and the optimisation over `θ` is the
one of §2.3's check (i)). With general node-local maps in place of fixings the hub-routing bound is still a product of flattening
ranks of a node-locally processed tensor, so it is subject to the §8.2 cap of 4 in any case. ∎

---------------------------------------------------------------------------------------------------

## 4. Theorem 2: diagonal pieces do not trade [R]; and the exact obstruction for general pieces

### 4.1 Diagonal pieces

Write a leg configuration as `(x, y)` with `x_e, y_e ∈ [N]` the two legs of edge `e`; `f_Δ(x,y) = [x = y]`. A piece is
**diagonal** if `A(x,y) = r(x)·[x = y]` for a function `r : [N]^9 → F` (`F` any field). This class contains every block
decomposition of `⟨N³,N³,N³⟩` along bond values (`r = 1_I(x_{01,·})1_J(x_{02,·})1_K(x_{12,·})`), every "restrict `f_Δ` to a set of
edge values" ansatz, all `Z_3×Z_3`-symmetric bond-value ansätze, and, since `f_Δ` is invariant under `GL(N)^9` acting edge-wise by
`(g_e, g_e^{−⊤})`, everything diagonal in a common edge-wise basis.

**Theorem 2.** If `Σ_{i≤T} r_i(x)[x = y] = f_Δ` (i.e. `Σ_i r_i ≡ 1`), then every piece satisfies
`c_row(A_i) ≥ log₂|supp r_i|` and `c_col(A_i) ≥ log₂|supp r_i|`, and some piece has `|supp r_i| ≥ N⁹/T`. Hence
`max_i min(c_row, c_col) ≥ 9λ − log₂T` and `max_i (c_row + c_col) ≥ 18λ − 2log₂T`: **no trade at all, `φ = 9` on this class, over
every field.**

*Proof.* Index `[N]^9` by the array `(θ_{ργ})`, `θ_ρ := (θ_{ργ})_γ ∈ [N]³`. The flattening of `A = r[x=y]` across `(V_0 | V_1V_2)`
has rows indexed by the row-0 legs, i.e. by `(θ_01, θ_02)`, and columns by all other legs, which include the `y`-legs of the same
edges, hence again the value `(θ_01,θ_02)`; the rows have pairwise disjoint column supports, so
`rk(A; V_0|rest) = |π_{01,02}(S)|`, `S := supp r`, and likewise `rk_1 = |π_{01,12}(S)|`, `rk_2 = |π_{02,12}(S)|`, where `π` projects
`S ⊆ [N³]³` onto two of the three coordinates `θ_01,θ_02,θ_12`. Loomis–Whitney: `|π_{01,02}(S)|·|π_{01,12}(S)|·|π_{02,12}(S)| ≥ |S|²`.
The cut bound `Π_r rk_r ≤ 2^{2c_row}` gives `c_row ≥ log₂|S|`. For columns use the transposed array (`θ_{·γ}`) and the same
argument. Since `Σ_i r_i = 1` pointwise, `∪_i supp r_i = [N]^9`. ∎

*Remarks.* (a) The bound is sharp for product supports (`r = 1_{I×J×K}`: `c_row = log|I||J||K|`). (b) It also shows that the
diagonal "product trick" `f_Δ·[x_{e*} ≠ 0] + f_Δ·[x_{e*} = 0]` (costs `(9λ + log(1−1/N), 9λ + log(1−1/N))` and `(8λ, 8λ)`) is
optimal among diagonal two-piece identities at every `N`: `M = 9λ + log₂(1 − 1/N)`; at `N₀ = 2` one support is `≥ 256`, so
`M ≥ 8`. (c) The same proof gives, for the `3×3` level (two edges per rectangle, array `[N]^{3×3}` with two values per cell), the
analogous `c_k ≥ log|supp|` and hence Conjecture 8.1 **on the class of diagonal decompositions** — a class that includes all
product decompositions and all block decompositions, but not the App. H / eight-square pieces, which are not diagonal.

### 4.2 Why ideas (1)–(5) stop at 4 for general pieces

The flattening world certifies exactly 4 on Δ_3 (`flatcert4.out`, exhaustive over `3⁹` orientations with the §8.2 LP; two or three
merges), and `engine2-decorrelated.md` §8.3 shows that `m`-party CVZ functionals, tensor rank, border rank, slice rank and geometric
rank applied after node-local processing give no more on the `3×3` level; the argument transfers to Δ_3 verbatim (a column functional
on a row-full piece meets straddling legs because the complement of a row is not a union of columns). Against this cap:

1. **Bond-triple functional.** A row network of bonds `d` lies in `U_0 ⊗ U_1 ⊗ U_2 ⊂ V_0⊗V_1⊗V_2` with `U_r = im W_r`,
   `dim U_r ≤ d_{rr′}d_{rr″}`, `Π_r dim U_r ≤ 2^{2c}`; its `(V_0 | V_1V_2)` image is spanned by the `d_01d_02` tensors
   `Σ_k W_1(e_i⊗e_k) ⊗ W_2(e_j⊗e_k)`, each of `(1|2)`-rank `≤ d_12`, while `f_Δ`'s image is `{x ⊗ I_{N³}}`. The dimension
   information is exactly what `F^{uniform}` uses (`F ≤ Π (dim U_r)^{1/3}`), and the rank-of-generators information is a flattening
   of a node-locally processed tensor (fix a functional on `V_0`). To go beyond, one needs an invariant of the **pair**
   (`U_0⊗U_1⊗U_2`, column structure); none that is subadditive and monotone is available: a column-cheap piece's row-side image is
   an arbitrary `N⁶`-dimensional subspace (Lemma 3.2), so any row-side invariant is unbounded on it. A dimension count (product
   subspaces of dimension `≈ 3N^{4+2a/3} + N^{2a}` against low-rank perturbations of dimension `≈ 2N^{6+a}` inside `N^{12}`) says a
   *generic* operator is not within rank `2^{aλ}` of a row-structured one for `a < 6`, consistent with `φ ≥ 6`, but `J` is a
   permutation, far from generic.
2. **Subvariety restrictions.** Node-local linear maps (fixings, pairings, projections) followed by any functional bounded by
   flattening ranks: capped at 4 (§8.2–8.3); followed by `F_row` with the column piece routed as a row network: capped at 3
   (Lemma 3.4). Non-node-local maps destroy one of the two network structures (a row-local map on `V_r` mixes the columns' legs;
   a map that is row- and column-local is node-local). Polynomial (tensor-power) restrictions produce mixed products of row and
   column networks, which are neither.
3. **Lemma 4.11 mechanism.** It needs a node isolated as a whole group of merge 1 and another isolated as a whole group of merge 2
   after restriction, with the functional `θ = (½,½,0)`; on Δ_3 a node is isolated in its row iff the other two nodes of the row are
   fully fixed, and the only node that can then be isolated in a column with free legs is the same node, giving the node cut
   `rk ≤ N²` and `N² ≤ d_01d_02 + e_01e_02`: nothing beyond `2λ`.
4. **Isotypic decomposition.** Under `G = GL(N)^9` edge-wise, `V = ⊕_{S⊆E} V_S` (`V_S = ⊗_{e∈S}(traceless) ⊗ ⊗_{e∉S} C·I_e`),
   `f_Δ` spans `V_∅`, and `f_Δ = R + C` gives `R = αf_Δ + Z`, `C = (1−α)f_Δ − Z` with `Z ∈ ⊕_{S≠∅}V_S`. The projections `π_S` are
   not merge-local: `tr_e` contracts a row-`r` leg with a row-`r′` leg and adds a factor `N` to the bond `ρ(e)` (so `π_S(R)` is a
   row network with bonds `d_ρ (N+1)^{|S∩ρ|}`), which loses `|S|λ` — too much. No inequality between `‖π_∅(R)‖` and the other
   components is available without a norm on the pieces, and the pieces can be scaled and cancel.
5. **Entropy / multi-partition rank.** `f_Δ` is a degree-2 graph tensor: on the 9 node parties `F^θ(f_Δ) = N^{Σ_v 2θ_v} = N²` for
   every `θ`, the maximum possible for any tensor on these parties; so every node-party functional is saturated by `f_Δ` and says
   nothing. Partition rank with respect to the row partition bounds row networks (`≤ 2^{2c/3}`-type) but not column networks,
   and conversely; the Rossman–Zhu multiquadratic SOS method applies to lower bounds against ranks of flattenings, i.e. to the
   same cut information.

**What a proof of `φ > 4` must do, exactly.** It must bound, for a tensor `R` that is a restriction of `⟨d⟩` on the row groups,
some quantity that (i) is monotone under row-local *and* column-local restrictions or at least under node-local ones, (ii) is
subadditive, (iii) is small on restrictions of `⟨d⟩` with `vol(d) ≤ 2^{4λ}` **and** small on column networks of cost `≤ 4λ`, and
(iv) is large on `f_Δ`. Any such quantity that factors through the flattening ranks of node-locally processed tensors fails by the
§8.2 computation, so (iii) must use that the three row cuts of `R` come from one bond triple together with the column structure,
e.g. that the `(V_0|rest)` image of `R` is spanned by `≤ d_01d_02` tensors of `(V_1|V_2)`-rank `≤ d_12` whose **column** structure is
unconstrained — the first place where row and column information meet in one object.

**What a counterexample to `φ ≥ 4 + ε` must look like, exactly.** By §3.1 it suffices to consider polylog(λ) pieces of distinct
shapes; for one shape class it is `f_Δ = R + C` with `vol(d), vol(e) ≤ 2^{(4+ε)λ}`; `R` must have all three column cuts of rank
`≥ N⁶(1 − 3N^{−10/3+2ε/3})` (Lemma 3.2) while its row cuts are `≤ N^{(8+2ε)/3}`-dimensional spans as in item 1, and `N·J − R′` must
have rank `≤ N^{4+ε}` (Lemma 3.3), where `R′ ∈ U_0⊗U_1⊗U_2 ⊂ End(X,Y)`, `dim U_r ≤ N^{(8+2ε)/3}`. Its pieces cannot all be diagonal in one
edge-wise basis (Theorem 2), and they cannot all be of the form `X_0^{(i)} ⊗ T_1 ⊗ T_2` (one triangle's factor varying): then
`Σ_i X_0^{(i)} = T_0` and the core floor gives a piece with `c(X_0^{(i)}) ≥ 3λ − o(λ)`, so `M ≥ 9λ − o(λ)` and
`Σ ≥ 18λ − o(λ)` on that class.

---------------------------------------------------------------------------------------------------

## 5. The straightened-edge family: a constant gain on the min-floor [R], and what ALS finds at `N₀ = 2` [N]

**Construction.** Fix a column pair `γ = {c, c′}`; its three edges `e_ρ` (`ρ = 01, 02, 12`) join `(r,c)` to `(r′,c′)` with `r ≠ r′`;
each row `r` has exactly one `γ`-leg at `(r,c)` and one at `(r,c′)`. Let `u_r` be any tensor on these two legs (an `N×N` matrix
`(r,c)`-leg → `(r,c′)`-leg) and set

  `R := (u_0 ⊗ u_1 ⊗ u_2) ⊗ ⊗_{e∉γ} I_e`,   `C := f_Δ − R = (I_{e_01}⊗I_{e_02}⊗I_{e_12} − u_0⊗u_1⊗u_2) ⊗ ⊗_{e∉γ} I_e`.

*Row cost of `R`:* the six non-`γ` edges contribute `N²` to each row bond and the `u_r` are row-local, so `c_row(R) ≤ 6λ`; the row
cuts are `N⁴`, so `c_row(R) = 6λ` exactly, for every choice of `u_r`. *Column cost of `C`:* the two other column pairs carry `N³`
each; the `γ`-bond carries the operator `X := Π_σ − u_0⊗u_1⊗u_2` from the three `(·,c)`-legs to the three `(·,c′)`-legs, where
`Π_σ` is the **cyclic shift** of the three `N`-dimensional factors (`I_{e_ρ}` sends the leg of `(r,c)` to the leg of `(r′,c′)`,
`r′ = σ(r)`), so `c_col(C) = 6λ + log₂ rank(Π_σ − u_0⊗u_1⊗u_2)` (the cut bound shows this is exact). With `u_r = I`:
`rank(Π_σ − I) = N³ − #{Z_3-orbits on [N]³} = N³ − (N³ + 2N)/3 = (2N³ − 2N)/3`. Hence

  `c_row(R) = 6λ`,   `c_col(C) = 9λ − log₂(3/2) + log₂(1 − N⁻²)`,   `c_col(R) = 9λ`,   `c_row(C) ∈ [9λ + 3log₂(1 − N⁻²), 9λ + 3log₂(1 + 1/N)]`
(row cuts of `C` have rank `≥ N⁶ − N⁴`; `C` is the sum of a bond-`(N,N,N)` and a bond-`(1,1,1)` row tensor times the `N²` identities),

so `M = 9λ − 0.585 + log₂(1 − N⁻²)` for every `N`: a constant gain over the raw `9λ`, against `log₂(1 − 1/N) → 0` for the diagonal
trick, and `R` is a row network of cost `6λ` whose complement is a column network below raw — the first exact identity on Δ_3 of this
kind. `R` is the graph tensor of Δ_3 with the three `γ`-edges replaced by horizontal edges `(r,c)–(r,c′)`; its row cost `6λ` is the
number of edges still crossing rows. The sums are `c_row + c_col = 15λ` for `R` and `≈ 18λ − 0.585` for `C`: no asymptotic trade
in the sense of (A), consistent with the rectangle-content conjecture.

**`min_{A,B,C} rank(Π_σ − A⊗B⊗C)` [N].** Alternating least squares with a rank-`m` slack (`cyc.py`): at `N = 2` the residual is
`0.94, 0.79, 0.62, 0.39, 0.0000` for `m = 0..4`; at `N = 3` it is `> 0.21` for `m ≤ 15` and `0.0000` at `m = 16`. So the minimum is
`(2N³ − 2N)/3` at `N = 2, 3` (attained by `I`), and the family above is optimal in its class at these `N`. A proof for all `N` would
be a statement about rank distance from a Kronecker product to the cyclic shift [C].

**ALS at `N₀ = 2` [N]** (`als_runs.py`, 8 restarts × 300 sweeps, then 6 × 1500; relative residuals; `d3lib.py` of
`engine3-delta3/`, validated there):

| two-piece shape (row bonds + column bonds) | costs | min residual | verdict |
|---|---|---|---|
| r488 + c488 | 8, 8 | 4·10⁻⁴ (decreasing) | exact: diagonal product trick |
| r444 + c488 | **6, 8** | **0.0000** (4 of 6 restarts) | exact; edge-cut ranks: three edges of column pair 01 have rank 4, six have rank 1 — **the straightened-edge family** (`analyze3.py`) |
| r448 + c488 | 7, 8 | 5·10⁻¹⁰ | exact; same family (bond 8 unused) |
| r448 + c448, r484 + c484, r448 + c484 | 7, 7 | 0.519–0.533 | none |
| r288 + c288 | 7, 7 | 0.637 | none |
| r288 + c488 | 7, 8 | 0.179 | none found |
| r288 + c882 | 7, 8 | 0.7071 | none |

The exact solutions found have 65 distinct values (64 nonzero values × 64 entries) and off-diagonal mass, which first looked like a
new non-diagonal identity; the edge-cut ranks identify it as `(u_0⊗u_1⊗u_2) ⊗ I^{⊗6}` with `rank(Π_σ − ⊗u_r) = 4`, i.e. the family
above (the ALS gauge rotates it). So at `N₀ = 2`: **two-piece identities with both costs `≤ 7` are not found; `M = 8` is the best
two-piece value, achieved by the diagonal trick and by the straightened-edge family.** This is evidence [N], not proof; the exact
`N₀ = 2` two-piece floor from flattenings is 5 (`engine3-delta3.md` §1), and the gap `[5, 8]` at `N₀ = 2` mirrors `[4, 9]`
asymptotically.

---------------------------------------------------------------------------------------------------

## 6. Status table

| statement | status | where |
|---|---|---|
| (B) `max_i(c_row + c_col) ≥ 9λ − 1.5log₂T`; `V ≥ 9λ/2` (ρ ≥ 1/2 in Theorem A's sense) for Δ_3 and every two-merge configuration, hyperedge pieces included | **proved [R]** (CVZ over `C`; Strassen support functional for other fields, flagged) | Theorem 1 |
| §1.7 sum criterion / `engine3-delta3b` game criterion unsatisfiable at every `N₀`, every `T` | **proved [R]** | Theorem 1(c) |
| Diagonal pieces (block decompositions, bond-value restrictions, common edge-wise basis): `c_row, c_col ≥ log|supp|`, no trade, `φ = 9` | **proved [R]**, every field | Theorem 2 |
| Conjecture 8.1 on the class of diagonal decompositions of the 3×3 level | proved [R] (same proof) | Rem. 4.1(c) |
| Partial fixings + hub routing + uniform functional give `≤ 3` | proved [R] | Lemma 3.4 |
| Sum of networks = network with summed bonds; min-floor problem = polylog(λ) pieces of distinct shapes; one shape = two-piece problem | proved [R] | §3.1 |
| Operator form `N·J = R′ + L`, `rank L ≤ 2^{aλ}` | proved [R] | Lemma 3.3 |
| Straightened-edge family: `c_row(R) = 6λ`, `c_col(C) = 9λ − log₂(3/2) + log₂(1 − N⁻²)`; `M ≤ 9λ − 0.585` for all `N` | proved [R] | §5 |
| `min rank(Π_σ − A⊗B⊗C) = (2N³−2N)/3` | [N] at `N = 2, 3`; upper bound [R] | §5 |
| `N₀ = 2`: no two-piece identity with both costs ≤ 7; the (6,8) identities are the straightened-edge family | [N] (ALS) | §5 |
| (A) no trade at all (`Σ ≥ 18λ − o(λ)`) for general pieces | **open [C]**; implies `φ ≥ 6` | §1, §4.2 |
| (C) `φ > 4` for general pieces | **open [C]**; exact obstruction and counterexample shape stated | §4.2 |
| `φ ≥ 4.5` (Conjecture 8.1 analogue), `φ ≥ 6`, `φ = 9` | open [C]; `4 ≤ φ ≤ 9 − 0.585/λ` | §1, §5 |

What this changes for the programme: the "α′ > 1 through Δ_3 with two merges" route of `engine3-open-door.md` §3.2(ii)/§6.1 is
closed by Theorem 1 (it was closed by Prop. 4.8 all along; the hyperedge cost does not reopen it). The live questions on Δ_3 are the
min-floor `φ` (for the `Σ_t 2^{min cost}` accounting and for correlated decompositions of tensor powers), the three-merge game value
(rows, columns, diagonals; pigeonhole floor `1/3`, flattening floor `4/9`), and the rectangle-content statement (A). The next
construction-side probes are the two-piece problem at `N₀ = 4` with the `Z_3×Z_3` ansatz (the straightened-edge family shows what a
cost-`6λ` row piece with a below-raw complement looks like; a family with `rank(Π_σ − K)` of lower order than `N³` for a
row-structured `K` of more than one term would be the first linear gain), and the three-merge game on Δ_3.
