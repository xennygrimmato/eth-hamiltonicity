# How Anthropic's proof gets a bound in n alone (the 2^{C k² n log log n/√log n} term), and whether it transfers to the permanent

Workspace `/home/user/anth-build` (Lean v4.33.1); paths below are relative to `proof/` unless they start
with `/`. Paper text: `/tmp/claude-0/-home-user-lean-code/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/anth/fm/paper.txt`,
Appendix C at l.2017, Appendix D (Theorem D, Steps 1–6) at l.2060–2452. Our API notes:
`/home/user/eth-hamiltonicity/research/anthropic-api.md`.

**One-paragraph answer.** The m-independence is *not* produced by sparsification alone. Sparsification
(Appendix C/Step 5, Calabro's thresholds) only turns a k-CNF into a disjoint sum of 2^{εn} formulas in
which every variable occurs in at most Δ = (k/ε)^{O(k)} clauses; such a formula still has m ≈ Δn ≫ n
clauses, and the clause-cluster network of §6 (`satFk`, U < 6m) would cost 2^{e·Δn}, useless since
eΔ → ∞. The real device is the **variable-node network of Appendix D, Step 3**
(`variables/VariableBound/Net/Defs.lean`, `netD`/`netDN`): nodes hold blocks of *variables*; clauses are
never tested; the sum Σ_ξ Π_E [E satisfied] is rewritten by inclusion–exclusion as Σ_ξ Σ_{Π ⊆ V(ξ)}
(−1)^{|Π|} over sets Π of *violated* clauses ("marks"), cut off at |Π| ≤ n̄ ≈ n/log Δ, with the
assignments violating more than n̄ clauses killed by O(n) sparse parity checks (Steps 1–2, Lemmas 12–13).
A pair of nodes shares only *which of the clause-tests between them are marked*, encoded as the rank of
the mark string among strings with μ ones (`VariableBound.Net.rank`, `cw t μ = ⌈log C(t, μ)⌉`). With O(n)
marks of arity ≤ k among T ≤ km tests, Σ log C(t_{ab}, μ_{ab}) ≤ log C(T, μ) ≤ μ log(3T/μ) = O(kn log Δ)
bits in total. So **m enters only through log Δ**, and sparsification is what makes log Δ = O(k log(k/ε)).

## 1. The sparsification statement (Lean)

* Rule (IPZ/Calabro): `sparsification/SparsifyWidthK/Defs.lean`: `WidthK.Heart θ F j H` (H nonempty,
  |H| < j, H ⊆ at least θ(j−|H|) clauses of size j), `WidthK.Rule` (smallest such j, a largest H),
  `light F H = red (F ∪ {H})`, `heavy F j H = red (F ∪ petals F j H)`, `Leaf`. The counting version adds
  to the heavy child the side list 𝒩 = {¬ω : ω ∈ H} (README "heavy child"; `consequences/CountKSat/Defs.lean`),
  so no assignment satisfies two outputs. Combinatorics: no sunflower lemma; Calabro's accounting
  along a root–leaf path (`WidthK.AddK`, `InvK`, `Node`: at most β_i·n clauses of size i are ever added,
  each literal in ≤ d_i of them) plus the leaf count Σ_{j ≤ kn/τ} C(Ln, j) ≤ 2^{εn}
  (`SparsifyWidthK/Thresholds.lean`, `StepMachines/Math/SparsifyCount.lean: pow_mul_sum_choose_le_exp`).
* Thresholds used in the main theorem: `sparsification/SparsificationLemma/Cal/Defs.lean`:
  α = ⌈2(k−1)² ε⁻¹ ⌈log(32(k−1)²/ε)⌉⌉ (`alphaC`), β_1 = 2, β_c = Σ_h 4α β_{c−h} β_h = 2(8α)^{c−1}Cat_{c−1}
  (`betaC`, `StBetaCat`), θ_0 = 2, θ_c = α β_c (`thetaC`); outputs `Cal.sparsify k n ε φ : List PFml`
  (depth cut `depthC` = (β_1+…+β_{k−1})n).
* Exact form proved (`sparsification/SparsificationLemma/StepSparsify.lean`, for k ≥ 3, 0 < ε ≤ 1):
  `outputs_le`: number of outputs ≤ 2^{εn}; `exactly_one` (`ExactlyOne`: a satisfying assignment of φ
  satisfies exactly one output, a non-satisfying one none); `count_eq_sum`: #sat(φ) = Σ_outputs #sat.
  Occurrences: `RecursionToBound.ownDeltaIsBounded` (every output has `DeltaOf` ≤ `occBound k r` =
  2(θ_0+…+θ_{k−1})+2) and `occBoundIsThePrinted` (≤ 2(8k/ε)^{3k}+2). Cost: `RecursionToBound.walkCost`
  (exponent εn + c·k(log n + log(8k/ε))). Clause count of an output (`WidthK.leafC`·n) is proved but
  *not used* downstream: Theorem D reads only Δ.
* Statements at the top: `RecursionToBound.outputsAreFew`, `outputsAreWithinTheSetting`
  (`variables/RecursionToBound/Defs.lean` l.233–254): with ε ∈ [e, 2e], log Δ ≤ 3k log(8k/e) + 2 ≤ 4kC₀ log log n.

So the "disjunction" is a disjoint sum of ≤ 2^{εn} formulas on the same n variables, each with
Δ ≤ 2(8k/ε)^{3k}+2 occurrences per variable, produced in 2^{εn}·n^{O(k)}·(8k/ε)^{O(k)} time, with ε = e_ℓ ≈ 1/√log n.

## 2. Where k² and log log n come from

Exponent per output (Step 4, `RecursionToBound.oneOutputCost`): needAt ≤ A·e·k·n·log Δ. Chain:

1. Total bits of one profile's network, display (68): `VariableBound.Net.SizeU.stUPrinted`
   U ≤ 6k(n + log 2Δ) + 28kn log(96Δ log 2Δ) + 2g². **First factor k**: a mark (clause/incidence) touching
   t ≤ k nodes has t−1 tests (`tests_le`: T_0 ≤ (k−1)m, T_1 ≤ k·r·s̄), and the marks are bounded in
   number (kind 0: n̄+1 ≈ n/log Δ; kind 1: M ≤ 14n, `(61)`), so by `sum_lg_choose_le` + (59) the
   cost is O(kn log Δ). Lemma 8/Lemma 1 cost is 2^{e(U + gP/K) + 2gP/K}·poly, so the exponent is e·O(kn log Δ)
   (gP/K, eK², g log K, K² log n are all o(en) for K ≤ n^{1/17}, Δ ≤ n^{1/(40C₀)}).
2. **Second factor k and the log log n**: log Δ ≤ 3k log(8k/e) + 2 (`outputsAreWithinTheSetting`,
   from `occBoundIsThePrinted`), and the 2^{2en} outputs: total ≤ A·k²·e·n·log(k/e) =
   `expVariablesA k n e` (`RecursionToBound.exponentIsWithinTheBound`). With e = e_ℓ ≤ c/(log K_ℓ)^{α'}
   and K_ℓ > n^{1/(17C₀)}, log(k/e) ≤ (C₀ + ¼) log log n (k ≤ (log n)^{1/4}), giving
   2^{C' k² n log log n/(log n)^{α'}} (`ThmVariables.inParticular`, `timeVariablesAAlpha`).
   α' = ½ from Theorem B's pieces: `PairsToBound.thetaOfThePairs` (e_ℓ ≤ 0.85√(3x₀+6)/√log K_ℓ),
   `PairsToBound.mainRegimeBound`, `CountedRoute.thmVariablesBHolds` (Theorem D(b)),
   `MainResults.mainTheorem` with `expN k n = k² n lg lg n/√lg n`.
3. `one_le_loglog` (`rates/ClauseBound/TopN/Gen.lean` l.37, used in `UniformInK/Top/FallBack.lean`) is
   only the arithmetic fact log log(n+4) ≥ 1 that puts exhaustive 2^n counting (small n, or k > (log n)^{1/4})
   under the bound (rate `SatK.rN 1 α n = lglg(n+4)/lg(n+4)^α`). It is not where the log log comes from.

So: k² = (arity of a mark) × (log Δ ∝ k from Calabro's (8k/ε)^{3k}); log log n = log(1/e) with e ≈ 1/√log n.

## 3. Any other source of m-independence? (`proof/variables/`)

`variables/` *is* the variable-node construction and nothing else: `VariableBound/Net` (Step 3 network,
`netD`, profiles `admD`, `nPr = (I+m+1)^{2g²}` profiles), `VariableBound/Search` + `Family`, `Field` (Lemma 13,
GF(2^s) family of checks, Step 2 search by the potential Υ), `Params`, `Count`/`Top` (`countD` = Steps 1–4),
`SparsifyThenCount`, `RecursionToBound` (Step 5), `PairsToBound` (Step 6), `ThmVariables`. A twin
implementation lives in `rates/ClauseBound/ParityChecks` ("OL": checks become dummy variables n+j, sums
`truncW` over layered mark networks, `parOf` parameters) and feeds `UniformInK`/`SatM.TargetUniform`
(`statements/UniformInKStatement.lean`). Both are the same mechanism. There is no network in the code
where clauses are "checked implicitly" without marks: an *unmarked* clause is simply never looked at
(`okD` only verifies that every *marked* object has all its literals false at the node), which is exactly
why m does not appear. The only other network is the §6 clause-cluster one (`Count.wordNet`/`satFk`,
P = 6m̄, B = 1, U < 6m), which gives the m-bound.

## 5 (Q5, taken before Q4). What the engine charges for

`Printed.ComputesNetworks` (`statements/PrintedStatement.lean` l.149; Lemma 1, `Printed.groupingLemma`):
for every `N : Net g` with `N.Is P B` and query price τ,
T ≤ C₁·2^{e(U + gP/K) + 2gP/K}·(P+B)^{C₁}·τ, states ≤ C₁(P+B)^{C₁}, g = 3K⁸. Explicit form
`ExplicitCost.groupingExplicit` (Lemma 8): T ≤ (K^g + 𝒯·2^{2gP/K}·τ)·(g(P+B))^{C₁} with the clique label
length L = ⌈(U + 2ζgP)/K²⌉ and the clique solver's 𝒯 = 2^{eK²L}·(K(L+B'))^{C₀K²} (`CliqueLevels.bound`).
So the cost depends **exponentially on U = Σ_{a≠b} c_{a,b}, the total of shared label bits** (factor e), on
**P (max bits per node, and max Σ_b c_{ab})** only through gP/K = 3K⁷P (must be o(en)), on g only through
K^g and the polynomial, on B and τ polynomially/multiplicatively. It does not depend on |S_a| or on the
number of nodes as such. `Net.Is` (`networks/Eight/SecNetworks_Defs.lean` l.58) requires len_a ≤ P,
Σ_b c_{ab} ≤ P, |W|,|Ψ|,|f| < 2^B. Theorem D(a) (`ThmVariables.partA`, hypothesis (57)) is the only
statement with a bound in something other than clauses/variables, and it is stated for k-CNFs; the generic
objects are `ComputesNetworks`/`GroupingExplicit` in U, P, B, τ, g, K.

## 4 (Q4). Transfer to the permanent: verdict

Set-up: perm(A) = #perfect matchings of the bipartite graph G_A (rows R, columns C, |E| = nnz(A), max
degree Δ; dense means Δ ≈ n). Three natural networks on g = 3K⁸ nodes, each holding n/g rows and n/g columns:

**(a) Block/profile network (the one that works for sparse A).** Fix a profile μ_{ab} = number of rows of
R_a matched into C_b (a g×g contingency table; ≤ (n+1)^{g²} = 2^{o(n)} profiles, as in Step 3). z_a holds
π|_{R_a} (for i ∈ R_a a neighbour π(i) ∈ N(i), log Δ bits) and, for each b ≠ a, the set T_{ba} ⊆ C_a of a's
columns claimed by R_b (rank among μ_{ba}-subsets). W_a ∈ {0,1}: π|_{R_a} injective, and
{T_{ba}}_b ∪ (π(R_a) ∩ C_a) partition C_a. Ψ_{a,b} = [T_{ab} computed by a = T_{ab} stored by b] ∧ [sym.],
an equality test, so c_{ab} = cw(|C_b|, μ_{ab}) + cw(|C_a|, μ_{ba}) (Observation (b) after Definition 1, exactly
the `rank`/`cw` device of Step 3). Nonzero terms ↔ perfect matchings, value = #PM, B = 1. By
`sum_lg_choose_le`: U ≤ 2 Σ_b log C(g|C_b|, |C_b|) + 2g² ≤ 2n log(eg) + 2g²; using the edge-sparse
encoding instead (rank among μ_{ab}-subsets of E(R_a, C_b)) U ≤ 2 log C(|E|, n) + 2g² ≤ 2n log(eΔ) + 2g².
P = O((n/g) log(nΔ)), so gP/K = O(K⁷ n log n/g) = o(en). Lemma 1 then gives
**#PM(G) in 2^{O(n·log min(Δ, g)/√log n)}** (with `Printed.groupingLemma` + `Given.stOnGiven`, or
`groupingExplicit` + `CountedRoute.onTheCountedRecursion`, as in anthropic-api.md §4) — the genuine analogue
of Appendix D's "O(kn log Δ) bits": m-independent, no sparsification, no marks, no parity checks needed,
because the all-distinct constraint is *local to the column owner* once the sets T_{ab} are shared. This beats
2^n only for Δ = 2^{o(√log n)}. Remark for our HC theorem (§5–6 of exact-hc-theorem.md): the same
rank trick applied to the labels on E(a,b) (only n of the m edges carry a non-N label) replaces our
"bits per edge" w_{ab} = e_{ab} log 5 by log C(e_{ab}, μ_{ab}) + 2μ_{ab}, i.e. U = O(n log Δ) instead of O(m).

**(b) Dense A.** The block network has U ≥ Ω(n log g) for typical profiles (the block pattern of a random
bijection carries ≈ n log g bits that must cross node boundaries), and Lemma 1 needs g ≥ K with
e = e_K = Θ(1/√log K): exponent e·n·log g ≥ Ω(n √log K) ≫ n. Worse than Ryser's 2^n·poly. Case (ii) of
Lemma 8 (g = O(K log K)) does not help (log g ≈ log K). The obstruction is structural, not an accident of
the encoding: to make e·U = o(n) one needs e_K·log K → 0, i.e. α' > 1 in e_K = (log K)^{−α'}; Theorem B's
pieces (ρ = 1/√2, Hardy–Ramanujan) give α' = ½ and ρ < ½ is not available (Appendix H discusses the search
for cheaper pieces). So within Definition 2 + Lemma 1 the dense permanent cannot be brought below 2^n by
any encoding whose nonzero terms are the bijections, unless the rate α' improves past 1.

**(c) Why the Appendix-D mark trick does not transfer.** Write perm = Σ_{σ: rows→columns, σ(i)∈N(i)} Π_j [column j hit]
("clauses" = columns) or, dually (Ryser), Σ_S (−1)^{n−|S|} Π_i |N(i) ∩ S| ("clauses" = rows, variables =
columns). In both views the constraints have **width Δ (= n when dense) and each variable occurs in Δ
constraints**; Theorem D's exponent is k·e·n·log Δ and both k and Δ are n. Concretely, a marked column
("unhit") must be verified by *every* node owning a row adjacent to it: a mark has arity g instead of k, so
the O(n) marks of the cut-off and of the parity checks cost Θ(gn) bits (U ≈ 2(g−1)(n̄ log(n/n̄) + M log s̄)),
even worse than (b). Ryser's S must be known to all nodes: U ≥ 2(g−1)n, P = n (gP/K = 3K⁷n fails too).
**Sparsification-style branching has no analogue**: IPZ/Calabro branch on a literal set H ("heart")
contained in many clauses; in the column-clause view distinct clauses share no literals ([σ(i)=j] belongs
to clause j only), so `WidthK.Heart` never fires — the instance is already "sparse" (one occurrence per
literal) but of width n, and sparsification reduces occurrences, never width. Branching on a row's choice
costs d_i branches and lowers no other degree; reducing all degrees to Δ by restricting rows to Δ-subsets
costs Π_i C(d_i, Δ)/C(d_i−1, Δ−1) ≈ n^{Θ(Δn)} branches. From the CNF side the same obstruction appears
as: the all-distinct constraint on n log n bits needs Ω(n²) clauses of width ≥ 2 log n (or n² variables
x_{ij} with n wide clauses), outside the regime k ≤ (log n)^{1/4}, m = O(n) of the Main Theorem.

**Verdict.** The mechanism is CNF-specific: it rests on (i) constraints of bounded arity k and (ii) a
sparsification that makes occurrences n^{o(1)}, so that O(n) marks of arity k and O(log Δ) bits each encode
all cross-node information. The permanent of a dense 0/1 matrix has neither property, and every encoding
costs Ω(n log g) shared bits, which Lemma 1 turns into 2^{Ω(n √log K)}. **Most promising route (honest):**
the profile/block network (a) for bounded- or low-degree bipartite graphs, giving #PM in
2^{O(n log Δ/√log n)} (2^{o(n)} iff log Δ = o(√log n)), built directly on `Net g`/`Net.Is` with
`Printed.groupingLemma` or `groupingExplicit`; and the same rank trick to improve our HC network from
O(m) to O(n log Δ) bits. For dense matrices, nothing in this code or paper offers a path; it would need a
rate e_K = o(1/log K), which is a different theorem.
