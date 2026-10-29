# Crossover: where the ETH-refutation algorithms first beat brute force

*29 Oct 2026. Script: `research/scripts/crossover.py` (mpmath, 60 digits, log domain; K_ℓ = 2^{L_ℓ} is never
built as an integer). Output: `research/scripts/crossover.out`. Run with `python3 -I crossover.py`.*

## Summary (plain language)

**For each algorithm, the first n at which it provably beats brute force is about:**

| algorithm | as written (tier A) | parameters re-optimised (B) | + justified constants (C) |
|---|---|---|---|
| Anthropic #3-SAT, official Lean Theorem 1, m = 4.26n | **n ≈ 2^{552 040}** if the TM degree q = 1; 2^{2.2·10⁶} (q = 2), 2^{3.5·10⁷} (q = 10) | 2^{245 009} | 2^{119 103} (schedule); 2^{31 358} (+ FMM base case, heuristic) |
| Anthropic #3-SAT, any m (n-route) | 2^{3.4·10¹⁰} (q = 1) | 2^{1.6·10¹⁰} | 2^{3.9·10⁹}; 2^{1.0·10⁹} [H] |
| Anthropic 3-SAT decision machine (`inRateTM`) | 2^{2^{1747}} (exhaustive search below 2^{2^{1722}}) | — | — |
| OpenAI #3-SAT, Engine I (any m) | **n ≈ 2^{3.0·10¹³}** | 2^{8.5·10⁷} | 2^{3.8·10⁷} |
| OpenAI Engine II (the paper's sharper bound) | not before log₂n ≈ 2^{85} (2^{510} at full recursion depth); no upper bound (all constants O_C) | — | — |
| **#HC (ours)**, cubic graphs, vs n²2^n | **n ≈ 2^{55 440}** | 2^{44 356} | 2^{20 888}; 2^{4 905} [H] |
| #HC, Δ = 4 / Δ = 8 | 2^{112 860} / 2^{458 100} (2^{112 860} with the degree network) | 2^{90 291} / 2^{90 292} (degree network) | 2^{9 799} / 2^{19 350} [H] |

In words:

* **Anthropic.** The official Lean counting algorithm (CountedRoute, m-route) first beats 2^n on 3-CNFs with
  m = 4.26n clauses at about n = 2^{552 000}. That holds only if the machine's unknown polynomial degree q is 1. q is
  the one existential constant that matters, and each doubling of q multiplies the exponent by 4. On arbitrary
  formulas the n-route needs n ≈ 2^{3·10¹⁰}.
* **OpenAI.** As written, the algorithm needs n ≈ 2^{3·10¹³}. Re-optimising its own parameters brings that to
  2^{8.5·10⁷}. It has no unknown constant that matters.
* **#HC.** Our algorithm (conditional on Anthropic's Theorem A(b) and Lemma 8) beats Held–Karp on cubic graphs from
  n ≈ 2^{55 000}.

All other existential constants (C₀, C₁, C₂, polynomial degrees) are irrelevant at these sizes: they would have to
exceed 2^{5·10⁴} to move any n\*.

**The dominant term** is the same in every Anthropic-based case: the clique exponent e_ℓ·U. Here U is about 2km for SAT,
about 84n·log Δ for the n-route, and 4.65m for #HC. n\* is then a staircase: the first level ℓ with e_ℓ·U/n < 1, at the
smallest n allowed to use that level (K_ℓ⁹ ≤ m, K_ℓ¹⁷ ≤ n, K_ℓ³⁰ ≤ n). For OpenAI it is the Taylor (Hasse
derivative) term log₂C_q. The other two costs of the paper's eq. (three-costs) are below 10⁻³ at the crossover.

**The most effective lever** is different for each paper:
* *OpenAI*: replace the Hoeffding window R = (β+3)√λ by the least window that the exact binomial tail allows. This is
  tier B, and it shrinks log₂n\* by 3.5·10⁵×.
* *Anthropic*: pinning q matters most (×4 per doubling). Among constants, an FMM base case e₀ = 5/18 gives ×4, using
  e_ℓ instead of fractionHalf plus a free level gives ×2.25, and re-tuning ζ_ℓ, g_ℓ/K_ℓ gives ×2. From A to C2 the gain
  is ×17.6.
* *#HC*: the same schedule levers. The degree network helps from Δ ≥ 4 in U, and lowers n\* by 4× at Δ = 8.

## 0. What is computed

* T_alg(n) is the **proven upper bound** on the running time, with every explicit term and constant kept and the free
  parameters chosen as the tier says. The rate is log₂T_alg/n. Brute force is 2^n for #3-SAT and n²·2^n (Held–Karp)
  for #HC. The crossover n\* is the least n with T_alg < T_brute. We report t\* = log₂n\*, because n\* itself has
  between 10³ and 10¹⁴ binary digits.
* **Tier A**: as written (the Lean definitions, or the paper's parameter choices).
  **Tier B**: the same proven lemmas, with their free parameters re-optimised for each n.
  **Tier C**: constant changes that are justified but not in the proofs. Each is labelled *proven elsewhere* or *heuristic*.
* An existential constant (one that exists in Lean or hides in an O(·)) is never given a value. It is a parameter. Setting
  it to 0, or setting the polynomial degree q to 1, gives the **explicit-part lower bound** on n\*.
* Labels: **[P]** proven (Lean or paper, as cited), **[Par]** depends on a parameter we do not know, **[H]** heuristic.

## 1. Sources and formulas used (checked against the source; discrepancies with the plan marked ⚠)

Lean paths are under `/home/user/anth-build/proof/`. The OpenAI paper is
`…/scratchpad/oai-math-latest/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex`.
Only its `.tex` was read.

### 1.1 Anthropic

| item | source | formula used |
|---|---|---|
| schedule | `statements/LevelsStatement.lean` l.21–36 (`Levels.Gen`) | K₀ = 2^{x₀}, g_ℓ = 2^{3ℓ+x₀}K_ℓ, K_{ℓ+1} = g_ℓ², ζ_ℓ = 2^{−ℓ−5}, e₀ = ½, e_{ℓ+1} = (ρ+3ζ_ℓ)e_ℓ + 3/K_ℓ, ρ = 1/√2. The script asserts `PartA.logK` (log₂K_ℓ = 60·2^ℓ − 6ℓ − 42 at x₀ = 18) and `PartA.case_ii` for ℓ < 40. |
| x₀ | `maintheorem/CountedRoute/Defs.lean` l.118–124; `GeneralPieces.x₀Of` | x₀ = 18, the least value allowed (the other constraint, 2^{x₀} ≥ c + 7 or c + 5, binds only if c > 2¹⁸). |
| clique bound | `statements/CliqueLevelsStatement.lean` l.47 | 2^{e_ℓK²λ}(K(λ+B))^{C₀K²}; C₀ is existential (`ExplicitCost.RecursionSolves`, `rates/CountedRecursion/RecursionDefs.lean` l.553: ∀c ∃C₀). ⚠ In TM steps (`Solves`) the exponent e_ℓK²λ is claimed only up to a constant factor (docstring l.25–33). In counted operations (`SolvesInFactor`) it is exact. |
| grouping (Lemma 8) | `rates/ExplicitCost/GroupingDefs.lean` l.180; `statements/AppRunningTimeStatement.lean` l.101–109 | T ≤ (K^g + 𝒯·2^{2gP/K}·τ)(g(P+B))^{C₁}, L = ⌈(U+2ζgP)/K²⌉, B′ = ⌈2gP/K⌉ + g²B; case (i) g = 3K⁸, ζ = 1/(2K); case (ii) K∣g, c_ab ≤ P/g, K ln(2gK) ≤ 2ζ²g. C₁ is existential. |
| **official main theorem** | `Solution.lean` l.44: `MainResults.mainTheorem := CountedRoute.mainTheoremHolds` | ⚠ The plan used e_ℓ. The official route (`maintheorem/CountedRoute`) runs the solver `solverOfMachine` (`rates/CountedToPadded/Defs.lean` l.148), whose pad exponent is **needOf = ⌈e′K²λ⌉ + C₀K²·size(K(λ+B+1)) + 2**. Here e′ is `fractionHalf` (`rates/GeneralPieces/Num/Between.lean` l.34–37): 2^{−ℓ/2} for even ℓ and 1.4·2^{−(ℓ+1)/2} for odd ℓ. That is ≈ ρ^ℓ, about 1.55·e_ℓ. Tier A uses e′. The other Lean proofs (NamesInOrder / GeneralPieces, `Seq.rate`: need ≤ e_ℓK²λ + C₀K²log₂(K(λ+B))) and Theorem D(a) for *any* number in [e_ℓ, 2e_ℓ] justify e_ℓ in tier B. |
| m-route exponent | `rates/ClauseBound/Alg/Top.lean` l.33–80 | `root9` (largest K_ℓ ≤ m^{1/9}), g = 3K⁸, `PtopK` = max(1, 2k⌈m/g⌉), `lamTopK` = ⌊(K³ + 2kmK + gP)/K³⌋, **needTop = max(3K⁸·size K, P(2g/K+1), (K−1)λ, S.need(λ, P·2g/K))**, `planM`/`eM`: exhaustive search if needTop > n. Cross-check: `GeneralPieces/Num/TopDisplay.lean` l.463 `top_level`: needTop ≤ 2e_ℓkm + (2C₀+15)(km/K + K⁸log K + K²log(km)). |
| TM time | `variables/PairsToBound/Defs.lean` l.192 `Computes` | steps ≤ q·(\|x\| + 2^{expo} + 1)^q. **q is existential.** So T_TM ≈ 2^{q·expo}. The final forms `timeMin` etc. (`statements/MainTheoremFormsStatement.lean` l.85–103) fold q into one C. |
| n-route exponent | `variables/RecursionToBound/Defs.lean` l.140–200 | ⚠ The plan said "Δ ≤ (log n)^{4kC₀}". Lean instead uses the explicit `occBound` = 2(θ₀+θ₁+θ₂)+2 = 32α²+4α+6 with α = ⌈8ε⁻¹⌈log₂(128/ε)⌉⌉ (`sparsification/SparsificationLemma/Cal/Defs.lean` l.37–55). needAt = needNet(UbD, PbD, BbD) + size(nPrMax) + size(…), with UbD = 6k(n+LD Δ) + 28kn·clog₂(96Δ·LD Δ) + 2(3K⁸)² (`variables/VariableBound/Net/Defs.lean` l.324–398). needWalk = ⌈εn⌉ + 2 + size(stack), level `root17`, and ε = e′ (`epsOf`). There is also an existential threshold n₁ ≥ n₀ below which the route searches exhaustively. |
| 3-SAT decision machine | `rates/PaddedDescent/Params.lean` l.56–98, `Main.lean` l.47–63 | sOf n = ⌊3(⌊log₂⌊log₂n⌋⌋ − 911)/19⌋, exhaustive while s < 128, pad 2^{2^{131}(⌊n/2^s⌋+1)}. ⚠ The plan's floor "n < 2^{2^518}" comes from the docstring of `statements/ThreeSatRateStatement.lean` l.64. It is true but weak. The true floor is 2^{2^{1722}}, and the pad alone exceeds 2^n until 2^{2^{1747}}, as `Main.lean` says. |

### 1.2 OpenAI (paper only; the Lean development certifies no finite crossover)

| item | location | formula used |
|---|---|---|
| Engine I count | `prop:general-count` l.2013; `eq:pair-count`, `eq:hasse-order` l.1890 | 2Qr·C_q(2D+1)^{2τn}2^{2n/r} vectors, C_q = Σ_{s≤q}2^s C(n,s), **q = ⌊d_H/Q⌋** |
| degree | `lem:total-order`, `eq:origin-residue` l.2980–3040 | d_H = kR(m_test + 2(ℓ−1)), ℓ = n+1, m_test ≤ 6n (`lem:greedy-hashes`) ⇒ d_H = 24Rn for k = 3 |
| parameters | `lem:incidence-parameters` l.2747; proof of `thm:overview-sparse-polynomials` l.3095–3190 | λ = ⌈log₂n⌉, ν = ⌈log₂λ⌉, r = ⌊√λ/ν²⌋, Q = ⌊λ/(128ν)⌋, R = (β+3)⌈√λ⌉ with β the least integer with b, w ≤ λ^β; τ = 1/(rλ), D = r^{2Q}. Checks: r ≥ 2, Q > R, R ≥ 32, 6R ≤ Q, 2(b+w)D² ≤ M′, 2Qr² ≤ n′, tail. If any fails: exhaustive search. Branching on variables in > b₀ = ⌈M/n⌉⌈√λ⌉ scopes gives ≤ 2^{n/√λ} branches. |
| hash reduction | `lem:sparse-checks`, `lem:greedy-hashes` l.3220–3500 | μ = ⌊log₂m⌋+1, P_h = 20000B²μ², D₀ = 320000B²μ³, 3n(2m)^{P_h}+1 calls, Tanner search 2^{c_G d_G}; scope w ≤ kD₀ |
| sparsification | `lem:sparsify` l.3543, proof in `app:sparsify` l.3790–3850 | ⚠ The plan said "B = O_k((s log s)^{k−1}), hidden". The appendix makes it **explicit**: Γ = 2(3^{k−1}−1), M the least power of 2 ≥ Γ with Γ⌈log₂(4CM)⌉ ≤ σM, C = 4Σ_{j≤k−2}(3M)^j, B = 2Σ_{j<k}M^j, nodes ≤ (Cn+1)²2^{σn}, σ = 1/s, s = ⌊√λ/ν²⌋ (`prop:interpolation-bound` l.3570) |
| Engine II | `quantitative-reduction.tex` l.26; `quantitative-contraction.tex` l.80–110, l.558–619 | r = 64, ε = 1/131072, u_d = ⌊ελ/2^d⌋, H = ⌈s/⌊√λ⌋⌉, and (tensor-parameter-bounds) λ^{4/5} ≤ u_d at every active call. All rate constants are O_C(·). |

### 1.3 #HC (ours)

`research/exact-hc-theorem.md` §6 (6.1)–(6.2): gP ≤ 2.33(2m+n)+3g³, U ≤ 4.65m+g³, B ≤ 2(2m+n)/g+5,
log τ ≤ 1.5(2m+n)/g+3+C₂log n, L ≤ gP+1, B′ ≤ 2gP+1+g²B, branches ≤ n^{4m/Θ}, Θ = max(2, ⌈n/g⌉), level
K_ℓ³⁰ ≤ n, and the clique algorithm at e_ℓ (Theorem A(b) as printed). The degree network is
`research/hc-degree-theorem.md` Prop. 3.2 and §4.1: U ≤ 2n log₂(2e·d̄)+g³, gP ≤ 2(n+g)λ_Δ+3g³, Λ ≤ (2n/g+2)λ_Δ,
B ≤ Λ+2, log τ ≤ Λ+C₂log n, profiles ≤ (2ν+1)^{C(g,2)}, with no branching. Both are conditional on Anthropic's
Theorem A(b) and Lemma 8, and both count word-RAM operations, so there is no TM degree q.

## 2. Constants that are existential or hidden, and how each was handled

| constant | where | handling | effect on n\* |
|---|---|---|---|
| **q**, the TM polynomial degree (Anthropic) | `PairsToBound.Computes`: steps ≤ q(\|x\|+2^{expo}+1)^q. It is folded into the C of `timeMin`/`timeN` | [Par] q ∈ {1,2,3,5,10}. q = 1 gives the explicit-part lower bound. It is also the machine's own switch, since `planM` uses the clique route iff expo ≤ n. | **The only constant that matters.** The condition is q·2e′kα < 1, so each doubling of q costs about 2 levels, and t\* grows ~4× per doubling (t\* ∝ q²). |
| C₀ (clique polynomial factor) | `RecursionSolves` ∀c∃C₀; `StRate2`; `needOf` | [Par] C₀ ∈ {0,1,10}, plus break-even | none: it enters as C₀K²·size(·)/n. At tier-A n\* (α = 4.26) it moves n\* only if C₀ > 2^{429342}. |
| C₁ (Lemma 8 factor) | `GroupingExplicit` ∃C₁ | [Par] (HC: C₁ ∈ {0,10}, plus break-even). Not in the Lean pad exponent at all: `needTop` has no C₁. | none (enters as C₁log(g(P+B))/n) |
| C₂ (log τ) and the O(log n) of (6.2) | exact-hc-theorem.md (6.1)–(6.2) | [Par] ∈ {0,10}, plus break-even | none |
| c (pieces), Hardy–Ramanujan B, C | `ClauseBound.Inst.Half.Cst`, `PartitionStatement` | only through C₀ and through x₀ (2^{x₀} ≥ c+7). x₀ = 18 binds unless c > 2¹⁸ − 7. | none |
| n₀, n₁ (n-route "large n") | `ThmVariablesAForEveryMachine` ∃n₀ ∀n₁ ≥ n₀ | [Par] cannot be bounded. The computed n-route t\* is a lower bound, and the true crossover is max(n\*, n₁). | unknown, can only increase n\* |
| OpenAI polynomial factors (n+m)^{O_k(1)}, poly(D,Q,r,…) | throughout | [Par] degree c. Break-even reported. | none: a factor (n+m)^c moves n\* only if c > 2^{(λ\*−log λ\*)}. |
| OpenAI B = O_k((s log s)^{k−1}) | lem:sparsify | **explicit** in app:sparsify (§1.2), computed exactly | enters only through β (log b) |
| OpenAI "for sufficiently large n" (r ≥ 2, 6R ≤ Q, …) | lem:incidence-parameters | the checks are evaluated exactly. Below the first n where all pass, the algorithm searches exhaustively. | the checks first pass at λ ≈ 2^{37}–2^{38} |
| OpenAI Engine II constants O_C(·), O_{C,A}(·) | thm:tensor-contraction | not boundable. Only the explicit parameter threshold (§6) is reported. | lower bound only |
| OpenAI Lean ∃ C A d | `SubexpOrderedRawMainTheorem.lean` l.115 | not used: Lean gives no finite crossover | — |

## 3. Anthropic

### 3.1 The schedule (Lean, x₀ = 18)

| ℓ | log₂K_ℓ | e_ℓ | e′_ℓ (fractionHalf) | e_ℓ/ρ^ℓ |
|---|---|---|---|---|
| 0 | 18 | 0.5 | 1.0 | 0.5 |
| 2 | 186 | 0.302 | 0.5 | 0.604 |
| 4 | 894 | 0.159 | 0.25 | 0.634 |
| 6 | 3 762 | 0.0803 | 0.125 | 0.642 |
| 8 | 15 270 | 0.0403 | 0.0625 | 0.644 |
| 9 | 30 624 | 0.0285 | 0.0438 | 0.644 |
| 10 | 61 338 | 0.0201 | 0.0313 | 0.645 |
| 12 | 245 646 | 0.0101 | 0.0156 | 0.645 |

e_ℓ/ρ^ℓ tends to 0.6448 = ½·∏(1+3ζ_j/ρ). So the 3ζ_ℓ terms cost a factor of 1.29. The +3/K_ℓ terms are negligible:
they are < 2^{−17} at ℓ = 0 and doubly exponentially smaller after. (Lever 4: confirmed for 3/K, refuted for 3ζ.)

### 3.2 3-SAT decision machine (`Sat3.inRateTM`, PaddedDescent): tier A only [P]

The machine searches exhaustively for every n < 2^{2^{1722}}. The time is q·(pad)^q with pad = 2^{2^{131}(⌊n/2^s⌋+1)},
so it is below 2^n only once q·2^{131−s} < 1:

| q | needs s ≥ | n\* |
|---|---|---|
| 1 | 132 | 2^{2^{1747}} |
| 2 | 133 | 2^{2^{1754}} |
| 10 | 136 | 2^{2^{1773}} |
| 1000 | 142 | 2^{2^{1811}} |

This is a decision procedure (not #SAT). It is far worse than the counting routes below because of its padding
constant C0K 3 = 2^{131}.

### 3.3 #3-SAT, m-route (Theorem 1 in m; the official `MainResults.mainTheorem`), k = 3, m = αn

Rate table, tier A, α = 4.26, q = 1, C₀ = 0, at n = 2^{2^j}:

| j | log₂n | ℓ (root9) | rate = needTop/n | dominant |
|---|---|---|---|---|
| 8 | 256 | 0 | 25.6 | solver |
| 12 | 4 096 | 3 | 8.95 | solver |
| 16 | 65 536 | 6 | 3.20 | solver |
| 18 | 262 144 | 8 | 1.60 | solver |
| **20** | 1.05·10⁶ | 10 | **0.799** | solver |
| 24 | 1.68·10⁷ | 14 | 0.200 | solver |
| 30 | 1.07·10⁹ | 20 | 0.025 | solver |

The rate is 2e′_ℓ·k·α up to terms of relative size < 2^{−18000}. It halves every two levels.

**Crossover t\* = log₂n\*** [P for q = 1 and C₀ = 0 as a lower bound; Par in q]:

| tier | α = 1 | α = 3 | α = 4.26 | ℓ\* (α = 4.26) |
|---|---|---|---|---|
| A: CountedRoute, root9, e′ = fractionHalf, q = 1 | 33 858 | 275 614 | **552 040** | 10 |
| A, C₀ = 1 or 10 | same | same | same | |
| B: same lemmas, num = e_ℓ, level free, q = 1 | 7 163 | 122 176 | **245 009** | 9 |
| C1: ζ_ℓ = 2^{−(ℓ+z)} with the least g/K that case (ii) allows (not in Lean; paper's proof) | 6 459 | 59 247 | 119 103 | 8 |
| C2: C1 + FMM base case e₀ = 5/18 [H] | 1 449 | 15 405 | **31 358** | 6 |
| C3: C1 + e₀ = ω/9 = 0.2635 [H] | 1 353 | 14 412 | 29 341 | 6 |
| C4: C2 + x₀ = 10 [H; needs c ≤ 1017] | 1 161 | 13 036 | 26 621 | 6 |
| C5: C2 + no K^g grouping search [H] | 1 265 | 13 473 | 27 431 | 6 |

Sensitivity to the TM degree q (α = 4.26):

| q | A | B | C1 | C2 |
|---|---|---|---|---|
| 1 | 5.52·10⁵ | 2.45·10⁵ | 1.19·10⁵ | 3.14·10⁴ |
| 2 | 2.21·10⁶ | 9.82·10⁵ | 4.78·10⁵ | 1.27·10⁵ |
| 3 | 4.42·10⁶ | 1.97·10⁶ | 9.58·10⁵ | 2.72·10⁵ |
| 5 | 8.85·10⁶ | 3.93·10⁶ | 3.55·10⁶ | 9.58·10⁵ |
| 10 | 3.54·10⁷ | 1.57·10⁷ | 1.42·10⁷ | 3.83·10⁶ |

**Dominant term.** At every tier the cost at n\* is the solver term ⌈e′K²λ⌉ ≈ 2e′_ℓkm. At the tier-A n\*, the
grouping search, P(2g/K+1) and (K−1)λ are each < 2^{−18000}·n. So n\* is fixed by two discrete facts:
1. the first level ℓ with q·2e_ℓkα < 1; and
2. how large n must be before that level may be used:
   * in tier A by the rule K_ℓ⁹ ≤ m (t\* = 9 log₂K_ℓ − log₂α);
   * in tier B by the search term 3K⁸·size K ≤ n (t\* ≈ 8 log₂K_ℓ + 11).

Since log₂K_ℓ ≈ 60·2^ℓ, one level more doubles t\*.

### 3.4 #3-SAT, n-route (Theorem D(b): any number of clauses), k = 3

Here the rate is (needOutputs + needWalk)/n. The cost is set by the worst Δ = occBound ≈ 2048·⌈log₂(128/ε)⌉²/ε², which
is 2.8·10¹³ at ℓ = 25. The network total is U/n = 18 + 84·⌈log₂(96Δ·⌈log₂2Δ⌉)⌉ ≈ 4 800. Rate table (tier A, q = 1):

| j | log₂n | ℓ (root17) | rate | U/n |
|---|---|---|---|---|
| 22 | 4.2·10⁶ | 12 | 55.4 | 3 546 |
| 28 | 2.7·10⁸ | 18 | 8.08 | 4 134 |
| 34 | 1.7·10¹⁰ | 24 | 1.15 | 4 722 |
| 37 | 1.4·10¹¹ | 27 | 0.425 | 4 974 |
| 40 | 1.1·10¹² | 30 | 0.162 | 5 310 |

| tier | q = 1 | q = 2 | q = 5 | q = 10 |
|---|---|---|---|---|
| A: CountedRoute, ε = num = e′, root17 | **3.42·10¹⁰** (ℓ = 25) | 1.37·10¹¹ | 1.10·10¹² | 4.38·10¹² |
| B: num = ε ∈ [e_ℓ, 2e_ℓ] free (best: e_ℓ), level free | **1.61·10¹⁰** | 6.44·10¹⁰ | 5.15·10¹¹ | 2.06·10¹² |
| C1: re-tuned schedule, sparsification ε decoupled from e (best ε ≈ 128e) | 3.93·10⁹ | 1.68·10¹⁰ | 1.26·10¹¹ | 5.37·10¹¹ |
| C2: C1 + e₀ = 5/18 [H] | 1.05·10⁹ | 7.28·10⁹ | 3.36·10¹⁰ | 2.33·10¹¹ |

**Dominant term**: e′·U ≈ e′·84n·log₂(96Δ log 2Δ) (0.821 of the rate at tier-A n\*). The walk (2^{εn} leaves)
contributes 1.7·10⁻⁴. Every K-dependent term is below 2^{−6·10⁸}. Lean ties the sparsification ε to e (ε = num ∈ [e, 2e]).
Decoupling them (C1) is worth about two levels, because the walk term εn is cheap and the gain from 2 log₂(1/ε) inside U
is large. The existential n₁ of the n-route can only increase these numbers.

### 3.5 Lever ranking (Anthropic)

1. **The TM degree q** (existential). Doubling q costs ×4 in t\*. Pinning q is worth more than every constant
   improvement below, and nothing in Lean bounds it.
2. **The base case e₀** (FMM, e₀ = 5/18, [H]). It multiplies e_ℓ by 0.556, which saves ~1.7 levels and gives ×4–×8 in t\*
   (m-route: 119 103 → 31 358 at α = 4.26).
3. **Using e_ℓ instead of fractionHalf e′** (tier B; proven in the other Lean routes): e′/e_ℓ ≈ 1.55. Together with the
   level rule this gives ×2.25 (552 040 → 245 009).
4. **Re-tuning ζ_ℓ and g_ℓ/K_ℓ** (tier C1). ζ_ℓ = 2^{−(ℓ+6)} with the least g/K that case (ii) allows. It gives ×2
   (245 009 → 119 103). Lean's ζ_ℓ = 2^{−(ℓ+5)} is close to optimal in shape, but g = 2^{3ℓ+x₀}K is larger than case (ii) needs.
5. **Level rule**: K⁹ ≤ m (root9) → 3K⁸ log K ≤ n. This is part of the ×2.25 in item 3.
6. Smaller x₀ (= 10, [H]) gives ×1.15. Dropping the K^g grouping search [H] gives ×1.14. Both are minor: g = 3K⁸ ≤ m is needed anyway.
7. +3/K_ℓ: negligible. C₀, C₁, C₂: irrelevant (break-even C₀ > 2^{429342}).

## 4. #HC (ours; conditional on Anthropic Theorem A(b) and Lemma 8), vs Held–Karp n²2^n

Tier A: level rule K_ℓ³⁰ ≤ n, Lean schedule, e_ℓ (Theorem A(b) as printed); m = Δn/2.

| network | tier | Δ = 3 | Δ = 4 | Δ = 8 |
|---|---|---|---|---|
| exact-hc §6 (U ≈ 4.65m) | A (C₀=C₁=C₂ ∈ {0,10}) | **55 440** (ℓ = 5) | 112 860 (ℓ = 6) | 458 100 (ℓ = 8) |
| | B: level free | 44 356 | 90 291 | 366 482 |
| | C1: re-tuned ζ, g/K | 20 888 | 43 205 | 177 700 |
| | C2: + e₀ = 5/18 [H] | **4 905** | 10 470 | 46 182 |
| | C3: + e₀ = ω/9 [H] | 4 615 | 9 799 | 43 206 |
| | C4: + x₀ = 10 [H] | 4 330 | 8 695 | 39 079 |
| degree network (U ≈ 2n log₂(2eΔ)) | A | 55 440 | 112 860 | **112 860** (ℓ = 6) |
| | B | 44 357 | 90 291 | 90 292 |
| | C1 | 40 037 | 43 205 | 49 161 |
| | C2 [H] | 9 080 | 9 799 | 19 350 |
| | C4 [H] | 8 021 | 8 024 | 15 846 |

**Dominant term**: e_ℓ·U, which is 0.788 of n at the tier-A n\* for Δ = 3. Every other term is below 2^{−550}·n. The
branches (n^{4m/Θ}) and profiles ((2ν+1)^{C(g,2)}) are below 2^{−12000}·n. In tier B the binding lower-order term is
the g³ = 27K²⁴ copy-bit term in U and gP, so n\* ≈ K_ℓ²⁴ (t\* ≈ 24 log₂K_ℓ). Break-even constants at the tier-A n\*
(Δ = 3): C₀ > 2^{51726}, C₁ > 2^{55422}, C₂ > 2^{55421}. Within these ranges the constants do not move n\*.
The degree network has the smaller U from Δ ≥ 4 (8.88n against 9.30n at Δ = 4). It lowers n\* in tier A only at Δ = 8,
where it is 4× smaller, because the level is discrete. At Δ = 3 the old network is better (6.98n against 8.06n). With no TM degree q and no padding, #HC has the smallest crossover of all the algorithms here: about
n ≈ 2^{55 000} as written, and n ≈ 2^{4 900} with FMM base and re-tuned schedule.

## 5. OpenAI (#3-SAT, any m), Engine I: the interpolation route of `prop:interpolation-bound`

Rate = 1/s (sparsification leaves) + 1/t (branches on heavy variables) + log₂C_q/n (Taylor) + 2τ log₂(2D+1)
(measurements) + 2/r (one group) + polylog/n (Tanner search, 3n(2m)^{P_h} calls, 2Qr). Here n = 2^λ.
The polylog terms are below 2^{−10⁸} at the crossovers, so the paper's (n+m)^{O(1)} factors cannot matter.
C_q is bounded rigorously by (q+1)·2^{q+nH₂(q/n)} (3^n once q ≥ 2n/3).

### 5.1 Tier A (paper parameters) [P, with the worst-case b, w bounds]

| j | λ = log₂n | status | β | r | q/n | rate |
|---|---|---|---|---|---|---|
| 4–18 | 16 … 2.6·10⁵ | s < 2 → exhaustive search | | | | 1 |
| 20–30 | 10⁶ … 10⁹ | r < 2 or Q ≤ R → exhaustive | | | | 1 |
| 32–36 | 4·10⁹ … 7·10¹⁰ | 6R > Q → exhaustive | | | | 1 |
| 38 | 2.7·10¹¹ | all checks pass | 7 | 363 | 2.23 | 1.59 (C_q = 3^n) |
| 42 | 4.4·10¹² | | 6 | 1 188 | 0.554 | 1.55 |
| 44 | 1.8·10¹³ | | 6 | 2 166 | 0.290 | 1.16 |
| **46** | 7.0·10¹³ | | 6 | 3 964 | 0.152 | **0.766** |
| 50 | 1.1·10¹⁵ | | 6 | 13 421 | 0.041 | 0.289 |

All checks of the proof first pass at λ ≈ 8.07·10¹⁰ (log₂λ = 36.2), where the rate is 1.60. The rate first drops
below 1 at **λ\* = log₂n\* ≈ 3.02·10¹³ (log₂λ\* = 44.78)**. There β = 6, r = 2 712, Q = 5.24·10⁹ and R = 4.94·10⁷.
The terms at λ\* are Taylor 0.998, group 2/r 7.4·10⁻⁴, leaves 3.7·10⁻⁴, measurements 2.9·10⁻⁶ and branches 1.8·10⁻⁷.

**Dominant term: the Taylor/Hasse term log₂C_q.** It comes from q = ⌊24Rn/Q⌋ with R/Q = 128(β+3)ν⌈√λ⌉/λ. The
paper's R = (β+3)⌈√λ⌉ is set by a Hoeffding bound with deviation R/4 and the union over b ≤ λ^β incidences. At the tier-A λ\*, with the same r, Q and
τ, that R is 32× larger than an exact binomial window needs, so q/n stays above 0.2 until λ ≈ 3·10¹³. The other two "costs" of
eq. (three-costs) are negligible at the crossover: group 2/r and measurements together are < 10⁻³.

### 5.2 Tier B (same lemmas, lem:layout's numerical hypotheses only, parameters optimised) [P]

Free parameters: σ = 1/s, the branching threshold b₀ = ⌈M/n⌉·t, r, Q (at its maximum allowed by 2(b+w)r^{4Q} ≤ M),
R, and τ = r·b·Pr[W ∉ I] (the least allowed). The tail is bounded by Chernoff–KL, a rigorous upper bound on the exact
binomial tail. Search: floats, coordinate descent with restarts. Each reported point is re-evaluated with mpmath
through the same exact cost function as tier A.

| j | λ | rate | (s, t, r, R) |
|---|---|---|---|
| 24 | 1.7·10⁷ | 1.51 | (128, 512, 18, 17 150) |
| 26 | 6.7·10⁷ | 1.07 | (128, 512, 18, 34 948) |
| 28 | 2.7·10⁸ | 0.710 | (128, 512, 29, 66 152) |
| 32 | 4.3·10⁹ | 0.281 | (512, 2048, 86, 244 286) |
| 40 | 1.1·10¹² | 0.035 | (4096, 16384, 946, 3.46·10⁶) |

**λ\*_B ≈ 8.53·10⁷ (log₂λ\* = 26.35)**. The mpmath-verified rate there is 0.99983, with Taylor 0.888, group 2/r 0.100,
leaves 0.0078, branches 0.0020 and measurements 0.0018. The exact-tail lever shrinks t\* by a factor of **3.5·10⁵**.

### 5.3 Tier C: m_test ≤ n + ⌈n/log₂(4/3)⌉ + 1 ≈ 3.41n instead of 6n [P-derivable]

The bound comes from the proofs of `lem:sparse-checks` (when q_G > 1 there are < m/B ≤ n initial rows) and
`lem:greedy-hashes` ((3/4)^t2^n < 1 already for t = ⌊n/log₂(4/3)⌋+1 rounds). It lowers d_H from 24Rn to 16.2Rn. The paper does
not state it, but its proof gives it.
Result: **λ\*_C ≈ 3.82·10⁷ (log₂λ\* = 25.19)**, rate 0.99985 verified (Taylor 0.888, group 0.100).

Not used, because the proof does not give it: halving the group term via |S_{t,g}| ≤ n/r instead of 2n/r, and lowering
the precision ℓ = n+1.

## 6. OpenAI Engine II (`thm:tensor-contraction`, the sharper n log log n/√log n and m ≤ Dn bounds): lower bound only

All rate constants are O_C(·). What is explicit is the parameter regime, `quantitative-contraction.tex`
(tensor-parameters) and (tensor-parameter-bounds): ε = 2^{−17}, u_d = ⌊ελ/2^d⌋, and λ^{4/5} ≤ u_d at every active
call. Active calls reach depth d < (log₂C + ½log₂λ)/3. At that depth the bound needs ελ^{5/6}/C^{1/3} ≥ λ^{4/5},
i.e. **λ ≥ 2^{510}·C^{10}**. At depth 0 alone it needs λ ≥ 2^{85}. Below that, the stated estimates are not available
and the paper falls back to direct summation. [P-reading: this treats the claim of (tensor-parameter-bounds) as a
hypothesis the proof needs.] So Engine II as written gives nothing below log₂(wires) ≈ 2^{85}–2^{510}. That is far
beyond Engine I's n\*, so Engine I is OpenAI's operative crossover. The explicit leaf term H/n ≥ 1/√λ has no effect
there.

## 7. Explicit-part lower bounds (all existential constants at 0, q = 1)

Each of these is a rigorous lower bound on the crossover *of the proven bound*. For the padded Lean machines, which
write a pad of 2^{expo} units, it is also a lower bound on where the machine itself leaves exhaustive search
(`planM` / `plan` fall back when expo > n).

| algorithm | as written (A) | best proven re-parametrisation (B) |
|---|---|---|
| Anthropic 3-SAT decision (`inRateTM`) | n\* ≥ 2^{2^{1747}} | — |
| Anthropic #3-SAT, m-route, m = 4.26n | t\* ≥ 552 040 | t\* ≥ 245 009 |
| Anthropic #3-SAT, m-route, m = n | t\* ≥ 33 858 | t\* ≥ 7 163 |
| Anthropic #3-SAT, n-route (any m) | t\* ≥ 3.42·10¹⁰ | t\* ≥ 1.61·10¹⁰ |
| OpenAI #3-SAT, Engine I (any m) | t\* = 3.02·10¹³ (poly factors irrelevant) | t\* = 8.53·10⁷ |
| OpenAI Engine II | log₂(wires) ≥ 2^{85} (2^{510} at full depth) | — |
| #HC, Δ = 3 (vs n²2^n) | t\* = 55 440 | t\* = 44 356 |

For OpenAI Engine I and for #HC, the "lower bound" is the crossover itself: the remaining constants (polynomial
degrees, C₀, C₁, C₂) would have to exceed 2^{(t\*−log t\*)} or 2^{5·10⁴} to change it. For the Anthropic SAT routes
the true proven crossover is the q-dependent value in §3.3–3.4, and q is unknown.

## 8. Dominant term in each regime

| regime | dominant term at n\* | share of rate | what fixes n\* |
|---|---|---|---|
| Anthropic m-route | solver exponent e′K²λ ≈ 2e′_ℓkm | > 1 − 2^{−18000} | first level with 2q·e′_ℓkα < 1; then K⁹ ≤ m (A) or 3K⁸log K ≤ n (B) |
| Anthropic n-route | e′·U, U ≈ 84n·log₂(96Δ log 2Δ), Δ ≈ 2¹¹ε⁻²log²(1/ε) | 0.9998 (walk εn: 2·10⁻⁴) | first level with q·e′·U/n < 1; then K¹⁷ ≤ n |
| Anthropic decision | pad 2^{2^{131}(n/2^s+1)} | — | s = sOf n ≥ 132 + log₂q |
| OpenAI Engine I (A) | Taylor log₂C_q, q = 24Rn/Q | 0.998 | R/Q ≈ 128(β+3)ν/√λ small enough |
| OpenAI Engine I (B, C) | Taylor 0.89 + group 2/r 0.10 | 0.99 | balance of r (group) against Q_max ∝ λ/log r (Taylor) |
| #HC | e_ℓ·U, U = 4.65m (or 2n log₂(2eΔ)) | > 1 − 2^{−550} | first level with e_ℓU/n < 1; then K³⁰ ≤ n (A) or g³ = 27K²⁴ ≪ n (B) |

In the Anthropic regimes the rate is flat inside a level band and halves every two levels. Each level doubles
log₂K_ℓ. So n\* is a staircase in every constant: a constant change helps only once it crosses a level boundary,
and then it halves t\*.
