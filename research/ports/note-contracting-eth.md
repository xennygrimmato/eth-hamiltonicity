# The contracting case of the tensor-price dichotomy contradicts the weak exponential-time hypothesis

*Version 2, 26 November 2026. Working title. Changes from the first draft are listed at the end.*

---

## 0. What is shown, and what is not

Anthropic's paper "VP ≠ VNP over every field" [AN] proves its permanent lower bound by a case split: over every
field k, the *flat* or the *contracting* hypothesis holds (AN Def. 2.1 = Def. D.1; Thm 2.2 = Thm D.2; Lean `thm_alt`).
We show that the contracting case has an algorithmic consequence, which the paper does not mention.
- **Characteristic 0.** If the contracting hypothesis holds over a field of characteristic 0, then 3-SAT on n
  variables can be decided deterministically in time 2^{O(n^{1−δ})}·poly for some δ > 0. We give this in two ways.
  - **Theorem R** (§3) uses only [AN] and classical facts. The form with poly(n)-size advice has been refereed. That
    the advice can be computed, so that the algorithm is uniform, rests on an audit of [AN]'s Lean proof terms by one
    reader (§3.6).
  - **Theorem A** (§4) passes through OpenAI's "ports" property [EG, HC] and OpenAI's IM Theorem 7.1.
- **Characteristic p** (§5, refereed). If the contracting hypothesis holds over a field of characteristic p, or if
  characteristic p admits ports, then 3-SAT has a randomised one-sided-error algorithm in 2^{O(n^{1−δ})}·poly, and a
  deterministic one with poly(n) advice. The probabilistic core is machine-checked in our Lean.

**Theorem B** (§6) reduces the hypothesis to finite metric objects. **Corollary 1** (§7): under the weak
exponential-time hypothesis (Weak ETH), the contracting hypothesis fails over every field of characteristic 0, so (by
`thm_alt`) the flat hypothesis holds there. **Corollary 1′** (§5.3) extends this to every field under randomised Weak
ETH. Neither uses OpenAI's theorem that flats exist (EG Thm 1.2); via Theorem R and C1-AN they use no OpenAI result.

**What we do not show.** We do not claim that the contracting hypothesis holds or fails; we prove no unconditional
algorithm or lower bound; we do not decide whether the two cases exclude each other ([AN] D.3: "We do not show that
the two cases exclude each other"). Every conclusion is an implication between hypotheses, with status in §8.

**Provenance of the sources.** Both source papers were produced by AI systems and have not been refereed by people.
- [AN, §3, p. 11]: "The proofs in this paper were found and written by AI. No human mathematician has checked the
  proofs."
- The README of OpenAI's release says it contains "manuscripts and supporting proof artifacts produced by an unnamed
  internal OpenAI model", "best understood as a form of raw research data".
- Both labs supply Lean developments. We read parts of both, but we built neither. (One file and nine definitions of
  [AN]'s Lean were copied verbatim into our own project and compiled there; §3.3.)

**Our own Lean.** Two projects, `research/ports/lean/` and `research/ports/lean-c1/` (Lean v4.36.0, Mathlib v4.36.0),
build with no `sorry`, no `axiom`, no `native_decide`, and only the standard axioms `propext`, `Classical.choice`,
`Quot.sound`. They are not linked to either lab's development: imported statements enter as explicit hypotheses,
transcribed by hand and checked by reading only.

**Status tags used below.**

| Tag | Meaning |
|---|---|
| [AN-L] | stated in [AN], with a Lean counterpart named by [AN] |
| [AN-p] | read off a *printed proof* in [AN], or off the structure of its Lean proof; not a stated theorem of either |
| [OA-L] | stated by OpenAI, with a Lean counterpart |
| [OA] | stated by OpenAI, without Lean |
| [cl] | classical |
| [ours-R] | our step, checked by an internal referee |
| [ours] | our step, not refereed |
| +L | in addition, the step (or the part named) is machine-checked in our Lean, conditional on the hypotheses stated |

The internal referee reports are `review-theoremR.md`, `review-theoremAB.md`, `review-uniformity.md`,
`review-c1.md` and `review-hull.md`.

---

## 1. Sources and conventions

- **[AN]** Anthropic, "VP ≠ VNP over every field", Nov. 2026, with Lean development
  (github.com/anthropics/formal-math, `vp-vnp`). Page numbers refer to its paper.pdf.
- **[EG]** OpenAI, "Euclidean geometry in the asymptotic spectrum of tensors", 24 Nov. 2026.
- **[HC]** OpenAI, "Circuit lower bounds for Hamiltonian cycle and the permanent", 24 Nov. 2026.
- **[IM]** OpenAI, "The logarithmic exponent of integer multiplication on tapes", 24 Nov. 2026.
- **[MM]** OpenAI, "The matrix multiplication exponent is nine fourths", 24 Nov. 2026 (used only in §7).
- **OpenAI Lean**: `OAI/Computability/MultitapeWeakETH/{Price,Cloud,MiddleDecision}.lean` in OpenAI's release.

**Hypotheses.** "Power-saving" means time 2^{O(v^{1−δ})}·poly(input length) for some fixed δ > 0, v the number of
variables of a 3-CNF.

| Name | Statement: there is no power-saving algorithm that … |
|---|---|
| Weak ETH (WETH) | … decides 3-SAT deterministically. This is [IM, §1, p. 1]; OpenAI's Lean `WeakETH` (`Price.lean`) asks for one `FiniteMultiTapeMachine`, so it is uniform |
| rWETH | … decides 3-SAT with randomness and one-sided error (never accepts an unsatisfiable formula; accepts a satisfiable one with probability ≥ 1/2) |
| UWETH | … deterministically solves the promise problem Unique-3-SAT |
| ⊕_pWETH | … deterministically computes #3-SAT mod p |
| nuWETH | … decides 3-SAT deterministically with poly(v) advice bits depending on v only |

Relations: ETH ⇒ WETH; rWETH ⇒ WETH; nuWETH ⇒ WETH; and rWETH ⇒ UWETH ⇒ ⊕_pWETH for every prime p (Corollary C5,
§5.2).

---

## 2. Definitions

### 2.1 Anthropic's spectral points, prices and the two hypotheses

[AN, Def. 2.1, pp. 4–5, `def_cases`; restated as Def. D.1, p. 30] Let V be a finite set of parties. A V-tensor over k
is an element of ⊗_{v∈V} k^{n_v}; products are taken party by party; s is a *restriction* of t if s = (⊗A_v)t.
- A *spectral point* φ on V maps V-tensors to [0, ∞), with φ(1) = 1, φ(st) = φ(s)φ(t), and "φ(s) ≤ Σ_j φ(t_j) whenever
  s = Σ_j s_j with every s_j a restriction of t_j".
- The wire ⟨q⟩_{uv} is the q × q identity in the indices of u and v; φ(⟨q⟩_{uv}) = q^{d_φ(u,v)} for a pseudometric d_φ
  (`lem_exponents`). A *price* is "a pointwise limit of functions c·d_φ with real numbers c ≥ 0" (`def_price`).
- For a price on Mat_μ(F₂), "D(r)² [is] the mean of |a, a+W|² over all a and all W of rank r". Here F₂ only labels the
  parties: "its F₂ is not the field k" (p. 5).

> **Flat hypothesis** (D.1): "All finite subsets of all Euclidean spaces, with their metrics, are prices."
> **Contracting hypothesis** (D.1): "There are an integer μ ≥ 2 and a real number s with 1 ≤ s and s² < μ such that
> D(μ) ≤ s D(1) for all prices on Mat_μ(F₂)."

Lean: `Paper/Alternative.lean`, `def Contracting`, `def Flat`. Every price has D(μ) ≤ √μ·D(1) (p. 5), so contracting
improves the trivial bound by a constant factor at one μ. Every point of Strassen's asymptotic spectrum (OpenAI's
spectral point, [EG §2.1]) is an [AN] spectral point, since s = Σs_j is a restriction of ⊕s_j [ours-R: review-AB §1].

**Theorem 2.2 / D.2** (`thm_alt`) [AN-L]: "Over every field k at least one of the two hypotheses of Definition 2.1
holds." The Lean proof (`Alternative.lean`, l. 921ff.) is a `by_cases` on `Contracting K` that calls
`thm_alt_euclidean hK` in the negative case: **¬Contracting K ⇒ Flat K**, as in the printed proof (p. 30).

**The rank metric.** ρ_μ(a, b) = √rk(a − b) on Mat_μ(F₂). Steps 2–7 of the proof of D.2 produce, when contracting
fails, a price with |a, a′|² = rk(a − a′) for μ ≥ 3 (Lean `thm_alt_rank_price`). Remark D.3: this price is not
Euclidean.

### 2.2 Anthropic's program model and cuts

[AN §I.1, pp. 48–49] Data are binary trees; programs use eleven constructs, and "every construct costs one step".
`guess` gives "two runs, with outputs nil and (nil, nil)"; `weight` multiplies the run's weight by a named generator of
a finitely generated ring A ⊂ k; `use` appends a name to a tally. "An instance z is τ-plain if all its runs halt and every accepting run has an empty tally
and costs at most τ. The sum sum(z) ∈ A of an instance is the sum of the weights of its accepting runs."

[AN Def. J.1, p. 52, verbatim]:
> "A program G cuts (τ, s) into (τ′, s′) with P pieces in t steps if the following holds for every instance z with
> |z| ≤ s. • All runs of G on z halt. The accepting ones take at most t steps, have empty tallies, and output lists of
> at most P instances of size at most s′. • If z is τ-plain, then all these instances are τ′-plain, and
> sum(z) = Σ_runs weight · Π_{y in the list} sum(y), where the sum is over the accepting runs of G on z."

Lean: `CutD` (`NS1/Compose.lean`, l. 25). It tracks steps and pieces, **not guesses**.

[AN Thm J.3, p. 53, `thm_onecut`] [AN-L]: "There are constants a₀, C, v₀ such that the following holds with
Λ = (lg v)^C, for all v ≥ v₀, all τ ≥ v^{a₀} with 4 lg τ ≤ (lg v)², all s ≤ τ and all 2 ≤ k ≤ v^64. Some program of
size at most v^{a₀} cuts (τ, s) into (τΛ/k, (s/k + τ/v^256)Λ) with at most kΛ pieces, in (s + τk/v^256)Λ steps."

[AN Thm J.4, pp. 54–55, `thm_cut`] [AN-L]: "There are a multiple H ≥ 272 of 16 and constants C_cut, v₀ such that the
following holds whenever v ≥ v₀ and α satisfy (lg v)^{C_cut α} ≤ v. For all τ and s with v^H ≤ τ ≤ v^{Hα} and
s v^48 ≤ τ, some program of size at most v^H cuts (τ, s) into (v^H, v^{H−32}) with at most τv²/v^H pieces in at most
τ/v^24 steps."
§§F–K assume the contracting case throughout (p. 37); J.4 involves no permanent. Lean `exists_setting`
(`Paper/Cuts.lean`, l. 570) supplies, for any `Field K` with `Contracting K`, a subring A with `Algebra.FiniteType ℤ A`,
generators θ and the hypotheses of `thm_cut`. In the Lean, H = 16(a₀ + 217); H is not explicit.

### 2.3 OpenAI's ports

[EG Def. 11.1, verbatim]:
> "A field has ports if it admits a family of regular, symmetric multigraphs of unbounded order and bounded degree, and
> a constant γ such that V(x) ≤ γE_G(x) for every graph in the family and every assignment into a spectral space over
> the field."

Here E_G(x) = |V|^{−1} Σ G_ij d(x_i, x_j)², V(x) = |V|^{−2} Σ d(x_i, x_j)². "This property depends only on the
characteristic." [HC §2.2]: X_χ is the class of Hadamard spaces with spectral prices over fields of characteristic χ,
and "The condition for X_χ is precisely port admission by χ".

[HC Thm 4.2, verbatim] [OA-L]:
> "Let P be the walk on a d-regular multigraph with n ≥ 2 vertices, d ≥ 1, and uniform stationary law π. Suppose that
> V_π(x) ≤ βE_P(x) for every placement x in every member of a class of Hadamard spaces without ports. Then
> β ≥ c log n/log(d+1) for an absolute constant c > 0."

Lean counterpart, characteristic 0 only: `exists_logarithmic_placement` (`Cloud.lean`, l. 83), for order 2^s and degree
2^e, threshold s/(10000(e+3)), with hypotheses `large` and `scalar` (§4).

[IM Thm 7.1, verbatim] [OA-L]:
> "If characteristic zero admits ports, then for some δ > 0 a deterministic algorithm decides 3-SAT on v variables in
> 2^{O(v^{1−δ})} bit operations times a polynomial in the input length. In particular, under variable-count Weak ETH,
> characteristic zero does not admit ports."

Its proof rests on [HC Thm 13.1] (enumerable contraction under ports; quoted in §5.1). Lean: `middle_count_bridge :
PortZero → PowerSavingDecision …` (`MiddleDecision.lean`), with `PortZero` over `AlgebraicClosure ℚ`.

---

## 3. Theorem R: the route through Anthropic's paper alone

### 3.1 Statement

> **Theorem R.** Suppose the contracting hypothesis holds over a field k of characteristic 0. Let H be the constant of
> [AN] Thm J.4, and fix any δ < 187/(5H + 187).
>
> (a) **Counting a single plain instance.** There is a deterministic procedure that, for every τ-plain instance z of
> [AN]'s program model with |z| ≤ τ, computes sum(z) with 2^{O(τ^{H/(H+187)})}·poly(τ) operations in A. In characteristic
> 0 this means poly(τ)-bit arithmetic, after a fixed embedding into a number field (§3.5).
>
> (b) **3-SAT.** There is a deterministic algorithm that decides 3-SAT on n variables in 2^{O(n^{1−δ})}·poly(input
> length) bit operations.
>
> In both parts the algorithm is one fixed machine together with a finite table of constants. The table does not depend
> on n, and it is known to exist but is not explicit (§3.6).

**Status.** The *non-uniform form*, with the cutting program G_v of J.4 (size ≤ v^H = poly(n)) as advice, is refereed
(review-theoremR). Computing G_v from v, which gives the uniform statement, rests on the uniformity audit (§3.6): one
reader of [AN]'s Lean proof terms, with a meta-level central step. Lemma 1 is refereed as a reading of prose and Lean,
and only partly machine-checked (§3.3). The parameter arithmetic, the composition sum of Lemma 1 and the pruned
evaluation of Lemma 2 are machine-checked (`ThmR.lean`, `PrunedTree.lean`), with J.4 and the per-cut guess counts as
hypotheses.

> **Remark R′ (non-uniform form, refereed fallback).** Without the audit, (a) and (b) hold for an algorithm that also
> receives the advice string G_v of length poly(n), respectively poly(τ). This refutes nuWETH.

For H = 272 the bound on δ would be about 0.121, but H is not explicit. (a) concerns one τ-plain program in [AN]'s
model and needs no sparsification; a translation to multitape Turing machines with linear overhead looks routine but
is [ours], not written out. For counting 3-SAT solutions see §9, item 4.

### 3.2 Why the stated J.4 is not enough [ours-R]

J.4 bounds the lister only by τ/v^24 *steps*, and requires s·v^48 ≤ τ. An accepting run may therefore contain up to
τ/v^24 ≥ s·v^24 guesses, and enumerating the runs costs 2^{≥ s·v^24}; for 3-SAT, s ≥ n, so this is worse than brute
force. What is missing is a bound on the number of `guess` constructs.

### 3.3 The guess-count lemma

> **Lemma 1 (guess count)** [AN-p; ours-R; composition step +L]. In the setting of J.4 with α = 2, every accepting run
> of the composed lister G on an instance z with |z| ≤ s executes at most τ/v^235 `guess` constructs, for all v ≥ v₀
> (enlarging v₀ if needed).

**Where it is read from, in the paper.** The proof of J.3 (pp. 53–54), paragraph "The program G": "It guesses q, ρ,
the numbers of packets and the outcomes … It then guesses the contents of the cut packets … **All of this is
deterministic except for the guesses**, and every choice in the formula is guessed exactly once"; and the step account
"sΛ steps for the word, (MN)^{C_tree}Λ ≤ τΛ/v^256 steps for the plan, and kΛ · τΛ/v^300 steps for the cut packets"
(exponents from Table 2, p. 52).

**Where it is read from, in [AN]'s Lean** [ours-R, review-theoremR §1; read, not built]. The one-cut program is
`dealProg` (`Nc/Dl/Cut.lean`, l. 55). Its only reachable `guess` sites are `pickB` (`NS1/Lists.lean`, l. 316; the plan
choices) and `bitsB` (`NS1/Deal.lean`, l. 73; the cut-packet contents). The s-dependent phases `wordB` and `partStep`
contain no guess and account for exactly the s-dependent terms of the cost bound `dealB` (`Nc/Dl/Does.lean`, l. 31).
`compC` adds no guesses; the runs of G have weight 1; the other `guess` sites are summed inside the pieces.

**What is machine-checked** (`PortsLean/ANFragment/`). `Machine.lean` is [AN]'s `NS1/Machine.lean` verbatim, and
`Defs.lean` nine of [AN]'s definitions verbatim (including `pickB`, `stepC`, `compC`); they typecheck unchanged on
Mathlib v4.36. The overlay `Guess.lean` defines `EvG`, which mirrors `Ev` with a guess count on every accepting run
(`EvG.toEv`: these are exactly the accepting runs), and proves per-construct bounds, `pickB_guesses` (picking from n
options costs ≤ n guesses) and **`compC_guesses`**: if every accepting run of G makes ≤ g guesses and the pieces y of
each output have Σ_y g′(y) ≤ B under G′, then `compC G G′` makes ≤ g + B. **Not done:** `bitsB`; the bound for
`dealProg`; threading through `thm_onecut_program` → `thm_cut_compose` → `thm_cut`. These need [AN]'s Lean built,
which we have not done, so the per-cut counts remain a reading. **Findings.** (i) Guess bounds cannot be read off
[AN]'s `Does`/`Gives`: `ite guess id fail` gives one weight-1 output but makes one guess, and lists with cancelling
weights satisfy the same `Does`; bounds must be derived from program syntax. (ii) `Ev`, `Does` and `CutD` quantify over
*accepting* runs only (`NS1/Comp.lean` l. 69), matching the pruned evaluator of Lemma 2.

*Proof of Lemma 1.* Each `guess` costs one step and the word phase is guess-free, so one cut at level i (time bound
τ_i, k_i ≤ v^64) makes ≤ τ_iΛ/v^256 plan guesses (the J.3 proof: all tables "are smaller than v^{a₀} and than
τ/v^256") plus ≤ k_iΛ · KTΛ/v^300 cut-packet bits (Prop. J.2; KT ≤ τ_iΛ + K, K ≤ τ_i), so g_i ≤ 2τ_iΛ³/v^236. (The
working notes had Λ²; the referee's count gives Λ³; the difference is absorbed, Λ being a power of lg v, p. 51.)
Composition (J.4 proof, p. 55): r = O(α) cuts; cut i+1 runs on each of the P_i pieces of time bound τ_i, and
"P_iτ_i ≤ τ(4Λ²)^i". Guesses add along a run (`compC_guesses`), so

    total ≤ Σ_{i<r} P_i·g_i ≤ 2rΛ³(4Λ²)^r · τ/v^236 ≤ τ/v^235,

using 2r(4Λ³)^rΛ³ ≤ v, an instance of the J.4 proof's "All these powers of Λ are below v if C_cut is large" (Lean
`thm_cut`, via `polylog_loss_le`). ∎

The last two inequalities are `lemma1_per_cut` and `lemma1_composed` in `ThmR.lean` (+L). They are stated with Λ²; the
Λ³ form is the instance Λ ↦ Λ^{3/2}, since the hypothesis P_iτ_i ≤ τ(4Λ²)^i only weakens.

**Robustness of the exponent.** Only "total guesses ≤ τ/v^{48+g} with g > 0" matters (§3.5). 256 and 300 are in the
paper; 235 and 236 are our inference. Using only the *statement* of J.3, and granting that its s-term is guess-free,
the per-cut guesses are ≤ τkΛ/v^256, giving g = 143 and δ < 143/(5H+143).

### 3.4 From the guess count to deterministic time

> **Lemma 2** [ours-R, given Lemma 1 and J.4; +L for the pruning]. Assume contracting over k. Let v ≥ v₀,
> v^H ≤ τ′ ≤ v^{2H}, and let z be τ′-plain with |z|·v^48 ≤ τ′. Given G = G_v of J.4 (with α = 2), sum(z) can be computed
> deterministically with 2^{O(τ′/v^235 + v^H)}·poly(τ′) operations in A.

*Proof.*
1. **Enumerate the run tree of G on z, pruned.** Explore depth-first; cut off any branch once it exceeds t = τ′/v^24
   steps or g = τ′/v^235 guesses. Every prefix of an accepting run survives (J.4 and Lemma 1); no bound on
   non-accepting runs is needed (the referee's fix). `guess` is the only branching and is binary (p. 48), so the
   pruned tree has ≤ 2^{g+1} leaves and the enumeration takes 2^{g+1}·poly(τ′).
2. **Collect the accepting runs.** Each gives a weight w ∈ A (here w = 1) and a list of ≤ τ′v²/v^H pieces y.
3. **Evaluate the pieces.** Each is v^H-plain: enumerate its run tree cut off at v^H steps (≤ 2^{v^H} leaves) and sum
   the weights of accepting runs. The cut-off is exact.
4. **Output** Σ_runs w·Π_y sum(y) = sum(z) by Def. J.1 (Lean: `pv θ z = wsum Q (pvs θ)` in `CutD`). ∎

`PrunedTree.lean` proves, for abstract run trees with binary guess nodes and ring weights, that pruning at g guesses
and t steps leaves ≤ 2^g leaves (`leaves_prune_le`, no hypothesis) and preserves the sum whenever every *accepting*
leaf has ≤ g guesses and cost ≤ t (`sum_prune_eq`). The link to [AN]'s `Ev` is by reading.

> **Theorem R(a)** [ours-R; +L for the arithmetic]. For τ-plain z with |z| ≤ τ, put v := ⌈τ^{1/(H+187)}⌉ and
> τ′ := v^{H+235}, and apply Lemma 2.

*Check* (`ThmR.lean`: `v_choice`, `j4_constraints`, `lemma2_cost_le`, `theorem1_exponent`, `polylog_condition`).
τ ≤ v^{H+187} and v ≤ 2τ^{1/(H+187)}, so z is τ′-plain and |z|·v^48 ≤ τ′. v^H ≤ τ′ ≤ v^{2H} needs only **H ≥ 235** (J.4
gives 272). Every J.4 constraint holds exactly, with no rounding: τ′/v^235 = v^H, τ′/v^24 = v^{H+211}, pieces = v^237.
J.4's side condition (lg v)^{2C_cut} ≤ v holds for large v, so **v₀ must be enlarged depending on C_cut**. The cost is
≤ 2^{(2H+241)v^H}, with exponent ≤ (2H+241)·2^H·τ^{H/(H+187)}; the piece evaluation is of the same order as the run
enumeration. Small τ: brute force. ∎

### 3.5 3-SAT, and where characteristic 0 is used [ours-R]

**Sparsification** [cl: Impagliazzo–Paturi–Zane], in the sunflower version written out in the proof of [IM] Thm 7.1
(counting re-checked by the referee). Fix 0 < α < 1/4 and r = ⌈n^α⌉. In 2^{O(n^{1−α} log n)}·poly time, F becomes a list
of at most 2^{O(n^{1−α} log n)} 3-CNFs F_j, each with O(n^{1+4α}) clauses, with F satisfiable iff some F_j is. The
branching is **not** disjoint, so for decision each leaf is tested separately (a disjoint variant: §5.3).

**One leaf.** z_j = (P, ⟨F_j⟩) for a fixed program P. P builds by a loop a balanced binary tree of depth ⌈log₂ n⌉ whose
leaves are guessed bits; for each literal it walks down to its variable's bit in O(log n) steps; it fails on an
unsatisfied clause, and otherwise accepts with weight 1 and an empty tally. z_j is τ₀-plain with τ₀ = O(n + m_j log n),
|z_j| = O(m_j log n); put L = O(n^{1+4α} log n) ≥ both.
- sum(z_j) = 2^e·#SAT(F_j)·1_A with e = 2^{⌈log n⌉} − n padding leaves. In characteristic 0 the factor is harmless.
- **Padding fix.** P fails unless each padding leaf is 0 (O(n) deterministic steps). Then accepting runs correspond
  bijectively to satisfying assignments, e = 0, and sum(z_j) = #SAT(F_j)·1_A in every characteristic. Refereed
  (review-c1 §5); it is needed at p = 2 (§5.3).

**Characteristic 0.** By `exists_setting`, A ⊂ k is a finitely generated ℤ-algebra, and A ⊗ ℚ ≠ 0. A maximal ideal of
A ⊗ ℚ gives a ring map ψ: A → L into a number field (Zariski's lemma; [AN] K.6 uses the same device). ψ(1) = 1, so
ψ(sum(z_j)) = 2^e·#SAT(F_j) ∈ ℤ, positive iff F_j is satisfiable. All identities used hold in A and survive ψ. The
fixed table holds the images ψ(θ) of the named generators. Run weights are products of poly(τ) fixed algebraic numbers
and sums have 2^{O(τ)} terms, so every number has poly(n) bits.

**Exponent.** The total is 2^{O(n^{1−α} log n + n^{(1+4α)ρ} polylog n)}·poly with ρ = H/(H+187). Balancing
α = 1 − (1+4α)ρ gives α = (1−ρ)/(1+4ρ) = 187/(5H+187). This is < 1/4 exactly when **H > 112.2**, which J.4's H ≥ 272
satisfies (`alpha_star`, `choose_alpha`, `sat_exponent`; +L). Hence any δ < 187/(5H+187) works. ∎ (Theorem R(b))

In general, if the total guesses are τ/v^{48+g}, one gets δ < g/(5H+g).

### 3.6 Uniformity

The algorithm needs G_v for the one scale v determined by n. |G_v| ≤ v^H = poly(n), so Remark R′ needs no further
argument [ours-R].

**The referee's concern** (review-theoremR §4). `thm_onecut` assembles G from `obtain`ed witnesses. Some have decidable
finite specifications (subgroup chain, words, codes, bijections, SLP tables), which a fixed machine can find by search.
But the specifications of the plan structure TT (`thm_tree`, H.2) and of `pc` (`prop_pieces`, J.2) contain value
identities quantified over all inputs, which cannot be checked by search.

**The audit** (review-uniformity, final; one reader, by reading the proof terms; nothing built). Verdict: the
algorithm is **uniform, with an n-independent table of constants that are not explicit**; the non-uniform fallback is
not needed. Its findings:
1. **TT and pc are structure literals** (`exists_thinTrees`, `Paper/Tree.lean` l. 1468–1512; `prop_pieces`,
   `Paper/Pieces.lean` l. 765–801). Their data fields are explicit functions of a few small combinatorial witnesses;
   their `value` fields are *theorems*, proved for every choice of those witnesses that meets its spec (`tree_value`;
   `prop_pieces_identity`, `lem_runnet`). The `Nonempty` wrapper of `thm_tree` is packaging.
2. **Every remaining v-dependent witness has a finite, decidable spec** (subgroup chain, host maps, short words, an
   embedding, a bijection, a sorted move order, a bounded law choice, codes, tags, the SLP), produced in poly(v) by the
   obvious algorithms. The crudest search costs 2^{O(v^{2C_p+1} log v)}, and H ≥ 288·C_p (`Paper/Cuts.lean`,
   l. 122–127, 466–469), so every search fits the 2^{O(v^H)} budget.
3. **Nothing depends on the input z**: `CutD` is a statement about a fixed G, `∀ z, z.size ≤ s → …`.
4. **The contracting hypothesis enters only through `exists_laws`**, a finite law table independent of n and v.

**The constant table:** h, θ and generators of A; the laws, with a fixed enumeration; the universal automaton;
finitely many evaluator programs; the integers a, e, C_p, v₁, a₀, C, H, C₀, v₀; the images ψ(θ). None depends on n.
Some come from ineffective existence proofs (Strassen duality); that affects explicitness, not uniformity.

**Caveat.** "The proofs remain valid for any spec-satisfying choice" is a meta-level parametricity argument
(`Classical.choose` is opaque, so a proof can use a chosen object only through its spec), not a Lean theorem. A
Lean-checked uniform statement needs a mechanical refactoring (§9, item 1), during which no proof may unfold a specific
enumeration (`Fintype.equivFin`, `Fintype.ofFinite`) beyond its spec. The paper's prose agrees (H.2: "the groups, the
words, the cosets and the maps χ ↦ χ̂ are constants of the program").

---

## 4. Theorem A: contracting implies ports

> **Theorem A** [ours-R, from AN-L and OA-L; +L in characteristic 0]. Let k be a field of characteristic χ, and suppose
> the contracting hypothesis holds over k. Then χ admits ports (EG Def. 11.1). More precisely, for every sufficiently
> large multiple h of the constant u of [AN] F.6, the Cayley graph G_h of U_h(F₂) with generators x_j = 1 + E_{j,j+1}
> (0 ≤ j < h−1) is a single-graph certificate in the sense of [HC] Thm 4.2, with degree 2(h−1) after padding.
>
> **Corollary A′.** If k has characteristic 0, then by [IM] Thm 7.1 there is a uniform deterministic algorithm deciding
> 3-SAT on v variables in 2^{O(v^{1−δ})}·poly.

*Proof.*
1. **[AN F.6, p. 40, `thm_poincare`]** [AN-L]: "There are an integer u ≥ 2 and a real number C₀ ≥ 0 such that for every
   l ≥ 2, h = lu, and every price on U_h, E_{g,a}|a, ga|² ≤ C₀ Σ_{j<h−1} E_a|a, x_j a|²". This is in the contracting
   case over k, with u and C₀ depending only on (μ, s). [AN App. M]: "Sections A to L use nothing about k except that it
   is a field, apart from the element ½ in Proposition E.1." The Lean `thm_poincare` is stated for any `Field K`.
2. **Every finite configuration in X_χ is an [AN] price over k** [ours-R, review-theoremAB §1]. On a finite set S an
   [EG]-spectral space has metric δ(S)·d_F for a Strassen point F over some field K of characteristic χ. Restrict F to
   tensors over the prime field P; if k ≠ P, lift to k by [EG] Lemma 2.3 ("For k ⊆ K, the possible joint values of
   spectral points on any family of tensors defined over k are the same over the two fields") [OA]. Push forward along
   the placement: this is c·d_φ for an [AN] spectral point φ over k (§2.1).
3. **Translation.** x_j is an involution, so G_h is (h−1)-regular on n = 2^{h(h−1)/2} vertices. The left side of F.6 is
   V(x), because (a, ga) is a uniform independent pair; the right side is C₀(h−1)·E_P(x). So V ≤ C₀(h−1)·E_P for every
   placement into every member of X_χ.
4. **[HC Thm 4.2]** [OA-L]. If X_χ had no ports, then C₀(h−1) ≥ c·log n/log h = c·h(h−1)/(2 log h). This is false once
   h/log h > 2C₀/c. So X_χ has ports, and by [HC §2.2] χ admits ports. ∎

**Lean form (characteristic 0).** Citing `exists_logarithmic_placement` instead of the paper's Thm 4.2 needs:
- **Padding** with 2^e − (h−1) loops per vertex, e = ⌊log₂(h−1)⌋ + 1 (the draft's ⌈log₂ h⌉ was meant). F.6 then gives
  exactly the constant C₀·2^e ≤ 2C₀(h−1) in OpenAI's normalisation; simplicity of the graph is not needed.
- **Constants.** With s = h(h−1)/2: `beats`, C₀·2^e ≤ s/(10000(e+3)), and OpenAI's separate hypothesis `large`,
  10000(e+3) ≤ s. The condition **40000(C₀+1)(e+3) ≤ h** implies both and holds for all large h (`ThmAArith.lean`,
  `exists_good_multiple`; u and C₀ are fixed before l). `large` alone needs h ≥ 491; both together, checked directly,
  need h ≥ 480 300 at C₀ = 1. The single condition h/(log₂h + 4) > 40000·C₀ of review-theoremAB §3 does not give
  `large` (Lean counterexample: C₀ = 0, h = 2). The conclusion is unaffected.
- **`scalar`**, the same Poincaré bound for real-valued placements, holds because finite subsets of a line are [AN]
  prices over every field [ours, internal note b2 §3(ii), from AN Prop. C.3 and Lemma C.4(a)]; it also follows from
  [EG] Thm 1.1 [OA]. The paper version needs no such hypothesis, since ℝ ∈ X_χ ([HC §2.3]).

**Machine-checked deduction.** `PortsLean/ThmA.lean` with `ThmAArith.lean` proves `theorem_A : … → Contracting →
PortZero` from four statements transcribed by hand from the labs' Lean (F.6; OpenAI's logarithmic-placement theorem
with `large` and `scalar`; containment of OpenAI targets in [AN] prices, one direction; line subsets are [AN] prices)
and two facts about U_h(F₂) (its order; x_j involutions). The labs' objects are opaque predicates; the field bookkeeping
(`AlgebraicClosure ℚ` against `K`) sits in the containment hypothesis. Faithfulness is checked by reading only. The
Lean covers characteristic 0 only.

**What Corollary A′ rests on.** [IM] Thm 7.1, hence [HC] Thm 13.1 and [EG] §§12–13. We have not reviewed IM 7.1 as a
whole; HC 13.1 has been re-read by the referee of review-c1 (§5.1). Lean: `middle_count_bridge`, no `sorry` in that
directory by grep; not built.

---

## 5. Characteristic p

All of §5 is refereed in review-c1 (verdict: "No fatal gap"), from `c1d1/notes.md` Part C1. Where the notes and the
report differ, we follow the report.

### 5.1 What the mod-p counters accept

**OpenAI side.** [HC Thm 13.1, verbatim] [OA]: "Fix a characteristic admitting ports. There is an η > 0 such that
every closed bit network of volume at most s and maximum degree at most s^{1/20}, over any field of this
characteristic, has a formula for its contraction using 2^{O(s^{1−η})} arithmetic operations and local entry queries.
The topology determines the formula, which can be generated deterministically in 2^{O(s^{1−η})} bit operations and uses
fixed prime-field constants. …" A bit network has arbitrary tables at its vertices and sums over one bit per wire;
with {0,1} tables read in F_p the contraction is the number of consistent labellings mod p, and XOR, AND, equality and
pin tables are admissible. The proof uses characteristic 0 only in its final paragraph. **Constants** (wording fix):
HC itself allows them in a finite field E₀ ⊇ F_p of degree bounded independently of n (HC l. 3664–3667); so the
constants lie in F_p or a fixed finite extension of F_p, which is immaterial.

**Anthropic side.** Def. J.1 is an exact identity in A with no scalar; the laws are exact covers; ring entries in
programs are exact sums of products of generators; the referee found no field division in §§G–J. In characteristic p,
A/𝔪 = F_q is a finite field (Zariski) and ψ(sum(z)) is the weighted count mod p, with constants ψ(θ) in F_q.

Neither counter needs a 3-CNF, so a hash test is admissible.

### 5.2 Isolation in the power-saving regime [ours-R; core +L]

**Toeplitz hash.** For 1 ≤ k ≤ n+1, a ∈ F₂^{n+k−1}, b ∈ F₂^k: h_{a,b}(x)_j = b_j + Σ_i a_{n−1+j−i}x_i. Equivalently,
h_{a,b}(x) − b lists the coefficients of t^{n−1}, …, t^{n+k−2} of a(t)·x(t) in F₂[t]: **one polynomial
multiplication over F₂**.
- **Pairwise independence** (Lemma C1): for x ≠ y, (h(x), h(y)) is uniform. In fact T_a z is uniform for every k ≥ 1.
- **Circuit** (Lemma C2): for fixed a, x ↦ T_a x is F₂-linear. Schönhage's ternary method (or Cantor–Kaltofen) is a
  division-free bilinear program over F₂; with one operand fixed it becomes an XOR-only circuit of size
  O(n log n log log n), built in poly(n) time. Every wire is a function of x, so the attached gates are parsimonious.
- **Valiant–Vazirani** (Lemma C3): if 2^{k−2} ≤ |S| ≤ 2^{k−1}, then Pr[|S ∩ h^{−1}(0)| = 1] ≥ q(1−q) ≥ 3/16,
  q = |S|/2^k. A good k exists in {2, …, n+1}, so for uniform k the success probability is ≥ 3/(16n), and 16n rounds
  fail with probability ≤ e^{−3}.

> **Lemma C4** [ours-R; Tseitin step +L]. Let p be prime, δ > 0. A deterministic power-saving algorithm that either
> computes #3-SAT mod p, or merely answers "yes" on uniquely satisfiable and "no" on unsatisfiable 3-CNFs, yields for
> every δ′ < δ a randomised one-sided-error algorithm for 3-SAT in 2^{O(v^{1−δ′})}·poly.

*Proof.* Repeat 16n times: draw k, a, b; form F′ = F ∧ Tseitin(C) ∧ (outputs = 0), C the circuit of Lemma C2 (four
width-3 clauses per gate). #F′ = |S_F ∩ h^{−1}(0)| by parsimony, v′ = n + O(n log n log log n), and
16n·2^{O(v′^{1−δ})} ≤ 2^{O(n^{1−δ′})}. ∎

> **Corollary C5** [ours-R]. rWETH ⇒ UWETH ⇒ ⊕_pWETH, for every prime p.

**Derandomisation** [ours-R]. *Non-uniform:* there are ≤ 2^{8v³} 3-CNFs on v variables and
(1 − 3/(16v))^{64v⁴} < 2^{−8v³}, so one list of 64v⁴ triples (k, a, b), O(v⁵) bits, isolates for all of them; every
randomised algorithm below becomes deterministic with poly(v) advice, refuting nuWETH. *Uniform, under the
Impagliazzo–Wigderson hypothesis:* poly(T) seeds fool a one-sided test of time T, and the class 2^{O(v^{1−δ})} is
closed under polynomials, so nothing is lost in δ. *Unconditional and uniform:* no route known (an assessment).

**Machine-checked** (`research/ports/lean-c1/`).
- Toeplitz pairwise independence over **any finite field**, for all n, k, with the notes' indexing (`hash_pairwise`;
  surjectivity of a ↦ T_a z for z ≠ 0 over any field, `toeplitz_surjective`).
- Isolation ≥ **3/16 on the window M ≤ 4N ≤ 3M** (N = |S|, M = |range|), for any finite family with uniform marginals
  and pairwise independence at the target (`isolation`). The window contains the notes' 2^{k−2} ≤ N ≤ 2^{k−1}; the
  marginal hypothesis is needed separately when |S| = 1.
- Composition: for **n ≥ 1**, the average over k ∈ {2, …, n+1} is **≥ 3/(16n)** (`avg_succProb`). The notes' "such k
  exists" fails for n = 0.
- **Tseitin parsimony** (`Circuit.card_tseitin`, `gateClauses_iff`).
- **Not covered:** the multiplication circuit and its size O(n log n log log n) (Lemma C2), including the
  identification of the hash with one polynomial product; the link to either lab's counting theorem (HC 13.1, or
  Theorem R with the program-model encoding); the sparsification; the exponent arithmetic; the derandomisation.

### 5.3 The theorems

> **Theorem C1-OA** [ours-R, from OA]. Assume characteristic p admits ports and HC 13.1 as printed. Then 3-SAT on v
> variables has a randomised one-sided-error algorithm in 2^{O(v^{1−δ})}·poly, for any δ < min{α, 1 − (1+4α)(1−η_p)},
> with 0 < α < 1/4, (1+4α)(1−η_p) < 1, and η_p the η of HC 13.1 for characteristic p. This is the same *formula* for δ
> as IM 7.1, not the same δ.

*Proof outline.* Sparsify as in IM 7.1. Repeat 16v times: draw (k, a, b) once for all leaves; for each leaf F_j build
IM 7.1's bit network and attach natively, to one extra copy of each variable, the XOR circuit of Lemma C2: one ternary
table per gate, equality trees at fan-outs (degree ≤ 3), a and b pinned or folded into the gates, outputs pinned to 0.
The added volume O(v log v log log v) is below v^{1+4α}. The contraction over F_p is
|{x : F_j(x), h(x) = 0}| mod p; compute it by HC 13.1 and accept if some leaf gives a nonzero value. **Leaves are tested
separately**, never summed: every leaf implies F ("Both children imply the parent", IM), so on the isolation event
every leaf count is 0 or 1 and the leaf containing the solution gives 1. Soundness is unconditional. Time:
16v·2^{O(v^{1−α} log v)}·2^{O(v^{(1+4α)(1−η_p)})}. ∎

> **Theorem C1-AN** [ours-R, conditional on Theorem R's inputs]. If the contracting hypothesis holds over a field k of
> characteristic p, the same conclusion holds for any δ < 187/(5H_k+187), H_k the constant of J.4 for k.

*Proof outline.* Replace z_j of §3.5 by (P′, ⟨F_j, C⟩), where P′ guesses x, checks F_j, evaluates C gate by gate with
values in a persistent balanced tree (O(log G) steps per gate), and fails unless all outputs are 0. With the
**padding fix e = 0**, sum = |{x : F_j(x), h(x) = 0}|·1_A exactly. τ₀ and |z| grow by O(n log² n log log n), below L.
Then evaluate by Theorem R(a) and ψ: A → F_q, test leaves separately as above. ∎
- Without the padding fix the route fails at p = 2: sum = 2^e·#SAT ≡ 0 whenever n is not a power of 2. For odd p, 2^e
  is a unit.
- C1-AN inherits Theorem R's open points: uniformity rests on the audit (§3.6), and the per-cut part of Lemma 1 is a
  reading. Its non-uniform form (G_v and the hash list as advice) refutes nuWETH.

**Deterministic variants** (review-c1 §7 and S4(b)). Without the hash, the same networks or programs solve
Unique-3-SAT deterministically (overlapping leaves are harmless), refuting UWETH. Exact counting mod p needs a
**disjoint** sparsification: the petal child also adds the negated centre as unit clauses; the referee re-checked IM's
depth and leaf count with this change. With it, ports in characteristic p, or contracting over a field of
characteristic p (with the padding fix), give #3-SAT mod p deterministically, refuting ⊕_pWETH.

**Correction to an earlier review.** review-theoremR passed a "#3-SAT mod p" corollary of our working notes. As written
it was wrong: at p = 2 the factor 2^e kills the count, and overlapping leaves do not add up to #F. With both fixes it
is correct (review-c1 §5).

> **Corollary 1′** [ours-R]. Under rWETH, or under nuWETH: no characteristic admits ports, and the contracting
> hypothesis fails over every field; hence, by `thm_alt`, the flat hypothesis holds over every field.

*Proof.* Ports in characteristic p contradict rWETH by C1-OA (nuWETH by derandomisation); ports in characteristic 0
contradict WETH, hence rWETH and nuWETH, by IM 7.1. Contracting over k gives ports in char k by Theorem A; or,
without OpenAI's results, contradicts rWETH by C1-AN (characteristic p) and Theorem R (characteristic 0). ∎

---

## 6. Theorem B: finite objects

> **Theorem B** [ours-R].
> (i) **Sharp form** [AN-p]. For each μ ≥ 3 and each field k: the contracting inequality fails at μ (no s with 1 ≤ s,
> s² < μ works for all prices on Mat_μ(F₂)) **iff** ρ_μ = √rk is an [AN] price on Mat_μ(F₂) over k.
> (ii) If for some μ ≥ 2 the metric ρ_μ is not an [AN] price over ℚ, then the contracting hypothesis holds over ℚ (at
> max(μ, 3)). Hence the conclusions of Theorem R and of Corollary A′ hold.
> (iii) The same holds if the five-point set M5 = {0, I, e₁₁, e₂₂, e₁₁+e₁₂} ⊂ Mat₂(F₂), with the restricted metric, is
> not an [AN] price over ℚ. Its squared distances are 2 on the pairs 0–I, e₁₁–e₂₂ and (e₁₁+e₁₂)–e₂₂, and 1 on the
> other seven pairs.
> (iv) **Contrapositive.** Under Weak ETH, ρ_μ is an [AN] price over every field of characteristic 0, for every μ, and so
> is M5 (via Theorem R, or via Theorem A with [IM] 7.1; under nuWETH via Remark R′). Under rWETH or nuWETH the same
> holds over every field (Corollary 1′).

*Proof.*
- **(i) ⇐.** If ρ_μ is a price, D(r)² = r·D(1)², so D(μ) = √μ·D(1) > s·D(1) for every s < √μ.
- **(i) ⇒.** Steps 2–7 of the proof of D.2 (pp. 30–31). Step 2 uses failure at this μ only: "As the contracting
  hypothesis fails, for every s with 1 ≤ s < √μ there is a price on Mat_μ(F₂) with D(μ) > sD(1)". Step 5 needs μ ≥ 3.
  In Lean, `thm_alt_rank_price` assumes the global ¬Contracting K, but the proof of `thm_alt_extremal` uses it only
  through `hK ⟨μ, √t, …⟩` at the given μ (`Alternative.lean`, l. 306ff.). So the per-μ form is read from the proofs,
  not stated.
- **(ii), (iii).** Pull-back along an injection preserves prices [AN A.3]. M5 ⊂ Mat₂(F₂) (ten ranks recomputed), and
  a ↦ diag(a, 0) maps Mat_μ into Mat_{μ′} preserving rk(a − b). So "M5 not a price" ⇒ "ρ₂ not a price" ⇒ "ρ_{μ′} not a
  price for all μ′ ≥ 2". By (i) at μ′ = 3, contracting holds over ℚ.
- **(iv)** is the contrapositive, with Corollary 1′ for the last sentence. ∎

**[AN] price, not Strassen point (referee fix).** (iv) asserts that ρ_μ is an [AN] price: a limit of c·d_φ with φ
multiplicative and cover-subadditive. It does *not* assert that ρ_μ is the wire metric of a point of Strassen's
asymptotic spectrum; that would need an unreviewed reading of the proof of [EG] Lemma 11.3.

**"Finite" is not "decidable" (referee fix).** Each object is one metric on 5, 16 or 512 points, but price-ness is
asymptotic. By duality ([AN] Thm A.6), refuting it needs a family of covers of the tensor powers C^N of the
ρ_μ-weighted network with exponential saving; one cover in fixed dimensions constrains d_φ, not the price. No finite
certificate is known for either side. No metric-only inequality valid in all CAT(0) spaces can exclude ρ_μ or M5, since
√2·ρ_μ embeds isometrically in the Bruhat–Tits building of GL_{2μ}(F₂((t))) [ours, internal note c1 §2;
referee-checked]; conditions involving non-wire tensors, and [AN]'s crossing inequality B.3, remain open.

---

## 7. Corollaries, the case table, and consequences

> **Corollary 1.** Let k be a field of characteristic 0. Under Weak ETH:
> (a) the contracting hypothesis fails over k;
> (b) hence, by `thm_alt` in its proved form ¬Contracting K ⇒ Flat K, the flat hypothesis holds over k, and ρ_μ is an
> [AN] price over k for every μ (Theorem B(iv)).
>
> Part (a) has two independent proofs:
> - **via Theorem R:** [AN] and classical facts only. Uniformity rests on the audit (§3.6). Under nuWETH, Remark R′
>   gives (a) without the audit.
> - **via Theorem A and [IM] 7.1:** uses OpenAI's results, but not [EG] Thm 1.2.

*Proof.* Contrapositive of Theorem R, respectively of Corollary A′, applied to k itself. Both hypotheses are per field
(D.1: "two hypotheses on the field k"), so no transfer between fields is needed. ∎ [ours-R]

Corollaries 1 and 1′ are conditional proofs of [AN]'s flat hypothesis. They do not use [EG] Thm 1.2 ("Over every field
there is a spectral flat of every positive finite dimension"), which would give it unconditionally via §2.1.

**The case table** (one characteristic χ; "contracting" means over some field of characteristic χ).

| Cell | Possible? | 3-SAT consequence | Permanent / HC bounds that apply |
|---|---|---|---|
| contracting, ports | Not excluded by anything either lab proves [ours-R, review-AB §6]. Contradicts Weak ETH (χ = 0) and rWETH (any χ). | χ = 0: deterministic power-saving decision (Theorem R; Cor. A′). χ = p: randomised one-sided (C1-AN, C1-OA) | [AN] K.7: 2^{c(log m)²/log log m}. [HC] 12.2 [OA]: L^{[N]}_F(HC_N) > 2^{N^ε} |
| contracting, no ports | **Impossible** (Theorem A) | — | — |
| not contracting, ports | Not excluded | χ = 0: via [IM] 7.1 only. χ = p: C1-OA only | [AN]: flat-case bound E.11. [HC] 12.2 [OA] |
| not contracting, no ports | Not excluded. Forced by Weak ETH (χ = 0) and by rWETH (any χ) | none from these sources | [AN] E.11 / Thm 1.1: 2^{c(log m)^{4/3}}. [HC] Thm 1.1 [OA]: exp(c(log N)²/(log log N)²) |

The flat hypothesis is *not* a column: [AN] does not show flat and contracting exclusive, and Euclidean configurations
satisfy the contracting inequality (D(μ)²/D(1)² < 2 for Euclidean pull-backs; ours, c1 §4).

**The two labs' permanent bounds** are unconditional claims; nothing here changes them. [AN] Thm 1.1,
2^{c(log m)^{4/3}}, comes from the flat case ("The exponent 1/3 comes from the flat case alone", p. 59); under Weak ETH
the contracting-case bound K.7 holds vacuously in characteristic 0. Conversely, by Theorem A, wherever the contracting
case occurs, [HC] 12.2 (2^{N^ε}) applies too, conditionally on [HC] 12.2. The ports branch of [HC] is excluded in
characteristic 0 by Weak ETH ([IM] 7.1) and in every characteristic by rWETH (C1-OA); [HC] Thm 1.1 then rests on its
no-ports part. (Referee fix:) [HC] Thm 1.1 is weaker than [AN] K.7 by a factor log log in the exponent and stronger than
[AN] Thm 1.1, but the measures differ: [HC] bounds the degree-component border size L^{[N]}_F, [AN] exact circuit size
(and approximate circuits, Thm 1.4).

**Tensor rate of K_{2,3}** (companion note `note-k23-rate.md`; sources `hull/notes.md`, `review-hull.md`,
`review-fivepoint.md`). Let f*(K_{2,3}; k) be the supremum of rates of asymptotic restriction protocols over k from the
six binary wires u_iv_j of K_{2,3} to the four wires v₁v₂, v₂v₃, v₁v₃, u₁u₂. (i) If the contracting hypothesis fails
over k, then f*(K_{2,3}; k) ≤ 3/√10; border protocols are included over infinite k [ours-R, review-hull]. (ii)
Unconditionally, f*(K_{2,3}; k) ≥ 3/√10 over every field [ours; computer-assisted: the reduction to books and the
calibration were refereed at an interim stage, and one six-variable inequality is certified by interval arithmetic
with an independent checker]. So under Weak ETH, by Corollary 1, f*(K_{2,3}; k) = 3/√10 exactly over every field of
characteristic 0. Statements, scope and proofs are in the companion note.

**Conditional circuit lower bounds over F₂.** Our Theorem M1 (`mm/anti/notebook.md`) gives Ω(n²√log n) lower bounds
for B₂-circuits multiplying n × n matrices over F₂, the Boolean semiring and related products, assuming that some prime
has no ports. Its corrected dependency list (review-c1 §7) is: rWETH (or nuWETH, or UWETH, or ⊕₂WETH with the disjoint
sparsification of §5.3); [HC] 13.1 at the chosen prime; the sunflower sparsification of [IM] §7; [MM] Lemma 4.1 as
printed; and our Lemmas E and P. Neither Theorem R nor Theorem A is needed. The B₂-circuit bounds need only *some*
prime without ports; p = 2 is needed only for part (a)'s F₂-networks and parity-nondeterministic circuits.

---

## 8. Dependencies and status

We built neither lab's Lean. "Lean-backed" means a Lean statement exists per the lab, and we read it.

**Imported statements.**

| Statement | Location | Lean-backed | Our check |
|---|---|---|---|
| D.1, D.2 (¬C ⇒ F), D.2 Steps 2–7 | AN pp. 30–31 | `def_cases`, `thm_alt`, `thm_alt_rank_price` | proof term read; per-μ use read in `thm_alt_extremal` |
| F.6 Poincaré on U_h | AN p. 40 | `thm_poincare` | statement read; scalar case consistent with numerics (review-AB §3) |
| G.2 laws; A finitely generated; J.3, J.4 | AN pp. 43, 53–55 | `exists_laws`, `exists_setting`, `thm_onecut`, `thm_cut` | statements and proofs read; guess sites read; machine file copied (§3.3) |
| A.3 pull-backs, A.6 duality | AN | yes (per AN §3) | statements read |
| EG Def. 11.1, Lemma 2.3 | EG | `HasWireExpanders`, — | Lemma 2.3 proof read by referee |
| HC Thm 4.2 | HC | `exists_logarithmic_placement` (char 0; `scalar`) | proof re-read by referee |
| HC Thm 13.1 | HC | not checked | statement and proof re-read in review-c1 §1, incl. char p |
| IM Thm 7.1 | IM | `middle_count_bridge` | **not reviewed as a whole**; sparsification checked |
| MM Lemma 4.1 | MM | — | statement and proof read in review-c1 §7 (only for §7) |
| HC Thm 1.1, 12.2 | HC | 1.1 with this exponent "remains unformalized" per OA docs | quoted only |
| Sparsification (both forms); Zariski; VV; fast F₂[t] multiplication | classical; IM §7 | — | counting re-checked; disjoint form refereed |

**Our own steps.**

| Step | Refereed? | Our Lean |
|---|---|---|
| §3.2; Theorem R(a), (b) | yes (review-R §§2–3) | `ThmR.lean`: all arithmetic, J.4 and per-cut counts as hypotheses |
| Lemma 1 (guess count) | yes, as a reading of prose and Lean (review-R §1) | composition sum; `compC` additivity, `pickB` cost. Per-cut counts and threading through `thm_cut`: not done |
| Lemma 2, pruned enumeration | yes, with the pruning fix | `PrunedTree.lean` (abstract run trees) |
| Uniformity of Theorem R | by audit (review-uniformity): one reader, meta-level argument | — |
| Turing-machine reading of R(a) | no | — |
| Theorem A | yes (review-AB §§1–3, 9) | `ThmA.lean`, `ThmAArith.lean` (char 0, four transcribed hypotheses; size condition supersedes review-AB §3) |
| §5 (C1-OA, C1-AN, C4, C5, derandomisation, disjoint branching) | yes (review-c1), with its fixes | `lean-c1` (§5.2) |
| Theorem B; Corollaries 1, 1′; case table | yes (review-AB §§5, 7, 9; review-R §6); 1′ composes refereed steps | — |

---

## 9. Open points

1. **A Lean-checked uniform Theorem R (§3.6).** Turn the choice witnesses (`Gam`, host maps, `idx`, `coQ`, `FQ`, `FU`,
   `eE`, route words, `ch`, `Pl`, uses of `Fintype.equivFin`, the SLP) into parameters or computable `def`s, and restate
   `thm_onecut` as `CutD … (Gprog v τ s k)` with `Gprog` an explicit function of the constant table. Mechanical
   according to the audit, not done. A second reader of the audit would also help.
2. **Machine-checking Lemma 1 in full.** Done: guess-annotated semantics on a verbatim copy of [AN]'s machine file,
   per-construct bounds, `pickB`, `compC` additivity, the composition arithmetic, the pruned evaluator. Remaining:
   `bitsB`; the one-cut bound for `dealProg` (estimated 1.5–3k lines of overlay); the restatement of
   `thm_onecut_program`, `thm_cut_compose` and `thm_cut` with g ≤ τ/v^235 (needs the 261-file closure of [AN]'s
   development). All of this needs [AN]'s Lean built.
3. **[IM] 7.1 as a whole** is needed for the route via Theorem A in characteristic 0; we have reviewed HC 13.1 but not
   the rest of IM 7.1's proof.
4. **Counting in the number of variables.** With the disjoint sparsification (§5.3), Theorem R(a) gives #3-SAT exactly
   in characteristic 0 and #3-SAT mod p in characteristic p, in 2^{O(n^{1−δ})}. The characteristic-p form is refereed
   (review-c1); the characteristic-0 form combines refereed steps but has not itself been refereed [ours].
5. **Unconditional uniform derandomisation** of §5: no route known.
6. **Omitted.** A corollary about the optimality of our own decomposition engine under Weak ETH ("Corollary 2" of the
   working notes) rests on unchecked internal results; not claimed. The statement that the ports algorithm "obeys all
   flat floors" is heuristic and not used.
7. **Explicit constants.** H, u, C₀, η_p and the laws are not explicit; nor is δ.

---

## 10. Outlook (unrefereed in full; not claimed)

**Engine gap** (Theorem D of `c1d1/notes.md`). For "tower engines" of the type of [AN]'s algorithm (levels with p
fixed merges, node growth K ↦ K^β, configurations from a finite list), if the certified log-exponent α′ satisfies
**α′ > ½·log_β p** along infinitely many n, then the flat hypothesis fails over k and contracting holds over k̄, with the
consequences of Theorem R and §5. For p = β = 2 the threshold is 1/2.
- Status: the referee of review-c1 §8 found the averaging step correct; it needs the condition E_C ≥ 1 (raw bits per
  copy = E_C·λ) stated, and one side remark ("if L stays bounded then α′ = 0") replaced. The win-win theorem it relies
  on was not re-checked there. The statement concerns certified exponents, not running times.
- Grey zone: deficits below the level floor that tend to 0 can accumulate over the ≤ log log n levels up to a factor
  (log n)^{o(1)}, consistently with the flat hypothesis as stated (prices are limits, with no rate). So the sharp form
  "certified time 2^{o(n/√log n)} forces ¬flat" does not follow.
- If OpenAI's flats theorem (EG 1.2) holds, the hypothesis α′ > ½·log_β p never holds and the theorem is vacuous; what
  remains is an optimality statement for the class.

---

## Changes in v2

- **New §5 (characteristic p),** from review-c1: C1-OA, C1-AN, Lemma C4, Corollary C5, derandomisation, disjoint
  sparsification, Corollary 1′, the hypotheses table of §1. Fixes: "same formula for δ"; constants in a fixed finite
  extension of F_p; padding fix e = 0 needed at p = 2; counting needs the disjoint sparsification; the earlier review's
  pass of "#3-SAT mod p" recorded as an error. Machine-checked core (`lean-c1`) stated with what it does not cover.
- **Lean status.** Both our projects build with no `sorry` and only standard axioms (the draft called `ThmR.lean`
  unconfirmed). Added: v := ⌈τ^{1/(H+187)}⌉, τ′ := v^{H+235}; the side conditions H > 112.2, v₀ depending on C_cut,
  H ≥ 235; the guess-count overlay and what remains; the findings on `Does`/`Gives` and accepting runs; the size
  condition for Theorem A (thresholds 491 and 480 300); e = ⌊log₂(h−1)⌋ + 1. The J.3 condition 4 lg τ′ ≤ (lg v)² in the
  check of R(a) was replaced by J.4's own side condition.
- **§3.6** states the audit's final verdict. **K_{2,3}** and **Theorem M1**: one paragraph each in §7.
  **Theorem D**: outlook only, corrected. §§2 and 8 shortened; Theorem B is now §6.
