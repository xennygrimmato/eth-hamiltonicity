# The contracting case of the tensor-price dichotomy contradicts the weak exponential-time hypothesis

*First full draft, 26 November 2026. Working title.*

---

## 0. What is shown, and what is not

Anthropic's paper "VP ≠ VNP over every field" [AN] proves its permanent lower bound by a case split: over every
field k, the *flat* or the *contracting* hypothesis holds (AN Def. 2.1 = Def. D.1; Thm 2.2 = Thm D.2; Lean `thm_alt`).
We show that the contracting case has an algorithmic consequence, which the paper does not mention. If the contracting
hypothesis holds over a field of characteristic 0, then 3-SAT on n variables can be decided deterministically in time
2^{O(n^{1−δ})}·poly for some δ > 0. We give this in two ways.
- **Theorem R** uses only [AN] and classical facts. Its status differs by form:
  - The form with poly(n)-size advice has been refereed.
  - That the advice can be computed, so that the algorithm is uniform, rests on an audit of [AN]'s Lean proof terms by
    one reader (§3.6).
- **Theorem A** passes through OpenAI's "ports" property [EG, HC] and OpenAI's IM Theorem 7.1.

**Theorem B** reduces the hypothesis to finite metric objects. **Corollary 1** follows: under the weak exponential-time
hypothesis (Weak ETH), the contracting hypothesis fails over every field of characteristic 0, and so (by `thm_alt`) the
flat hypothesis holds there. This does not use OpenAI's theorem that flats exist (EG Thm 1.2). Via Theorem R it uses no
OpenAI result at all.

**What we do not show.**
- We do not claim that the contracting hypothesis holds or that it fails.
- We prove no unconditional algorithm and no unconditional lower bound.
- We do not decide whether the two cases exclude each other. [AN] does not decide this either (D.3: "We do not show that
  the two cases exclude each other").
- Every conclusion below is an implication between hypotheses, each with the status recorded in §6.

**Provenance of the sources.** Both source papers were produced by AI systems and have not been refereed by people.
- [AN, §3, p. 11]: "The proofs in this paper were found and written by AI. No human mathematician has checked the
  proofs."
- The README of OpenAI's release says it contains "manuscripts and supporting proof artifacts produced by an unnamed
  internal OpenAI model", "best understood as a form of raw research data".
- Both labs supply Lean developments. We read parts of both, but we built neither.

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

The internal referee reports are `review-theoremR.md` and `review-theoremAB.md`.

---

## 1. Sources and conventions

- **[AN]** Anthropic, "VP ≠ VNP over every field", Nov. 2026, with Lean development
  (github.com/anthropics/formal-math, `vp-vnp`). Page numbers refer to its paper.pdf.
- **[EG]** OpenAI, "Euclidean geometry in the asymptotic spectrum of tensors", 24 Nov. 2026.
- **[HC]** OpenAI, "Circuit lower bounds for Hamiltonian cycle and the permanent", 24 Nov. 2026.
- **[IM]** OpenAI, "The logarithmic exponent of integer multiplication on tapes", 24 Nov. 2026.
- **OpenAI Lean**: `OAI/Computability/MultitapeWeakETH/{Price,Cloud,MiddleDecision}.lean` in OpenAI's release.

**Weak ETH.** We use the formulation of [IM, §1, p. 1]: "for no fixed 0 < δ < 1 can a deterministic algorithm decide
3-SAT on v variables in time 2^{O(v^{1−δ})} times a polynomial in the input length". OpenAI's Lean `WeakETH`
(`Price.lean`) asks for a single `FiniteMultiTapeMachine`, so it is *uniform*.
- **Non-uniform Weak ETH** (nu-Weak ETH) says the same for algorithms that may also receive, for each n, an advice string
  of length poly(n).
- nu-Weak ETH implies Weak ETH. Ordinary ETH implies Weak ETH. Whether ordinary ETH implies nu-Weak ETH depends on
  which non-uniform form of ETH one assumes; we only use the two hypotheses as defined here.

---

## 2. Definitions

### 2.1 Anthropic's spectral points, prices and the two hypotheses

[AN, Def. 2.1, pp. 4–5, `def_cases`; restated as Def. D.1, p. 30] Let V be a finite set of *parties*.
- A *V-tensor* over k is an element of ⊗_{v∈V} k^{n_v}. *Products* are taken party by party. s is a *restriction* of t
  if s = (⊗A_v)t for linear maps A_v.
- A *spectral point* φ on V is a function from V-tensors to [0, ∞) with φ(1) = 1 and φ(st) = φ(s)φ(t), and with
  "φ(s) ≤ Σ_j φ(t_j) whenever s = Σ_j s_j with every s_j a restriction of t_j".
- The *wire* ⟨q⟩_{uv} is the q × q identity in the indices of u and v. There is a pseudometric d_φ with
  φ(⟨q⟩_{uv}) = q^{d_φ(u,v)} (`lem_exponents`).
- A *price* is "a pointwise limit of functions c·d_φ with real numbers c ≥ 0" (`def_price`).
- For a price on Mat_μ(F₂), "D(r)² [is] the mean of |a, a+W|² over all a and all W of rank r". Here F₂ only labels
  the parties: "its F₂ is not the field k" (p. 5).

> **Flat hypothesis** (D.1): "All finite subsets of all Euclidean spaces, with their metrics, are prices."
> **Contracting hypothesis** (D.1): "There are an integer μ ≥ 2 and a real number s with 1 ≤ s and s² < μ such that
> D(μ) ≤ s D(1) for all prices on Mat_μ(F₂)."

Lean: `Paper/Alternative.lean`, `def Contracting`, `def Flat`. Every price has D(μ) ≤ √μ·D(1) (p. 5), so the
contracting hypothesis improves the trivial bound by a constant factor at one μ.

**Remark (how this class compares with Strassen's).** [AN] notes after Def. A.1 that its class "is larger than
Strassen's asymptotic spectrum". Every point of Strassen's spectrum (OpenAI's spectral point, [EG §2.1]) is an [AN]
spectral point: s = Σs_j is a restriction of ⊕s_j, and Strassen points are additive and monotone. [ours-R:
review-theoremAB §1]

**Theorem 2.2 / D.2** (`thm_alt`) [AN-L]: "Over every field k at least one of the two hypotheses of Definition 2.1
holds." The Lean proof is

    by_cases hK : Contracting K; · exact Or.inr hK; · exact Or.inl … thm_alt_euclidean hK …

(`Alternative.lean`, l. 921ff.). That is, **¬Contracting K ⇒ Flat K**, as in the printed proof: "We assume that the
contracting hypothesis fails and derive the flat one" (p. 30).

**The rank metric.** Put ρ_μ(a, b) = √rk(a − b) on Mat_μ(F₂). Steps 2–7 of the proof of D.2 produce, when contracting
fails, a price with |a, a′|² = rk(a − a′) for μ ≥ 3 (Lean `thm_alt_rank_price`, hypothesis ¬Contracting K). Remark D.3
records that this price is not Euclidean.

### 2.2 Anthropic's program model and cuts

[AN §I.1, pp. 48–49]
- Data are binary trees. A program is built from: fixed tree, argument, first, second, pair, if, run, guess, fail,
  weight, use. "Every construct costs one step."
- `guess` gives "two runs, with outputs nil and (nil, nil)". `weight` multiplies the run's weight by a named generator
  of a finitely generated ring A ⊂ k. `use` appends a name to a tally.
- An instance z is a pair (program, argument). "An instance z is τ-plain if all its runs halt and every accepting run
  has an empty tally and costs at most τ. The sum sum(z) ∈ A of an instance is the sum of the weights of its accepting
  runs."

[AN Def. J.1, p. 52, verbatim]:
> "A program G cuts (τ, s) into (τ′, s′) with P pieces in t steps if the following holds for every instance z with
> |z| ≤ s. • All runs of G on z halt. The accepting ones take at most t steps, have empty tallies, and output lists of
> at most P instances of size at most s′. • If z is τ-plain, then all these instances are τ′-plain, and
> sum(z) = Σ_runs weight · Π_{y in the list} sum(y), where the sum is over the accepting runs of G on z."

Lean: `CutD` (`NS1/Compose.lean`, l. 25). It tracks steps and pieces. **It does not track guesses.**

[AN Thm J.3, p. 53, `thm_onecut`] [AN-L]: "There are constants a₀, C, v₀ such that the following holds with
Λ = (lg v)^C, for all v ≥ v₀, all τ ≥ v^{a₀} with 4 lg τ ≤ (lg v)², all s ≤ τ and all 2 ≤ k ≤ v^64. Some program of
size at most v^{a₀} cuts (τ, s) into (τΛ/k, (s/k + τ/v^256)Λ) with at most kΛ pieces, in (s + τk/v^256)Λ steps."

[AN Thm J.4, pp. 54–55, `thm_cut`] [AN-L]: "There are a multiple H ≥ 272 of 16 and constants C_cut, v₀ such that the
following holds whenever v ≥ v₀ and α satisfy (lg v)^{C_cut α} ≤ v. For all τ and s with v^H ≤ τ ≤ v^{Hα} and
s v^48 ≤ τ, some program of size at most v^H cuts (τ, s) into (v^H, v^{H−32}) with at most τv²/v^H pieces in at most
τ/v^24 steps."
- §§F–K assume the contracting case throughout (p. 37: "In this section and in Sections G to K we are in the
  contracting case").
- J.4 involves no circuit and no permanent. The permanent enters only in K.3 (§1.1 of the rebase notebook tabulates
  this).
- Lean `exists_setting` (`Paper/Cuts.lean`, l. 570) supplies, for any `Field K` with `Contracting K`, a subring A with
  `Algebra.FiniteType ℤ A`, named generators θ and the hypotheses of `thm_cut`.
- In the Lean, H = 16(a₀ + 217). H is not explicit.

### 2.3 OpenAI's ports

[EG Def. 11.1, verbatim]:
> "A field has ports if it admits a family of regular, symmetric multigraphs of unbounded order and bounded degree, and
> a constant γ such that V(x) ≤ γE_G(x) for every graph in the family and every assignment into a spectral space over
> the field."

Here E_G(x) = |V|^{−1} Σ G_ij d(x_i, x_j)² and V(x) = |V|^{−2} Σ d(x_i, x_j)². [EG] adds: "This property depends only on
the characteristic." [HC §2.2] defines X_χ as the class of Hadamard spaces with spectral prices over fields of
characteristic χ, and says "The condition for X_χ is precisely port admission by χ".

[HC Thm 4.2, verbatim] [OA-L]:
> "Let P be the walk on a d-regular multigraph with n ≥ 2 vertices, d ≥ 1, and uniform stationary law π. Suppose that
> V_π(x) ≤ βE_P(x) for every placement x in every member of a class of Hadamard spaces without ports. Then
> β ≥ c log n/log(d+1) for an absolute constant c > 0."

The Lean counterpart, for characteristic 0, is `exists_logarithmic_placement` (`Cloud.lean`, l. 83). It is stated for
order 2^s and degree 2^e, with threshold s/(10000(e+3)). It carries an extra hypothesis `scalar`, which we discharge in
§4.

[IM Thm 7.1, verbatim] [OA-L]:
> "If characteristic zero admits ports, then for some δ > 0 a deterministic algorithm decides 3-SAT on v variables in
> 2^{O(v^{1−δ})} bit operations times a polynomial in the input length. In particular, under variable-count Weak ETH,
> characteristic zero does not admit ports."

- Its proof rests on [HC Thm 13.1] (enumerable contraction, under ports).
- Lean: `middle_count_bridge : PortZero → PowerSavingDecision …` and `price_of_variable_weakETH : WeakETH → PriceZero`
  (`MiddleDecision.lean`). `PortZero` is stated over `AlgebraicClosure ℚ`.

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

**Status of Theorem R.**
- The *non-uniform form* is refereed (review-theoremR). In that form the cutting program G_v of J.4, of size
  ≤ v^H = poly(n), is supplied as advice.
- Computing G_v from v, which gives the uniform statement above, rests on the uniformity audit (review-uniformity, §3.6).
  That audit is a reading of [AN]'s Lean proof terms by one reader, and its central step is a meta-level argument, not a
  Lean theorem.

> **Remark R′ (non-uniform form, refereed fallback).** Without the audit, (a) and (b) hold for an algorithm that also
> receives the advice string G_v of length poly(n), respectively poly(τ).

For H = 272 the bound on δ would be about 0.121, but H is not explicit.

**Scope of (a).** (a) is a statement about the weighted sum of one τ-plain program in [AN]'s model. It needs no
sparsification. In this sense it is deterministic subexponential counting for nondeterministic linear time in that
model. We have not written out a translation to multitape Turing machines with linear overhead. A machine with tapes as
pairs of lists looks routine, but it is [ours] and not refereed. For #3-SAT *measured in the number of variables*, see
§7.4.

### 3.2 Why the stated J.4 is not enough [ours-R]

- J.4 bounds the lister only by τ/v^24 *steps*, and it requires s·v^48 ≤ τ.
- An accepting run may therefore contain up to τ/v^24 ≥ s·v^24 guesses.
- Enumerating the runs costs 2^{≥ s·v^24}. For 3-SAT, s ≥ n, so this is worse than brute force.
- What is missing is a bound on the number of `guess` constructs, as opposed to steps.

### 3.3 The guess-count lemma

> **Lemma 1 (guess count)** [AN-p; ours-R]. In the setting of J.4 with α = 2, every accepting run of the composed lister
> G on an instance z with |z| ≤ s executes at most τ/v^235 `guess` constructs, for all v ≥ v₀ (enlarging v₀ if needed).

**Where it is read from, in the paper.** The proof of J.3 (pp. 53–54), paragraph "The program G", says:
- "On z it writes the word of z and cuts it into K parts … It guesses q, ρ, the numbers of packets and the outcomes,
  each in binary with a fixed number of digits, and it rejects unless ρ is valid … With these it computes by the binary
  operations, in (MN)^{C_tree}Λ steps, the tree, the packets, the heavy nodes and the pieces … It then guesses the
  contents of the cut packets, writes for each piece its script … **All of this is deterministic except for the
  guesses**, and every choice in the formula is guessed exactly once".
- The step account that follows: "The program G takes sΛ steps for the word, (MN)^{C_tree}Λ ≤ τΛ/v^256 steps for the
  plan, and kΛ · τΛ/v^300 steps for the cut packets".
- The list of guessed items matches the sum in Prop. J.2 (p. 52): "over boundary states, valid data ρ …, numbers of
  packets, good outcomes, and the contents of cut packets". Table 2 (p. 52) gives the exponents 300 and 256.

**Where it is read from, in the Lean.** [ours-R, review-theoremR §1; we read the code but did not build it.]
- The one-cut program is `dealProg` (`Nc/Dl/Cut.lean`, l. 55), with body `dealF` (`Nc/Dl/DealThm.lean`, l. 26).
- On this path the only reachable `guess` sites are `pickB` (`NS1/Lists.lean`, l. 316) and `bitsB` (`NS1/Deal.lean`,
  l. 73). They are reached through the DStep kinds `pick` and `bits` (`NS1/DSteps.lean`, l. 69ff.).
- The plan choices are `pickS` phases in steps1–8 (`Nc/Dl/Phases.lean`). The cut-packet contents are `steps9`, one
  `DStep.bits` per present cut unit (`Nc/Dl/Run2.lean`, l. 181).
- The s-dependent phases `wordB` (`NS1/Util.lean`, l. 34) and `partStep` (`NS1/Parts.lean`, l. 22) contain no guess.
  They account for exactly the s-dependent terms of the cost bound `dealB` (`Nc/Dl/Does.lean`, l. 31).
- Composition `compC` (`NS1/Compose.lean`, l. 53) adds no guesses. Along one run of a composition the guesses add as
  g₁ + P₁·g₂.
- The runs of G have weight 1.
- The other `guess` sites in the development belong to the evaluator, the universal evaluator and the accelerator. They
  are summed inside the pieces, not enumerated by G.
- No Lean predicate counts guesses, so Lemma 1 is a reading of the code and the prose. It is not a checked theorem
  (§7.2).

*Proof.* Each `guess` costs one step. So the guesses of one cut are at most the steps of its non-word phases. The word
phase (sΛ steps) is guess-free.

*One cut at level i* (time bound τ_i, k_i ≤ v^64):
- **Plan:** at most (MN)^{C_tree}Λ ≤ τ_iΛ/v^256 guesses. The inequality is the one the J.3 proof states. It uses that
  "all tables of size (MN)^{C_tree} … are smaller than v^{a₀} and than τ/v^256" (p. 53–54).
- **Cut packets:** at most k_iΛ pieces, each with at most KTΛ/v^300 bits of cut packets (Prop. J.2). Here KT ≤ τ_iΛ + K
  and K ≤ τ_i. This gives at most τ_iΛ³/v^236.

  (The rebase notebook wrote Λ² here. The referee's count gives Λ³. Since Λ is "a power of lg v whose exponent may grow
  a bounded number of times" (p. 51), the difference is absorbed. We use Λ³.)
- **Per cut:** g_i ≤ 2τ_iΛ³/v^236.

*Composition* (J.4 proof, p. 55):
- r = O(α) cuts. Lean uses r = 16hα.
- Cut i+1 runs on each of the P_i pieces of time bound τ_i, and "P_iτ_i ≤ τ(4Λ²)^i".
- Guesses add along a run, so

    total ≤ Σ_{i<r} P_i·g_i ≤ 2rΛ³(4Λ²)^r · τ/v^236 ≤ (100Λ³)^{r+1}·τ/v^236 ≤ τ/v^235.

- The last step uses (100Λ³)^{r+1} ≤ v. That is the J.4 proof's "All these powers of Λ are below v if C_cut is large",
  and in Lean the hypothesis discharged via `polylog_loss_le` in `thm_cut`. ∎

**Robustness of the exponent.** Only the form "total guesses ≤ τ/v^{48+g} with g > 0" matters (§3.6).
- 256 and 300 are in the paper. 235 and 236 are our inference.
- Using only the *statement* of J.3, and granting that its s-term is guess-free (which the Lean shows), the per-cut
  guesses are ≤ τkΛ/v^256. This gives g = 143 and δ < 143/(5H+143).

### 3.4 From the guess count to deterministic time

> **Lemma 2** [ours-R, given Lemma 1 and J.4]. Assume contracting over k. Let v ≥ v₀, v^H ≤ τ′ ≤ v^{2H}, and let z be
> τ′-plain with |z|·v^48 ≤ τ′. Given G = G_v of J.4 (with α = 2), sum(z) can be computed deterministically with
> 2^{O(τ′/v^235 + v^H)}·poly(τ′) operations in A.

*Proof.*
1. **Enumerate the run tree of G on z, pruned.** Explore depth-first. Cut off any branch once it exceeds t = τ′/v^24
   steps or g = τ′/v^235 guesses.
   - Every prefix of an accepting run survives (J.4 and Lemma 1), so the pruning loses nothing.
   - We do not need any bound on non-accepting runs. This is the referee's fix: it replaces the notebook's claim that
     *every* run has few guesses.
   - `guess` is the only branching and it is binary (p. 48), so the pruned tree has at most 2^{g+1} leaves.
   - Each construct costs O(1) pointer operations, so the enumeration takes 2^{g+1}·poly(τ′).
2. **Collect the accepting runs.** Each gives a weight w ∈ A (here w = 1) and a list of at most τ′v²/v^H pieces y.
3. **Evaluate the pieces.** Each piece is v^H-plain. Enumerate its run tree cut off at v^H steps (≤ 2^{v^H} leaves),
   and sum the weights of the accepting runs. The cut-off is exact, because runs longer than v^H do not accept.
4. **Output** Σ_runs w·Π_y sum(y). This equals sum(z) by Def. J.1 (Lean: `pv θ z = wsum Q (pvs θ)` in `CutD`). ∎

> **Theorem R(a)** [ours-R]. For τ-plain z with |z| ≤ τ, apply Lemma 2 with τ′ = τ^{(H+235)/(H+187)} and
> v = τ^{1/(H+187)}, up to rounding.

*Check.*
- z is τ′-plain.
- |z|·v^48 ≤ τ·τ^{48/(H+187)} = τ′.
- v^H ≤ τ′ = v^{H+235} ≤ v^{2H}, since H ≥ 272.
- 4 lg τ′ ≤ (lg v)² holds for large v.
- The cost is 2^{O(v^H)} = 2^{O(τ^{H/(H+187)})}.
- Small τ are handled by brute force. ∎

### 3.5 3-SAT, and where characteristic 0 is used [ours-R]

**Sparsification** [cl: Impagliazzo–Paturi–Zane]. We use the sunflower version written out in the proof of [IM]
Thm 7.1. The referee checked its counting.
- Fix 0 < α < 1/4 and r = ⌈n^α⌉.
- In 2^{O(n^{1−α} log n)}·poly time, F becomes a list of at most 2^{O(n^{1−α} log n)} 3-CNFs F_j, each with
  O(n^{1+4α}) clauses, such that F is satisfiable iff some F_j is.
- The branching is **not** disjoint: an assignment may satisfy several leaves. So we use it only for decision, testing
  each leaf separately.

**One leaf.** z_j = (P, ⟨F_j⟩) for a fixed program P.
- P builds, by a loop, a balanced binary tree of depth ⌈log₂ n⌉ whose leaves are guessed bits.
- For each literal, P walks down to the bit of its variable in O(log n) steps.
- P fails on an unsatisfied clause. Otherwise it accepts with weight 1 and an empty tally.
- z_j is τ₀-plain with τ₀ = O(n + m_j log n), and |z_j| = O(m_j log n). Put L = O(n^{1+4α} log n), so that both are at
  most L.
- sum(z_j) = 2^e·#SAT(F_j)·1_A, where e = 2^{⌈log n⌉} − n is the number of padding leaves. In characteristic 0 the
  factor is harmless.
- Alternatively, P can make the padding leaves non-free by failing unless each is 0. This costs O(n) deterministic
  steps and gives e = 0 and sum(z_j) = #SAT(F_j)·1_A. This variant is [ours], not refereed, and it matters only in
  positive characteristic (§9).

**Characteristic 0.**
- By `exists_setting`, A ⊂ k is a finitely generated ℤ-algebra. Since char k = 0, A ⊗ ℚ ≠ 0.
- A maximal ideal of A ⊗ ℚ gives a ring map ψ: A → L into a number field (Zariski's lemma). [AN K.6] uses the same
  device modulo a maximal ideal.
- ψ(1) = 1, so ψ(sum(z_j)) = 2^e·#SAT(F_j) ∈ ℤ. This is positive iff F_j is satisfiable.
- All identities used are identities in A, so they survive ψ.
- The fixed finite table consists of the images under ψ of the named generators θ of A.
- Bit sizes: run weights are products of poly(τ) fixed algebraic numbers, and the sums have 2^{O(τ)} terms. So every
  number has poly(n) bits.

**Exponent.**
- The total is 2^{O(n^{1−α} log n + n^{(1+4α)ρ} polylog n)}·poly, with ρ = H/(H+187).
- Balancing α = 1 − (1+4α)ρ gives α = (1−ρ)/(1+4ρ) = 187/(5H+187), which is < 1/4.
- Hence any δ < 187/(5H+187) works. ∎ (Theorem R(b))

In general, if the total guesses are τ/v^{48+g}, one gets δ < g/(5H+g).

### 3.6 Uniformity: the present status

The algorithm needs G_v for the one scale v determined by n. |G_v| ≤ v^H = poly(n), so the non-uniform form needs no
further argument [ours-R].

For the uniform form [ours-R, review-theoremR §4], `thm_onecut` assembles G from `obtain`ed witnesses. They fall into
two groups.
- **Witnesses with decidable finite specifications.** A fixed machine can find these by search within the time budget:
  - the subgroup chain of `exists_chain`;
  - the words, the injective codes and the bijections χ ↦ χ̂;
  - the SLP tables, once their function is fixed.
- **Witnesses whose specifications contain value identities over all inputs.** These cannot be found by search: the plan
  structure TT from `thm_tree` (H.2) and `pc` in `prop_pieces`. Uniformity needs these constructions to be explicit
  given (v, laws, tower).

The paper's prose says they are:
- H.2: "the groups, the words, the cosets and the maps χ ↦ χ̂ are constants of the program";
- "Packets are assigned … by their number in a fixed order";
- J.3: "rules such as ranks in a fixed enumeration decide which packet goes where".

Neither we nor our referee have checked this in the Lean. Hence the placeholder in Theorem R^u.

---

## 4. Theorem A: contracting implies ports

> **Theorem A** [ours-R, from AN-L and OA-L]. Let k be a field of characteristic χ, and suppose the contracting hypothesis
> holds over k. Then χ admits ports (EG Def. 11.1). More precisely, the following holds for every sufficiently large
> multiple h of the constant u of [AN] F.6. The Cayley graph G_h of U_h(F₂) with generators x_j = 1 + E_{j,j+1}
> (0 ≤ j < h−1) is a single-graph certificate in the sense of [HC] Thm 4.2. The certified family has degree 2(h−1).
>
> **Corollary A′.** If k has characteristic 0, then by [IM] Thm 7.1 there is a uniform deterministic algorithm deciding
> 3-SAT on v variables in 2^{O(v^{1−δ})}·poly.

*Proof.*
1. **[AN F.6, p. 40, `thm_poincare`]** [AN-L]: "There are an integer u ≥ 2 and a real number C₀ ≥ 0 such that for every
   l ≥ 2, h = lu, and every price on U_h, E_{g,a}|a, ga|² ≤ C₀ Σ_{j<h−1} E_a|a, x_j a|²". This is in the contracting
   case over k, with u and C₀ depending only on (μ, s). [AN App. M]: "Sections A to L use nothing about k except that
   it is a field, apart from the element ½ in Proposition E.1." The Lean `thm_poincare` is stated for any `Field K`.
2. **Every finite configuration in X_χ is an [AN] price over k** [ours-R, review-theoremAB §1].
   - On a finite set S, an [EG]-spectral space has metric δ(S)·d_F for a Strassen point F over some field K of
     characteristic χ.
   - Restrict F to tensors over the prime field P.
   - If k ≠ P, lift to k by [EG] Lemma 2.3 ("For k ⊆ K, the possible joint values of spectral points on any family of
     tensors defined over k are the same over the two fields") [OA]. For k = ℚ this step is not needed.
   - Push forward along the placement. This gives c·d_φ for an [AN] spectral point φ over k (§2.1 Remark).
3. **Translation.**
   - x_j is an involution, so G_h is a simple (h−1)-regular graph on n = 2^{h(h−1)/2} vertices.
   - The left side of F.6 is V(x), because (a, ga) is a uniform independent pair. The right side is C₀(h−1)·E_P(x).
   - So V ≤ C₀(h−1)·E_P for every placement into every member of X_χ.
4. **[HC Thm 4.2]** [OA-L]. If X_χ had no ports, then C₀(h−1) ≥ c·log n/log h = c·h(h−1)/(2 log h) (bases absorbed into
   c). This is false once h/log h > 2C₀/c. So X_χ has ports, and by [HC §2.2] χ admits ports. ∎

**Lean form, and the `scalar` hypothesis (referee fix).** If one cites `exists_logarithmic_placement` instead of the
paper's Thm 4.2, two adjustments are needed.
- **Padding.** Pad G_h with holding arcs to degree 2^e, e = ⌈log₂ h⌉. This at most doubles the constant.
- **Constants.** With s = h(h−1)/2, the requirement 2C₀(h−1) < s/(10000(e+3)) holds once h/(log₂h + 4) > 40000·C₀.
- **The `scalar` hypothesis.** The Lean theorem has an extra hypothesis `scalar`: the same Poincaré bound for
  real-valued placements of the padded graph.
  - It holds here because finite subsets of a line are [AN] prices over every field, so F.6 applies to them. This is
    [ours, internal note b2 §3(ii), from AN Prop. C.3 and Lemma C.4(a)]. It also follows from [EG] Thm 1.1 [OA].
  - The paper version needs no such hypothesis, since ℝ ∈ X_χ ([HC §2.3]).
- The order 2^{h(h−1)/2} is a power of 2, and G_h is connected, as `PortZero` requires.

**What Corollary A′ rests on.** [IM] Thm 7.1, hence [HC] Thm 13.1 and [EG] §§12–13. We have not reviewed these. A Lean
counterpart exists: `middle_count_bridge`, with no `sorry` in that directory by grep. We did not build it.

---

## 5. Theorem B: finite objects

> **Theorem B** [ours-R].
> (i) **Sharp form** [AN-p]. For each μ ≥ 3 and each field k: the contracting inequality fails at μ (no s with 1 ≤ s,
> s² < μ works for all prices on Mat_μ(F₂)) **iff** ρ_μ = √rk is an [AN] price on Mat_μ(F₂) over k.
> (ii) If for some μ ≥ 2 the metric ρ_μ is not an [AN] price over ℚ, then the contracting hypothesis holds over ℚ (at
> μ = max(μ, 3)). Hence the conclusions of Theorem R (non-uniform) and of Corollary A′ (uniform) hold.
> (iii) The same holds if the five-point set M5 = {0, I, e₁₁, e₂₂, e₁₁+e₁₂} ⊂ Mat₂(F₂), with the restricted metric, is
> not an [AN] price over ℚ. Its squared distances are 2 on the pairs 0–I, e₁₁–e₂₂ and (e₁₁+e₁₂)–e₂₂, and 1 on the
> other seven pairs.
> (iv) **Contrapositive.** Under Weak ETH (via Theorem A) or nu-Weak ETH (via Theorem R), the metric ρ_μ is an [AN]
> price over every field of characteristic 0, for every μ, and so is M5.

*Proof.*
- **(i) ⇐.** If ρ_μ is a price, then D(r)² = r·D(1)², so D(μ) = √μ·D(1). This exceeds s·D(1) for every s < √μ.
- **(i) ⇒.** This is Steps 2–7 of the proof of D.2 (pp. 30–31).
  - Step 2 uses failure *at this μ only*: "As the contracting hypothesis fails, for every s with 1 ≤ s < √μ there is a
    price on Mat_μ(F₂) with D(μ) > sD(1)".
  - Step 5 needs μ ≥ 3.
  - In Lean, `thm_alt_rank_price` assumes the global ¬Contracting K. But the proof of `thm_alt_extremal` uses it only
    through `hK ⟨μ, √t, …⟩` at the given μ (`Alternative.lean`, l. 306ff.). So the per-μ form is read from the proofs,
    not stated.
- **(ii) and (iii).** Pull-back along an injection preserves prices [AN A.3]. M5 ⊂ Mat₂(F₂): we recomputed the ten
  ranks. And a ↦ diag(a, 0) maps Mat_μ into Mat_{μ′} preserving rk(a − b). So "M5 not a price" ⇒ "ρ₂ not a price" ⇒
  "ρ_{μ′} not a price for all μ′ ≥ 2". By (i) at μ′ = 3, contracting holds over ℚ. Then apply Theorem R(b), or
  Theorem A with [IM] 7.1.
- **(iv)** is the contrapositive. ∎

**Correction to an earlier formulation (referee fix).** Part (iv) asserts that ρ_μ is an *[AN] price*: a limit of
c·d_φ with φ multiplicative and cover-subadditive. It does *not* assert that ρ_μ is the wire metric of a point of
Strassen's asymptotic spectrum. The Strassen-point version would need an unreviewed reading of the proof of [EG]
Lemma 11.3, and we do not claim it.

**"Finite" is not "decidable" (referee fix).** Each object is one metric on 5, 16 or 512 points. But whether it is a
price is an asymptotic question.
- By duality ([AN] Thm A.6), refuting price-ness needs **a family of covers of the tensor powers C^N of the
  ρ_μ-weighted network with exponential saving**. One cheaper cover does not suffice.
- Because prices are defined only up to the scale c, one identity in fixed dimensions constrains d_φ, not the price.
- No finite certificate is known for either side.
- No metric-only inequality valid in all CAT(0) spaces can exclude ρ_μ or M5, because √2·ρ_μ embeds isometrically in
  the Bruhat–Tits building of GL_{2μ}(F₂((t))) [ours, internal note c1 §2; referee-checked]. This leaves open
  conditions that involve non-wire tensors, and [AN]'s crossing inequality B.3, whose CAT(0)-validity is conjectural.

---

## 6. Corollaries, the case table, and the permanent bounds

> **Corollary 1.** Let k be a field of characteristic 0.
> (a) Under Weak ETH, the contracting hypothesis fails over k. This uses Theorem A and [IM] 7.1, hence OpenAI's results,
> but not [EG] Thm 1.2.
> (a′) Under nu-Weak ETH, the same follows from Theorem R alone. With Theorem R^u (placeholder) it would follow under
> Weak ETH from [AN] alone.
> (b) In either case, by `thm_alt` in its proved form ¬Contracting K ⇒ Flat K, the flat hypothesis holds over k, and ρ_μ
> is an [AN] price over k for every μ (Theorem B(iv)).

*Proof.* Contrapositive of Theorem R, respectively Corollary A′, applied to k itself. Both hypotheses are per field
(D.1: "two hypotheses on the field k"), so no transfer between fields is needed. ∎ [ours-R]

Corollary 1 is a conditional proof of [AN]'s flat hypothesis in characteristic 0. It does not use OpenAI's [EG] Thm 1.2
("Over every field there is a spectral flat of every positive finite dimension"), which would give the flat hypothesis
unconditionally via the containment of §2.1. Route (a′) uses no OpenAI result at all. The sparsification it uses is
classical.

**The case table** (one characteristic χ; "contracting" means over some field of characteristic χ). Each label is
attached to the cell it concerns.

| Cell | Possible? | 3-SAT consequence | Permanent / HC bounds that apply |
|---|---|---|---|
| contracting, ports | Not excluded by anything either lab proves [ours-R, review-AB §6]. In char 0 it contradicts Weak ETH. | char 0: 2^{O(v^{1−δ})} decision (Theorem R non-uniform; Cor. A′ uniform) | [AN] K.7: 2^{c(log m)²/log log m}. [HC] 12.2 [OA]: L^{[N]}_F(HC_N) > 2^{N^ε} |
| contracting, no ports | **Impossible** (Theorem A) | — | — |
| not contracting, ports | Not excluded | char 0: 2^{O(v^{1−δ})} decision via [IM] 7.1 only | [AN]: flat-case bound E.11. [HC] 12.2 [OA] |
| not contracting, no ports | Not excluded. In char 0 it is forced by Weak ETH. | none from these sources | [AN] E.11 / Thm 1.1: 2^{c(log m)^{4/3}}. [HC] Thm 1.1 [OA]: exp(c(log N)²/(log log N)²) |

The flat hypothesis is *not* a column of this table:
- [AN] does not show flat and contracting exclusive;
- Euclidean configurations satisfy the contracting inequality (D(μ)²/D(1)² < 2 for Euclidean pull-backs; ours, c1 §4).

**What this says about the two labs' permanent bounds.** Both labs' bounds are unconditional claims, and nothing here
changes them.

- **[AN].** Theorem 1.1 is m^{c(log m)^{1/3}} = 2^{c(log m)^{4/3}}, and it comes from the flat case. The contracting-case
  bound K.7 is 2^{c(log m)²/log log m}. [AN] says "The exponent 1/3 comes from the flat case alone" (p. 59).
  - Under Weak ETH (via OpenAI) or nu-Weak ETH (via [AN] alone), the contracting case does not occur in characteristic
    0. So K.7 then holds vacuously there, and the operative bound is the flat-case one.
  - Conversely, by Theorem A, wherever [AN]'s contracting case occurs, [HC] 12.2 applies too, giving 2^{N^ε}. This is
    much stronger than K.7, but it is conditional on [HC] 12.2.
- **[HC].** The ports branch (12.2) is excluded in characteristic 0 by Weak ETH. OpenAI says so itself ([IM] 7.1). So
  under Weak ETH, [HC] Thm 1.1 rests on its no-ports part.
- **Comparison (referee fix).** [HC] Thm 1.1, exp(c(log N)²/(log log N)²), is weaker than [AN] K.7 by a factor log log
  in the exponent. It is stronger than [AN] Thm 1.1. The measures differ:
  - [HC] bounds the degree-component border size L^{[N]}_F;
  - [AN] bounds exact circuit size, and separately approximate circuits (Thm 1.4).
  So the bounds are comparable in growth but are not bounds on the same quantity.

---

## 7. Dependencies and status

We built neither lab's Lean. "Lean-backed" means a Lean statement exists per the lab, and we read it.

**Imported statements.**

| Statement | Lab, location | Lean-backed | Our check |
|---|---|---|---|
| Def. D.1 (both hypotheses) | AN, p. 30 | `def_cases`, `Contracting`, `Flat` | read |
| Thm D.2, ¬C ⇒ F | AN, pp. 30–31 | `thm_alt` | read the Lean proof term |
| D.2 Steps 2–7 per μ | AN, pp. 30–31 | `thm_alt_rank_price` (global hypothesis) | per-μ use read in `thm_alt_extremal` |
| F.6 Poincaré on U_h | AN, p. 40 | `thm_poincare` | read statement; scalar case consistent with numerics (review-AB §3) |
| G.2 laws; A finitely generated | AN, p. 43 | `exists_laws`, `exists_setting` | read statement |
| J.3, J.4 | AN, pp. 53–55 | `thm_onecut`, `thm_cut` | read statement and proof; Lean structure read for guess sites |
| A.3 pull-backs, A.6 duality | AN | yes (per AN §3) | read statements |
| EG Def. 11.1, Lemma 2.3 | OA EG | `HasWireExpanders`, — | Lemma 2.3 proof read by referee |
| HC Thm 4.2 | OA HC | `exists_logarithmic_placement` (char 0; extra `scalar`) | proof re-read line by line by referee |
| IM Thm 7.1 (⇐ HC 13.1) | OA IM | `middle_count_bridge` | **not reviewed**; only the sparsification part checked |
| HC Thm 1.1, 12.2 | OA HC | 1.1 with this exponent "remains unformalized" per OA docs; 12.2 not checked | quoted only |
| Sparsification | classical; written out in IM §7 | (inside OA Lean) | counting re-checked |
| Zariski's lemma | classical | — | — |

**Our own steps.**

| Step | Refereed? |
|---|---|
| §3.2 (black-box J.4 insufficient) | yes (review-R §2) |
| Lemma 1 (guess count) | yes, as a reading of prose and Lean (review-R §1). Not machine-checked |
| Lemma 2, pruned enumeration | yes, with the pruning fix (review-R §2) |
| Theorem R(a) exponent | yes, recomputed (review-R §2) |
| Theorem R(b): encoding, char 0, δ | yes (review-R §3) |
| Uniformity (Theorem R^u) | **open**: gap per review-R §4; audit pending |
| Turing-machine reading of R(a) | no |
| Theorem A and its Lean side condition | yes (review-AB §§1–3, 9) |
| Theorem B (i)–(iv) | yes, with the AN-price fix (review-AB §5) |
| Corollary 1 | yes (review-R §6; review-AB §9) |
| Case table, bound comparison | yes, with wording fixes (review-AB §7) |

---

## 8. Open points

1. **Uniformity of Theorem R (§3.6).** Either check in the Lean that `thm_tree` and `prop_pieces` build their witnesses
   explicitly from (v, laws, tower), or refactor their `obtain`s into `def`s with those parameters. Until then:
   - Corollary 1(a′) is proved under nu-Weak ETH only;
   - the uniform statement depends on OpenAI's route (a).
   [Audit `review-uniformity.md`: not available at drafting time.]
2. **Machine-checking Lemma 1.** The referee's plan (review-R, final section) is:
   - add a `guesses` field to the run semantics;
   - define a guess-aware `Does` and a predicate `CutDG`;
   - prove guess-freeness of `wordF`, `partsF`, `tmsF` and `compC`;
   - restate `thm_onecut`, the composition lemma and `thm_cut` with g ≤ τ/v^235;
   - prove Lemma 2 for an explicit pruned evaluator.
3. **[IM] 7.1 / [HC] 13.1.** These are needed for the uniform route, and we have not reviewed them.
4. **Counting in the number of variables.** Theorem R(a) counts for a single plain instance. #3-SAT in 2^{O(n^{1−δ})}
   would need a count-preserving sparsification. Two candidates are Dell–Husfeldt–Marx–Taslaman–Wahlén (2014) and
   branching with the negated centre added as unit clauses. Not refereed; not claimed.
5. **Positive characteristic.** Theorem R(a) holds over any field where contracting holds: it computes sum(z) in a
   finite field A/𝔪. But this does not yet give a statement about 3-SAT.
   - The sparsification is not disjoint, so leaf counts mod p do not combine.
   - In characteristic 2 the factor 2^e in our encoding is a normalisation problem that is still open.
   - A separate note (in preparation, **unreviewed**) proposes that ports or contracting in characteristic p ⇒
     one-sided-error randomised 3-SAT in 2^{O(v^{1−δ})}, via Valiant–Vazirani isolation with a Toeplitz hash. We state
     nothing for p = 2, and no theorem for p > 2.
6. **Omitted.** We omit a corollary about the optimality of our own decomposition engine under Weak ETH ("Corollary 2"
   of the working notes). It rests on internal results that were not checked, and we do not claim it. Likewise, the
   working notes' statement that the ports algorithm "obeys all flat floors" is heuristic. It is not a theorem, and it is
   not used here.
7. **Explicit constants.** H, u, C₀ and the laws are not explicit. δ is not explicit either.
