# Referee report on "Theorem R" (rebase/notebook.md)

Referee pass, 26 Nov 2026. The source is the Anthropic paper "VP ≠ VNP over every field". Line numbers "l." refer to
`scratchpad/fm/paper.txt`. Lean paths are relative to `scratchpad/fm/repo/vp-vnp`. I read the paper's text for
§§H.1–K.4 and the relevant Lean files. No code was run.

## Summary verdict

**No fatal gap found. Theorem R survives, with fixes.** Ranked from weakest point to strongest:

| # | Item | Verdict |
|---|---|---|
| 4 | Uniformity (one fixed algorithm) | **Gap (unverified, plausible).** The non-uniform version is solid. |
| 1 | Lemma 1 (guess count) | **Correct with fix.** Confirmed against the Lean program's structure as well as the text. |
| 2 | Guess count ⇒ deterministic time; Theorem 1 | **Correct with fix** (run-tree pruning; bit sizes). |
| 3 | 3-SAT encoding, char 0, Nullstellensatz | **Correct.** |
| 6 | Corollaries | **Corollary 1 correct** (plain ETH suffices). Corollary 2 was not checked: it rests on external results. |
| 5 | Sanity | **No contradiction found.** The consequence is stronger than stated (see 5). |

---

## 4 (weakest). Uniformity — gap, not verified

**Claim (notebook §2.4).** v ↦ G_v is computable in poly(v) time from a fixed finite table.

**What the Lean does.** `thm_onecut` (Paper/Cuts.lean:101ff.) assembles G from the following witnesses.
- `prop_universal` and `prop_pieces` (Paper/Pieces.lean:653). Inside, `obtain ⟨TT⟩ := htree …`, i.e. `thm_tree` (H.2),
  supplies the plan/tree structure TT as a `Nonempty` witness.
- `pc` (`obtain ⟨pc⟩ := hP T k …`), whose fields include `pc.value`, the sum formula for every z.
- `exists_codes`, `exists_bits` (Nc/Dl/Inst.lean), and the SLP tables from `TT.computed` (Pieces.lean:449).
- The evaluators GR, chosen by `choose` for finitely many symbol codes.

**What ∃-elimination gives for free.** Lean proofs are parametric in an `obtain`ed witness. So any object that
satisfies the same spec works. Several witnesses have decidable, finite specs, and a fixed machine can find them by
search in time poly(v) or 2^{poly(v)}, which is within budget:
- the subgroup chain (`exists_chain`);
- the words;
- the injective codes;
- the bijections χ ↦ χ̂;
- the SLP tables, once the function they compute is fixed.

The notebook's chain construction is right: N(Γ_i)/Γ_i is a nontrivial 2-group, so it has an element x with
x ∉ Γ_i and x² ∈ Γ_i. Take index-2 steps and keep every h(h−1)/2-th term.

**What is not free.** The specs of TT (`thm_tree`) and `pc` contain the value identities: for all networks, node
tensors, or instances z. These cannot be checked by search. Uniformity therefore needs the *construction* inside
`thm_tree` and `prop_pieces` to be explicit given (v, laws, tower). The paper's text says that it is:
- H.2 proof, l.2781–2782: "the groups, the words, the cosets and the maps χ ↦ χ̂ are constants of the program";
- l.2785: "Packets are assigned to batches, slots and channels by their number in a fixed order";
- J.3, l.3135–3136: "rules such as ranks in a fixed enumeration decide which packet goes where".

Neither the notebook nor I checked this in the Lean proof of `thm_tree`.

**Fallback (solid).** G_v depends only on v, and v depends only on the input scale. Without constructivity, the
algorithm becomes a fixed machine with advice |G_v| ≤ v^H = poly(n). The result is then 3-SAT ∈
DTIME(2^{n^{1−δ}})/poly, which still contradicts non-uniform ETH. So:
- "Weak ETH ⇒ ¬contracting" is proved modulo the explicitness of `thm_tree`/`prop_pieces`;
- "non-uniform Weak ETH ⇒ ¬contracting" is proved outright, given Lemma 1.

The notebook's sentence "That is enough to contradict Weak ETH, which says that *no* such algorithm exists" is right
only once explicitness is checked. It should say so.

---

## 1. Lemma 1 — correct with fix

### Where the lister guesses: text (J.3 proof, l.3130–3143)

> "It guesses 𝑞, 𝜌, the numbers of packets and the outcomes, each in binary with a fixed number of digits, and it
> rejects unless 𝜌 is valid, the numbers give every node at most 𝑁 packets, and all outcomes are good. With these it
> computes by the binary operations, in (𝑀𝑁)^{C_tree}Λ steps, the tree, the packets, the heavy nodes and the pieces […]
> It then guesses the contents of the cut packets, writes for each piece its script […] All of this is deterministic
> except for the guesses, and every choice in the formula is guessed exactly once" (l.3131–3138)

> "The program 𝐺 takes 𝑠Λ steps for the word, (𝑀𝑁)^{C_tree}Λ ≤ 𝜏Λ/𝑣^256 steps for the plan, and 𝑘Λ · 𝜏Λ/𝑣^300 steps for
> the cut packets" (l.3141–3142)

The list of choices matches the formula of J.2 (l.3031–3033): "sum, over boundary states, valid data 𝜌 as in Lemma I.2,
numbers of packets, good outcomes, and the contents of cut packets". It also matches the choices o of H.2 (l.2634).

Other sources of nondeterminism live elsewhere and are not part of G:
- the guesses of the universal automaton (I.1, l.2898ff.) are letters inside blocks;
- the guesses of the evaluator (l.3113–3120) concern inner packets, letters, indices and summands of A-entries.

Both are summed inside the pieces.

### Where the lister guesses: Lean (stronger than the notebook's reading)

The one-cut G is `dealProg` (Nc/Dl/Cut.lean:55):

    dealF t0 t1 names nl nub sts sts' ts =
      lett (dstepsF nub sts (partsF names nl (wordF t0 t1 .id))) (lett (dstepsF nub sts' .id) (tmsF ts .id))

(Nc/Dl/DealThm.lean:26), with `sts = steps18` and `sts' = steps9`.

- **Only two guess sites.** The `guess` constructs reachable from it are `pickB` (NS1/Lists.lean:316, a unary walk
  over a list with one binary guess per element) and `bitsB` (NS1/Deal.lean:73, one guess per bit). They are reached
  only through the DStep kinds `pick` and `bits`: `dstepF`, NS1/DSteps.lean:69ff.
- **Plan phase.** The plan choices q, ρ, n, o are `pickS` phases in steps1–8 (Nc/Dl/Phases.lean, `phase_picks`).
- **Cut-packet phase.** The cut-packet contents are
  `steps9 = Uid.toList.map fun id => DStep.bits (C.nm (.cut id)) (C.nm (.cont id))` (Nc/Dl/Run2.lean:181). This
  guesses ub bits for each cut unit that is present.
- **The s-dependent part is guess-free.** `wordB` (NS1/Util.lean:34) and `partStep` (NS1/Parts.lean:22) contain no
  guess. They account exactly for the s-dependent terms of the cost bound,
  `dealB = 60s + (s+K)(60Lc+100) + K(60Lc+130) + nS(stepB Lc X + 30) + (X(90Lc+230) + bd((ub+1)(60Lc+100))) + mm(tmB′+60) + 300`
  (Nc/Dl/Does.lean:31). The other terms are independent of s.
- **Coverage of the check.** Grep for `.guess` over NS1 and Nc/Dl finds no other site on this path. Other sites (Nc/Grp,
  Nc/Uni, Nc/Acc, NS1/Eval, `WE.fm`, `gbit`) belong to the evaluator, the universal evaluator and the accelerator.
- **Run weights.** Every run of G has weight 1, since pickB and bitsB yield weight 1.
- **Composition.** `compC G G′ = lett (app G .id) (foldF (stepC G′) (.quote .nil) .id)` (NS1/Compose.lean:53) adds no
  guesses. Its CutD bound is `t₁ + P₁(t₂ + 62P₂ + 110) + 100` (l.91), so guesses add along a run: g₁ + P₁·g₂.

So the guesses of one cut are bounded by the s-independent part of the step bound. This is a statement that could be
read off the Lean program, not only off the prose.

### Recomputed bound

**Per cut at level i** (time τ_i, k_i ≤ v^64):
- plan: g ≤ (MN)^{C_tree}Λ = v^{O(1)}. This is independent of τ_i and s_i. Since τ_i ≥ v^H ≥ v^{a₀+16}, it is
  ≤ τ_iΛ/v^256 (l.3098: "all tables of size (MN)^{C_tree} … are smaller than v^{a₀} and than τ/v^256").
- cut packets: ≤ (k_iΛ pieces) × (KTΛ/v^300 bits each, l.3034), with KT ≤ τ_iΛ + K. This gives ≤ τ_iΛ³/v^236.
- per cut, g_i ≤ 2τ_iΛ³/v^236. The notebook writes Λ²; Λ is "a power of lg v whose exponent may grow a bounded number
  of times" (l.2984), so this is harmless.

**Composition** (J.4 proof, l.3159–3163: "P_iτ_i ≤ τ(4Λ²)^i", "r = O(α) cuts"):

  total ≤ Σ_{i<r} P_i g_i ≤ 2rΛ³(4Λ²)^r · τ/v^236 ≤ τ/v^235,

using (100Λ³)^{r+1} ≤ v. That inequality is `hX` in Lean `thm_cut`, Paper/Cuts.lean, via `polylog_loss_le`. Lean uses
r = 16hα.

### Per run or summed?

Per run. The bound is per run because guesses add along one run of the composition. "Every run" is stronger than
needed, and on failing runs it relies on the invalid-plan checks coming first. Fix: enumerate the run tree with pruning
at g guesses and t steps. Prefixes of accepting runs survive, so this is exact, and it uses only the bound for
accepting runs.

### Exponents

- 256 and 300 are in the text: Table 2, l.2990–2993, and the J.3 proof.
- 235 and 236 are inferred by the notebook.
- 235 is not load-bearing. Any total of the form τ/v^{48+g}, with g > 0, gives ρ = H/(H+g). The coarse bound read
  from the *statement* of J.3, per-cut guesses ≤ τkΛ/v^256 (granted that the s-term is deterministic), gives
  τ/v^{191} and ρ = H/(H+143).

### Asserted versus assumed

- The paper asserts the program's structure and step accounts. The formalization note to J.3 (l.3085–3087) says: "The
  proof describes the evaluator and the cutting program 𝐺 but does not print them".
- The Lean prints the program. No Lean predicate tracks guesses: CutD tracks steps only (NS1/Compose.lean:25).
- So Lemma 1 is a reading, not a theorem. The reading now covers the Lean code as well as the prose.

---

## 2. From guess count to deterministic time — correct with fix

### Guess alphabet and enumeration
- `guess` is binary: "two runs, with outputs nil and (nil, nil)" (l.2813).
- pickB is a binary walk.
- So a run tree with ≤ g guesses and ≤ t steps per path has ≤ 2^{g+1} paths, which a DFS enumerates in O(2^g·t)
  pointer operations.
- Cancellation of weights is irrelevant: every run is enumerated.

### The identity is exactly J.1/CutD
Lean: `pv θ z = wsum Q (pvs θ)`, and `Does` equates the run list's weighted sum with wsum (NS1/Comp.lean:69).

### Pieces
- Pieces are v^H-plain, so their accepting runs take ≤ v^H steps, and truncating at v^H is exact.
- Cost: ≤ 2^{v^H}·v^H per piece and ≤ τv²/v^H pieces per run.
- The only constructs are those of l.2807–2815, so the simulation has O(1) overhead per construct (construct number
  found by ≤ 11 loads, l.2874–2875).

### Bit sizes
- After ψ: A → L (number field), every piece-run weight is a product of ≤ v^H fixed algebraic numbers: O(v^H) bits.
- Sums of 2^{v^H} terms add O(v^H) bits.
- Products of ≤ τv² piece values give poly(τ) bits.
- Sums over 2^{τ/v^235} runs add O(τ) bits.
- G's runs have weight 1.
- Total: poly(τ) bits per number. The notebook's statement is fine.

### The regime s·v^48 ≤ τ is respected
Theorem 1 pads the time bound. A τ-plain z is τ′-plain for every τ′ ≥ τ.
- Take τ′ = τ^{(H+235)/(H+187)} and v = τ′^{1/(H+235)}.
- Then |z|·v^48 ≤ τ·τ^{48/(H+187)} = τ′.
- v^H ≤ τ′ = v^{H+235} ≤ v^{2H}, since H ≥ 272 ≥ 235. Rounding costs a constant factor.
- The J.3 condition 4 lg τ ≤ (lg v)² holds for large v.
- Cost: 2^{O(τ′/v^235 + v^H)} = 2^{O(v^H)} = 2^{O(τ^{H/(H+187)})}. Recomputed and correct.

### δ
- Exponent: O(n^{1−α} log n + n^{(1+4α)ρ} polylog n), with ρ = H/(H+g) and g = 187.
- Balancing α = 1 − (1+4α)ρ gives α = (1−ρ)/(1+4ρ) = g/(5H+g).
- So δ < 187/(5H+187), which is 0.1209 at H = 272. The required α < 1/4 holds (3g < 5H). **Confirmed.**
- In general, δ < g/((1+c)H + g), with c the clause-density exponent of the sparsification.

### The notebook's §2.1 (black-box J.4 is useless) is correct
The J.4 step bound τ/v^24 is at least s·v^24 (l.3152–3153).

---

## 3. The 3-SAT encoding — correct

- **τ-plain.** P is τ₀-plain with τ₀ = O(n + m log n): all runs halt, the tally is empty, and there is no `use`.
- **The sum counts assignments.** Accepting runs correspond bijectively to guess strings satisfying the check, with
  weight 1. So sum = 2^e·#SAT(F_j)·1_A.
- **Sparsification checked.** I checked OA IM §7.1 (`survey/oa/preprints/…integer-multiplication…/paper.txt`,
  l.1701–1749). It gives "at most 2^{O((v/r) log v)} leaves" and "O(vR²) clauses", with R = r² and r = ⌈v^α⌉, i.e.
  O(v^{1+4α}). Its own balancing is "δ < min{α, 1 − (1+4α)(1 − η)}". The CIP06 version (c(k, ε) = (k/ε)^{3k}) would
  give exponent 1+9α. That still gives δ > 0.
- **Characteristic 0.**
  - Lean `exists_setting` gives `A : Subring K` with `Algebra.FiniteType ℤ A` (Paper/Cuts.lean:570).
  - With char K = 0, ℤ ↪ A. A⊗ℚ is a nonzero f.g. ℚ-algebra, so a maximal ideal gives ψ: A → L with [L:ℚ] < ∞
    (Zariski).
  - ψ need not be injective. One only needs ψ(sum(z)) = N, which holds since ψ(1) = 1.
- **The finite table.** The constants are the images of the finitely many named generators θ in L. This is a finite
  table independent of n: non-explicit but uniform. In char p, A/𝔪 is finite and gives N mod p (Corollary 1′ is
  correct).

---

## 5. Sanity — no contradiction, and the consequence is stronger than stated

- **K.6** (l.3359–3361: "no nonzero commutative 𝐴-algebra has an accelerator of size 𝑣^𝑎 at scale 𝑣").
  - An accelerator is a weighted nondeterministic program that is faster in steps (v^H → v^{H−16}).
  - The algorithm of Theorem 1 is deterministic with 2^{τ^ρ} steps, so it is not an accelerator.
  - The diagonal of K.6 needs D to run in fewer steps than the program diagonalized. A τ-step program cannot simulate a
    2^{τ^ρ}-step algorithm. No conflict.
- **Where contracting is used.** Only through the laws: `exists_laws hK` in `exists_setting`, i.e. G.2 via F.6. In the
  flat case there are no laws, so the argument does not run. Nothing false follows.
- **Paper remarks.** "say nothing about whether NP-complete problems have fast algorithms" (l.182–183) concerns the
  paper's unconditional theorems. It is consistent with the theorem.
- **Strength of the consequence.** Theorem 1 gives deterministic 2^{O(τ^ρ)} evaluation of sums over τ-step weighted
  nondeterministic runs with |z| ≤ τ. That is #-counting for nondeterministic linear time in subexponential time. It
  implies, for example, #CircuitSAT for circuits of size n^{1+ε} in 2^{n^{(1+ε)ρ}} time. Through Williams-type
  connections, this would give new circuit lower bounds. None of this contradicts a known theorem; it is a much
  stronger consequence than 3-SAT alone. Iterating Theorem 1 on the pieces improves ρ toward the fixed point
  1 − 187/H, not toward 0. That is also not paradoxical.

---

## 6. Corollaries

- **Corollary 1(i): correct.** The hypothesis needed is the one in IM §1 l.33–35: "for no fixed 0 < δ < 1 can a
  deterministic algorithm decide 3-SAT on v variables in time 2^{O(v^{1−δ})} times a polynomial in the input length".
  Ordinary ETH implies it, deterministic or randomized. The field bookkeeping is per field, as Def. D.1 says ("two
  hypotheses on the field k", l.1691).
- **Corollary 1(ii): correct.** Lean `thm_alt` is `by_cases hK : Contracting K; … exact Or.inl fun … =>
  thm_alt_euclidean hK …` (Paper/Alternative.lean:921ff.), i.e. ¬Contracting K ⇒ Flat K. The text agrees: "We assume
  that the contracting hypothesis fails and derive the flat one" (l.1710).
- **Corollary 1(iii): consistent with D.3** (l.1787–1789: the price √rk(a−a′) "of the proof above").
- **Uniformity caveat.** Under the caveat of item 4, Corollary 1 is proved under *non-uniform* Weak ETH. It is proved
  under uniform Weak ETH once the explicitness of `thm_tree`/`prop_pieces` is checked.
- **Corollary 2: not checked.** It depends on `review-link` and the flat-floor theorem, which are outside this
  material.
- **Labels.** The notebook's labels K.6 and K.7 are theorem numbers. The subsections are numbered K.1–K.5, so there is
  no inconsistency.

---

## What it would take to machine-check Lemma 1 in Lean

1. **Count guesses in the semantics.** Extend the run record of `Ev` (NS1/Machine.lean; `Ev.guess` at l.243 produces
   `.det 1 …`) with a field `guesses : ℕ`. It increments at `Ev.guess` and adds through `ite`, `cons`, `run` and
   `lett`, as `cost` does. Alternatively, define it as a function of the run.
2. **A guess-aware `Does`.** Define `DoesG θ F x Q c g` = `Does` plus `∀ r ∈ l, r.guesses ≤ g`, with the lemmas
   `mono`, `app`, `ite`, `either` and `bindW`. Optionally also bound non-accepting branches; the pruning argument makes
   this unnecessary.
3. **Guess-free helpers.** Prove `Gives`-level determinism, `guesses = 0`, for `wordF`, `partsF`, `getF`/`setF`,
   `foldF`/`mapF` with guess-free bodies, `tmsF` and `stepC`.
4. **DStep guess costs.** Prove `DStep.guessCost`: `pick` ≤ the number of options, `bits` = m when the guard is
   nonempty, `op` = `check` = 0. Then prove `dstepsF_does` with guesses ≤ Σ guessCost.
5. **`CutDG`.** Define `CutDG θ τ s τ′ s′ P t g G` = `CutD` plus every listed run having ≤ g guesses.
   - Restate `thm_onecut_program` with g = nS·X + mm·bd·ub, i.e. the s-free part of `dealB`.
   - Restate `thm_onecut` with g ≤ τΛ/v^256 + kΛ·KTΛ/v^300.
   - Composition (`thm_cut_compose`): g = g₁ + P₁·g₂.
   - `thm_cut_iterate` / `thm_cut`: g ≤ τ/v^235.
6. **Deterministic evaluation.** Prove Lemma 2 as a statement about an explicit evaluator. For example, define
   `wsum` via enumeration of a run tree pruned at (t, g). Prove that it equals `pv` on plain instances.

**Uniformity.** Showing that the witness of `thm_tree` and `pc` depends only on (v, laws, a chain satisfying
`exists_chain`'s spec, codes) can be done by refactoring the `obtain`s into `def`s that take those as parameters.
