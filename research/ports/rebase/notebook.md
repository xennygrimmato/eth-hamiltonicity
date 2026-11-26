# rebase: contracting ⇒ fast 3-SAT, using only Anthropic's paper

Executor **rebase**, 26 Nov 2026. Tags: [K] quoted, with a pointer; [R] proved here; [R-p] proved here from the
*printed proof* of a cited statement (not from the statement itself, and not checked in Lean); [C] conjecture.

Sources:
- AN = Anthropic, "VP ≠ VNP over every field". I used the paper.pdf of github.com/anthropics/formal-math/tree/main/vp-vnp.
  The pdftotext copy is at `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/fm/paper.txt`, and
  line numbers "l.NNNN" below refer to that file. The sparse clone, with the Lean, is at `…/scratchpad/fm/repo/vp-vnp`.
- Strategist notes: `research/ports/ideas-ports.md` §0, Part 1, Part 2 (§2.5 is the sketch checked here).
- `research/vpvnp/c1/notebook.md` and `research/next/review-link.md`.

## Verdict

**The claimed implication holds, but not in the form the strategist sketched.**

- **Theorem R (below).** If the contracting hypothesis holds over some field k of characteristic 0, then for some δ > 0 a
  deterministic algorithm decides 3-SAT on n variables in 2^{O(n^{1−δ})}·poly(input length) bit operations.
  - Any δ < 187/(5H+187) works, where H ≥ 272 is the constant of AN Thm J.4. H is not explicit.
  - The algorithm is uniform: one fixed algorithm, with a fixed finite table of constants (the laws) that is known to exist
    but is not explicit.
- **Inputs used.** AN §§F–J, plus two classical facts: sunflower sparsification [IPZ01] and the Nullstellensatz.
  Nothing from OpenAI is used.
- **What the black-box statement of J.4 cannot give.** J.4 requires s·v⁴⁸ ≤ τ, with s the input size, and bounds the
  lister only by "τ/v²⁴ steps". So any use of J.4 as stated takes at least s·v²⁴ steps. Enumerating the runs then costs
  2^{≥ s·v²⁴}, and for 3-SAT s ≥ n, so this is worse than brute force. The strategist's "2^{O(τ^{1−12/H})}" is right as a
  function of τ, but τ ≥ v⁴⁸·n makes it useless.
- **The fix.** The printed proof of J.3 shows that the cutting program's steps are almost all *deterministic*, such as
  writing out the input. Its *guesses* number at most about τ/v²³⁵. That refinement [R-p] closes the gap.
- **Caveats on reliability.**
  - The refinement is not part of any statement of the paper or of the Lean (`CutD` in `NS1/Compose.lean` tracks steps
    only).
  - The paper's formalization note on J.3 says the program "is described but not printed".
  - Uniformity of the lister likewise comes from reading H.1–H.2 and J.3. The Lean `thm_cut` states only ∃ G.
  - The paper says of itself: "No human mathematician has checked the proofs" (l.580).
- **Corollaries.**
  1. Under variable-count Weak ETH, the contracting hypothesis fails over every field of characteristic 0. Hence (thm_alt;
     in Lean ¬Contracting K ⇒ Flat K) the flat hypothesis holds over every field of characteristic 0.
  2. Under Weak ETH, the flat floors of our engine (1/√2 per merge for two merges) are unbeatable in characteristic 0.
  3. In characteristic p, the same proof gives #3-SAT mod p, not a decision algorithm.

---

## Task 1. What in the contracting case is unconditional

### 1.1 The paper's own division

[K, AN §2.4, l.482–486, verbatim]:

> "Here the argument is indirect. Steps 1 to 4 prove, with no circuit and no permanent, that every computation of a
> nondeterministic program with weighted runs can be cut into short pieces, which a fast program lists. In Step 5 a small
> circuit for the permanent would speed up the sum over the runs of every short piece, hence all such computations, and a
> diagonal argument refutes this."

[K, AN §F header, l.2150]: "In this section and in Sections G to K we are in the contracting case, and we fix μ and s as in
Definition D.1."

So every statement of §§F–K assumes contracting over k. Which ones also assume a circuit:

| Statement | Hypotheses besides "contracting over k" | Circuit for PERM? |
|---|---|---|
| F.6 thm_poincare: ∃ u ≥ 2, C₀: for h = lu, l ≥ 2, every price on U_h has E_{g,a}\|a,ga\|² ≤ C₀ Σ_{j<h−1} E_a\|a,x_j a\|² | none | no |
| G.2 thm_laws: ∃ f.g. subring A ⊂ k, a₁, finitely many laws on U_h over A with (a), (b) | h fixed by (G.1) | no |
| H.1 tower, H.2 decomposition into tree networks | none (H.1 needs no hypothesis at all) | no |
| I.1 universal tape automaton, I.2 runs as networks | none (I is hypothesis-free; uses A only as weights) | no |
| J.2 pieces, J.3 one cut, **J.4 cuts at all scales** | none | **no** |
| K.2 lem_lowdeg | a circuit for *some* polynomial; no contracting needed | (any circuit) |
| K.3 lem_circuit (accelerator from a circuit) | circuit for PERM_m with ≤ v^a gates | **yes** |
| K.4 postponing; K.5 transfer to next scale | K.5 *assumes* an accelerator D (an implication) | no |
| **K.6 thm_noacc: no small accelerators** | none | **no** (an unconditional theorem in the contracting case) |
| K.7 thm_contracting (2^{c(log m)²/log log m}) | combines K.3 and K.6 | yes, as the hypothesis of the contradiction |

So the "cutting" half (F→J) and the "no accelerators" theorem (K.6) are unconditional consequences of contracting. Only the
step "circuit ⇒ accelerator" (K.3) and its use in K.7 involve the permanent.

### 1.2 Thm J.4 verbatim, with all hypotheses

[K, AN l.3148–3153]:

> "**Theorem J.4 (cuts at all scales).** There are a multiple H ≥ 272 of 16 and constants C_cut, v₀ such that the
> following holds whenever v ≥ v₀ and α satisfy (lg v)^{C_cut α} ≤ v. For all τ and s with v^H ≤ τ ≤ v^{Hα} and
> s v⁴⁸ ≤ τ, some program of size at most v^H cuts (τ, s) into (v^H, v^{H−32}) with at most τ v²/v^H pieces in at most
> τ/v²⁴ steps."

The standing hypotheses are: contracting over k with fixed (μ, s); the ring A and the laws of G.2; h chosen by (G.1).

"Cuts" is Def. J.1 [K, l.3008–3016]:

> "A program G cuts (τ, s) into (τ′, s′) with P pieces in t steps if the following holds for every instance z with |z| ≤ s.
> • All runs of G on z halt. The accepting ones take at most t steps, have empty tallies, and output lists of at most P
> instances of size at most s′.
> • If z is τ-plain, then all these instances are τ′-plain, and sum(z) = Σ_{runs} weight · Π_{y in the list} sum(y),
> where the sum is over the accepting runs of G on z."

The Lean form [K, `Paper/Cuts.lean` `thm_cut`] is
`∃ H C₀ v₀, 272 ≤ H ∧ 16 ∣ H ∧ ∀ v ≥ v₀, ∀ α τ s, lg v^(C₀α) ≤ v → v^H ≤ τ → τ ≤ v^(Hα) → s·v^48 ≤ τ → ∃ G : Tree,
G.size ≤ v^H ∧ CutD θ τ s (v^H) (v^(H−32)) (τv²/v^H) (τ/v^24) G`.
`exists_setting` gives the setting for any `Field K` with `Contracting K`.

### 1.3 The model and the problem

- **The model** [K, §I.1, l.2802–2834]. Data are binary trees. A program is a term in the constructs
  {fixed tree, argument, first, second, pair, if, run, guess, fail, weight, use}.
  - Each construct costs one step.
  - `guess` is the only branching: it gives two runs.
  - `weight p` multiplies the run's weight by a named generator of A.
  - `use` appends a name to the tally; it is used only in §K.
  - An instance z = (program, argument). It is *τ-plain* if all runs halt and every accepting run has an empty tally and
    costs ≤ τ.
  - sum(z) ∈ A is the sum of the weights of the accepting runs.
  - So the model is **a nondeterministic pointer/λ-style machine with ring-weighted runs**. It is not a Turing machine, not
    an arithmetic circuit, and not a tensor-network contraction. Tensor networks appear only inside the proof (I.2, H.2).
- **The problem.** J.4 is about sum(z) for an arbitrary plain instance: "sums over weighted runs of nondeterministic
  programs". The polynomial Φ of (2.2) enters only in K.3, where its circuit is turned into an accelerator. J.4 itself does
  not mention Φ.
- **What J.4 gives.** It is not an algorithm for sum(z). It gives a *nondeterministic program* G (the lister) of size ≤ v^H
  whose runs list pieces, together with the identity sum(z) = Σ_runs weight·Π sum(pieces). The only time bound is on the
  *steps* of accepting runs of G.
- **Uniformity, as stated.** Existential per v ("some program"; Lean `∃ G : Tree`). See 2.4 for why it is in fact
  uniformly constructible.

---

## Task 2. The 3-SAT consequence

### 2.1 Why J.4 as a black box is not enough [R]

Let z have size s, and let D be any deterministic procedure that computes the right-hand side of Def. J.1 by enumerating
the runs of G and evaluating each piece by brute force.

- From the statement alone, an accepting run of G can make up to t = τ/v²⁴ guesses, so D may have to visit 2^{τ/v²⁴}
  runs.
- J.4 needs τ ≥ s·v⁴⁸. Hence τ/v²⁴ ≥ s·v²⁴.
- For 3-SAT, s ≥ n (the formula must be read). So the bound is 2^{≥ n·v²⁴}, worse than 2^n.
- No padding helps: padding τ only raises τ/v²⁴. The input cannot be shortened either, because z must contain the formula.
- The same holds for J.3, whose step bound (s + τk/v²⁵⁶)Λ also contains s.

**So "Thm J.4 alone gives sums over τ-step runs in 2^{O(τ^{1−12/H})}" is true only for instances whose input is
v⁴⁸ times shorter than their running time.** That is the regime of §K, where inputs have size v′^{H−32} against times
v′^H. It is not the regime of SAT.

### 2.2 The refinement: G guesses little [R-p, from the proofs of J.3 and J.4]

**Lemma 1 (guess count).** In the setting of J.4, with α = 2, every run of the composed lister G on an instance z with
|z| ≤ s executes at most τ/v²³⁵ `guess` constructs (for v ≥ v₀ large).

*Proof, from the printed proof of J.3* (l.3130–3143; "All of this is deterministic except for the guesses").

One cut by k (2 ≤ k ≤ v⁶⁴) on an instance with time bound τ does the following.
- **Deterministic work.** It writes the word of z and cuts it into K parts (sΛ steps). With the plan it computes the tree,
  the packets, the heavy nodes and the pieces, by a fixed straight-line program of (MN)^{C_tree}Λ steps. It then writes
  the scripts.
- **Guesses.**
  - q, ρ, the numbers of packets and the outcomes, "each in binary with a fixed number of digits". These are at most
    (MN)^{C_tree}Λ ≤ τΛ/v²⁵⁶ bits; the inequality is the one stated in the proof ("(MN)^{C_tree}Λ ≤ τΛ/v²⁵⁶ steps for the
    plan").
  - The contents of the cut packets: at most kΛ pieces × KTΛ/v³⁰⁰ bits each, i.e. "kΛ · τΛ/v³⁰⁰ steps for the cut packets".
- The guessed items have fixed digit lengths. Invalid choices are rejected before the cut-packet contents are guessed. So
  the bound holds on *every* run, not only on accepting ones.
- Per cut the guesses are therefore g(τ) ≤ τΛ/v²⁵⁶ + v⁶⁴·τΛ²/v³⁰⁰ ≤ 2τΛ²/v²³⁶.

In J.4 the cuts are composed: cut i+1 runs on each of the P_i pieces of time bound τ_i. The proof of J.4 (l.3159–3166)
gives P_iτ_i ≤ τ(4Λ²)^i and r = O(α) cuts, with every (cΛ^c)^{r+1} ≤ v once C_cut is large (Lean: `polylog_loss_le`).
Guesses add along a run of the composition, so

  total guesses ≤ Σ_{i<r} P_i · 2τ_iΛ²/v²³⁶ ≤ 2rτ(4Λ²)^rΛ²/v²³⁶ ≤ τ/v²³⁵. ∎

**Lemma 2 (deterministic evaluation)** [R, given Lemma 1 and J.4]. Assume contracting over k. Then there are H, v₀ and a
deterministic algorithm with the following property. Let v ≥ v₀, v^H ≤ τ ≤ v^{2H}, and let z be τ-plain with |z|·v⁴⁸ ≤ τ.
The algorithm computes sum(z) ∈ A using 2^{O(τ/v²³⁵ + v^H)}·poly(τ) ring operations.

*Proof.*
1. Construct G (2.4).
2. Explore the run tree of G on z depth-first, cut off at τ/v²⁴ steps. Every run halts, and by Lemma 1 the tree has at
   most 2^{τ/v²³⁵} leaves. Each run is simulated with O(1) pointer operations per construct, so a run costs poly(τ).
3. For each accepting run, read its weight w ∈ A and its list of P ≤ τv²/v^H pieces y.
4. Each piece y is v^H-plain, so its accepting runs cost ≤ v^H. Enumerate its run tree cut off at v^H steps: at most
   2^{v^H} leaves, each poly(v^H). Sum the weights to get sum(y). (Any run longer than v^H is not accepting, so the
   cut-off is exact.)
5. Output Σ_runs w·Π_y sum(y). This equals sum(z) by Def. J.1.

The cost is 2^{τ/v²³⁵}·(poly(τ) + τ·2^{v^H}·poly(v^H)). ∎

**Theorem 1 (power-saving evaluation of weighted nondeterministic sums)** [R, given Lemma 1]. Assume contracting over k.
For every τ-plain instance z with |z| ≤ τ, sum(z) can be computed deterministically with 2^{O(τ^{H/(H+187)})}·poly(τ)
operations in A.

*Proof.*
- Put τ′ = ⌈τ^{(H+235)/(H+187)}⌉ ≥ τ and v = ⌊τ′^{1/(H+235)}⌋.
- Then z is τ′-plain, and |z|·v⁴⁸ ≤ τ·τ^{48/(H+187)} ≤ τ′, up to rounding, which is absorbed by enlarging τ′ by a constant
  factor.
- Also v^H ≤ τ′ ≤ v^{H+236} ≤ v^{2H}, using H ≥ 272.
- Lemma 2 applies with τ′/v²³⁵ = O(v^H) and v^H = O(τ^{H/(H+187)}). ∎

The power saving is c = 187/(H+187). For H = 272 it would be c ≈ 0.41, but H is not explicit
(Lean: H = 16(a₀+217), with a₀ from J.3).

### 2.3 3-SAT [R]

Let F be a 3-CNF on n variables.

**Sparsification** [classical; IPZ01, CIP06]. I use the sunflower version written out in OA's IM §7.1. It is elementary,
classical, and its argument does not use ports; I re-read its counting.
- Fix 0 < α < 1/4 and r = ⌈n^α⌉.
- In 2^{O(n^{1−α} log n)}·poly time, F becomes an OR of at most 2^{O(n^{1−α} log n)} 3-CNFs F_j.
- Each F_j has O(n^{1+4α}) clauses, and F is satisfiable iff some F_j is.
- (The CIP sparsification lemma with ε = n^{−α} would do as well, with a different constant in place of 4.)

**The instance for one leaf.**
- z_j = (P, ⟨F_j⟩), where P is a fixed program.
  - P builds, by recursion (a loop via `run`), a balanced binary tree of depth ⌈log₂ n⌉ whose leaves are guessed bits:
    O(n) steps, one run per assignment of the 2^{⌈log n⌉} ≥ n leaves.
  - For each clause and each literal, P walks down the tree along the binary index of the variable (O(log n) steps) and
    compares the bit with the literal's sign.
  - P fails as soon as a clause is unsatisfied. Otherwise it accepts with weight 1 and an empty tally.
- All runs halt. Every accepting run costs τ₀ = O(n + m_j log n), with m_j = O(n^{1+4α}).
- |z_j| = O(m_j log n). Put L = O(n^{1+4α} log n), so that τ₀ ≤ L and |z_j| ≤ L.
- sum(z_j) = 2^{e}·#SAT(F_j), where e = 2^{⌈log n⌉} − n counts the padding leaves. This is a positive integer iff F_j is
  satisfiable.

**Evaluation.**
- Theorem 1 with τ = L computes sum(z_j)·1_A in 2^{O(L^{ρ})}·poly(n) operations, where ρ = H/(H+187).
- Total exponent: O(n^{1−α} log n + n^{(1+4α)ρ} polylog n).
- Choose α < (1−ρ)/(4ρ). Then any δ < min(α, 1 − (1+4α)ρ) works.
- Balancing the two terms gives **δ < 187/(5H+187)**, about 0.12 if H = 272.

**The field and the bit complexity.** Here characteristic 0 is used.
- A ⊂ k is a finitely generated domain of characteristic 0. So ℤ → A is injective, and sum(z_j)·1_A determines the integer
  sum(z_j).
- To compute exactly, map A to a number field. A⊗ℚ is a nonzero finitely generated ℚ-algebra. By the Nullstellensatz,
  a maximal ideal gives a ring map ψ: A → L with [L:ℚ] < ∞, and ψ is injective on ℤ. Fix as constants the images in L of
  the finitely many named generators θ of A.
- The laws are polynomial identities over A, so every identity used (Def. J.1, G.2) survives ψ. (Over k = ℚ, ψ is not
  needed: A = ℤ[1/N].)
- Every run weight is a product of at most poly(τ) generators, and the sums have at most 2^{O(τ)} terms. So all numbers
  have poly(n) bits, and the total is 2^{O(n^{1−δ})}·poly bit operations on a multitape Turing machine.

**Theorem R.** If the contracting hypothesis (AN Def. 2.1/D.1) holds over some field of characteristic 0, then there is
δ > 0 and a deterministic algorithm that decides 3-SAT on n variables in 2^{O(n^{1−δ})} bit operations times a polynomial
in the input length.

It rests on:
- AN F.6, G.2, H.1, H.2, I.1, I.2, J.2, J.3, J.4 (statements Lean-verified);
- Lemma 1 and the uniformity claim of 2.4 (read off the printed proofs of J.3 and J.4 and of H.1–H.2; not Lean-verified);
- sparsification;
- the Nullstellensatz.

### 2.4 Uniformity [R-p]

The algorithm must be one fixed algorithm for all n; Weak ETH is about uniform algorithms. From the proofs, G for scale v
is built from three things.

1. **Fixed finite data, independent of v.**
   - The laws of G.2 and the generator table θ. These exist by the duality theorem A.6 and are not explicit. They are
     constants of the algorithm, and their number does not depend on the input.
   - The evaluator programs of J.3 (Lean `thm_onecut_evaluator`: one evaluator for each of finitely many symbol codes).
   - H, C_cut, v₀, h, b, a₁, C₁.
2. **The tower at the level n with |G_n| ≥ M** (H.1).
   - G_n = SL_h(F₂[s]/s^{n+1}).
   - A chain of subgroups {1} = Γ₀ ⊂ … ⊂ Γ_J of the kernel K_n (a 2-group), each of index b in the next.
   - Words of length ≤ L for all elements, the cosets, and fixed bijections χ ↦ χ̂.
   - The proof of H.2 uses only properties H.1(a)–(d) of these objects (l.2781: "the groups, the words, the cosets and the
     maps χ ↦ χ̂ are constants of the program"), and all of them can be checked by machine.
   - Any chain works. One can be found deterministically in poly(|G_n|) = poly(v) time: in a p-group a proper subgroup
     is properly contained in its normaliser, so extend Γ_i by an x with x ∉ Γ_i, x normalising Γ_i and x² ∈ Γ_i; this
     gives index-2 steps, and one keeps every (h(h−1)/2)-th term.
   - Words come from breadth-first search in the Cayley graph. (The Lean takes the chain from `exists_chain`, an existence
     statement, which is consistent with this.)
3. **The deterministic rules of J.2/J.3** (heavy nodes, ranks in a fixed enumeration).

So v ↦ G_v is computable in poly(v) time from fixed data. Even an exhaustive search of cost 2^{O(v^H)} would fit in the
budget. **The algorithm is uniform, but not explicit.** It is a fixed Turing machine with a finite table of constants
that is known to exist but is not written down. That is enough to contradict Weak ETH, which says that *no* such algorithm
exists.

Remark [R]. The laws are finitely many polynomial identities. If they exist over k, they exist over ℚ̄ (Nullstellensatz).
So for fixed (μ, s, a, ε, q) one could in principle search for them over ℚ̄. What is missing is a value of (μ, s) (L remarks,
l.3459–3461).

### 2.5 Where the first attempt failed, stated precisely

The strategist's §2.5 is correct in mechanism but skips the input-size constraint. Restated:

- *Black-box J.4:* sums over the runs of τ-plain instances of size ≤ τ/v⁴⁸ cost 2^{O(τ/v²⁴ + v^H)}.
  - This is a power saving only when the input is polynomially shorter than the time (|z| ≤ τ^{1−48/(H+…)}).
  - It gives nothing for SAT.
- *With Lemma 1:* the same holds with τ/v²³⁵ in place of τ/v²⁴. That is what makes |z| ≈ τ affordable.

Lemma 1 is the one extra ingredient read from a proof rather than a statement.

---

## Task 3. Comparison with the OpenAI route (Theorem A)

**Same mechanism.** Both routes run:

uniform squared Poincaré inequality over all prices → Strassen duality (AN A.6 / EG Lemma 2.2) → exact rerouting
identities (AN laws G.2 / EG motif conversion 12.1) → iterated rerouting with geometric decay of a quadratic load (AN H.2:
"the load, in a quadratic norm, is halved at every stage" / EG 13.1: shared bits ×2^{−T}) → a separator-like decomposition
(AN: tree networks cut into pieces, J.2 / HC 13.1: contraction as a sum of 2^{s^{1−η}} networks with small private pieces)
→ enumeration.

**Where they differ.**

| | Anthropic (this note) | OpenAI (Theorem A via IM 7.1) |
|---|---|---|
| Hypothesis | contracting: dense Poincaré on Mat_μ(F₂), one (μ, s) | ports: bounded-degree Poincaré over all spectral Hadamard spaces |
| Bounded degree from | F.6 on U_h at a *fixed* h (degree h−1), and the coset-complex tower SL_h(F₂[s]/s^{n+1}) (H.1), in which leaving out one generator type gives copies of U_h | port graphs (by hypothesis), restored at constant cost after each motif step |
| Object compressed | runs of a tape automaton (I.2), as a network on time blocks and input parts | arbitrary closed bit networks |
| Output | a *nondeterministic lister program*, bounded in steps | a deterministic "enumerable formula", bounded in arithmetic operations and entry queries |
| Losses per level | polylog Λ per cut; harmless here (they limit only K.7) | C₂^T growth of local fields |
| 3-SAT exponent | δ < 187/(5H+187), H ≥ 272 not explicit | δ < min(α, 1−(1+4α)(1−η)), η not explicit |

- AN F.6 together with OA HC 4.2 already gives contracting ⇒ ports (Theorem A). So Anthropic's hypothesis is at least as
  strong as OpenAI's.
- The Anthropic-only route does not fail, so OA IM 7.1 is not needed. What OA has that AN lacks is a **statement** in the
  right currency. HC 13.1 counts arithmetic operations of a deterministic procedure. AN J.4 counts steps of a
  nondeterministic program, mixing deterministic and guessing steps. So with AN one must open the proof of J.3 (Lemma 1).
- Anthropic never needed a guess count, because in §K the inputs are short.

---

## Task 4. Corollaries

### 4(a) Weak ETH ⇒ flat in characteristic 0, from Anthropic alone [R]

**Corollary 1.** Assume variable-count Weak ETH: for no δ > 0 does a deterministic algorithm decide 3-SAT on n variables
in 2^{O(n^{1−δ})}·poly (IM §1, l.33–36 of its text). Then, for every field k of characteristic 0:
(i) the contracting hypothesis fails over k;
(ii) the flat hypothesis holds over k;
(iii) √rk(a−b) is a price on Mat_μ(F₂) over k for every μ.

*Proof.*
- (i) is the contrapositive of Theorem R, applied to k itself. No transfer between fields is needed, because Theorem R
  holds for each field of characteristic 0 separately.
- (ii) Use AN thm_alt in its proved form: the Lean proof (`Paper/Alternative.lean`, l.921–924) is
  `by_cases hK : Contracting K; … Or.inl (thm_alt_euclidean hK …)`, i.e. **¬Contracting K ⇒ Flat K**. This is also the
  printed proof of D.2: "We assume that the contracting hypothesis fails and derive the flat one".
- (iii) is Steps 2–7 of D.2 (Remark D.3), at every μ ≥ 3, plus pull-back to μ = 2. ∎

**Field bookkeeping.**
- The hypotheses are per field (Def. D.1: "two hypotheses on the field k, on which the notion of a price depends").
- Theorem R covers each field of characteristic 0, so the conclusion is per field as well.
- The direction is right: Weak ETH ⇒ ¬C(k) ⇒ F(k). Nothing is claimed about characteristic p.
- In characteristic p the method gives Corollary 1′ below.

**Corollary 1′ (characteristic p)** [R]. If contracting holds over a field of characteristic p, then #3-SAT mod p is
computable deterministically in 2^{O(n^{1−δ})}·poly. The proof is the same, with A → A/𝔪 finite.
- Hence, under the hypothesis "no 2^{O(n^{1−δ})} algorithm counts 3-SAT mod p" (a mod-p variable-count Weak ETH), contracting
  fails in characteristic p and the flat hypothesis holds there.
- Getting a *decision* algorithm in characteristic p would need an isolation lemma that keeps the formula near-linear in
  size and keeps the exponent n^{1−δ}. Valiant–Vazirani does not (it adds Θ(n²) clauses and randomness). [C: I know of none.]
- The permanent plays no role in Theorem R, so characteristic 2 is not special here: it gives ⊕3-SAT.

So Corollary 1 is a conditional proof of the flat hypothesis in characteristic 0. It is independent of OpenAI's
Euclidean-geometry paper (EG Thm 1.2, which claims flats unconditionally) and uses only Anthropic plus Weak ETH.

Consequence for Anthropic's main theorem: under Weak ETH, the case that actually occurs in characteristic 0 is the flat
case. There Anthropic's bound is 2^{c(log m)^{4/3}} (E.11); the stronger contracting-case bound K.7 is then vacuous.

### 4(b) The engine's two-merge pieces under Weak ETH [R, given review-link]

Review-link gives the win-win (corrected form, l.120–124): if over k there are families with every piece
min_k c_k(A_i) ≤ (E/√p − η)λ, then FH fails over k and every extension, so contracting holds over k̄.

Combined with Theorem R this gives:

**Corollary 2.** Assume variable-count Weak ETH, and let k be a field of characteristic 0. Every family of exact
decompositions Σ_{i∈I_λ} A_i = d_λ·f_C over k, with |I_λ| = 2^{o(λ)}, of a configuration C of E edges each crossing all
p merges, has liminf_λ max_i min_k c_k(A_i)/λ ≥ E/√p.
- For two merges (the crossing), the per-merge rate is ρ ≥ 1/√2.
- So the engine's two-merge pieces, which achieve 1/√2, are optimal over every field of characteristic 0.
- Δ₃ with three merges gives 1/√3 per merge (planar bound 3√3), likewise.

*Proof.* Weak ETH ⇒ ¬C(k̄) by Theorem R (k̄ has characteristic 0). By contraposition of the win-win, no family beats the
floor; equivalently, Corollary 1(ii) gives FH over k and the flat-floor theorem applies directly. ∎

The second route is shorter, because the flat-floor theorem needs FH over k and Corollary 1 supplies it. The same holds
over a field of characteristic p under the mod-p hypothesis of Corollary 1′.

### 4(c) The dichotomy in one sentence

Either a certain inequality about "prices" of tensors over the rational numbers holds, and then Anthropic's own machinery
yields a deterministic algorithm that solves 3-SAT in time 2^{n^{1−δ}} for some δ > 0, beating every known algorithm in kind; or it
fails, and then every Euclidean shape is realised by tensor prices, the "flat" world in which Anthropic's weaker
permanent bound is the one that holds. So unless SAT is much easier than everyone believes, we live in the flat world.

---

## Task 5. Sanity checks

1. **Does Theorem R contradict anything known?** No.
   - It derives a 2^{n^{1−δ}} SAT algorithm from an *unproven* hypothesis. Weak ETH is a conjecture, and nothing known
     refutes contracting.
   - The consequence is about subexponential deterministic simulation of nondeterministic (counting) time. That is
     consistent with what is known: NTIME(n) ⊆ DTIME(2^{o(n)}) is open.
   - It does not conflict with K.6 (no small accelerators). An accelerator is a polynomial speedup *inside the
     nondeterministic weighted model* (v^H steps → v^{H−16} steps). Theorem 1 is an exponential-time deterministic
     evaluation, which K.6 says nothing about.
   - What would be a contradiction is an unconditional proof that sums over τ-step runs need 2^{Ω(τ)}. That would refute
     contracting. No such bound is known.
2. **Does the paper comment on algorithmic consequences of contracting?** No. The closest sentences:
   - [K, l.182–185] "A Turing machine or a Boolean circuit, in contrast, may manipulate the bits of its input in any way.
     The results of this paper therefore say nothing about whether NP-complete problems have fast algorithms."
     This is about their *theorems*, which are unconditional. It does not address what one *case* would give, so it is
     consistent with Theorem R.
   - [K, l.562–563] "Nor can a large Boolean circuit take the place of the program that the contracting case refutes,
     since we know no way to run it faster than gate by gate."
   - [K, l.291–292] "We do not know which of the two hypotheses holds, even over R, nor do we show that the two are
     mutually exclusive."
   - [K, l.3456–3461] "We do not know whether we are in the flat case or in the contracting case … in the contracting case
     we would also need values for the numbers μ and s."
   - [K, l.1789–1790, D.3] "Theorem D.2 is not effective: we do not know which case occurs, and the contracting case comes
     without a value for μ."
   - The paper never suggests that contracting is likely true. Theorem R says: given Weak ETH, it is false in
     characteristic 0.
3. **F₂-labels versus the field k.**
   - [K, l.270–272] "The field enters only through the tensors, which have entries in k, and the restrictions, which use
     k-linear maps. The set Mat_μ(F₂) only supplies the parties and their addition; its F₂ is not the field k."
   - [K, l.564] "Which of the two hypotheses holds may depend on the field."
   - [K, l.3471–3473, App. M] "Sections A to L use nothing about k except that it is a field, apart from the element ½ in
     Proposition E.1." The contracting half never uses ½, and the main text says §§A–K "work over the real numbers"
     (l.3416), but M generalises them.
   - So contracting over ℚ and over F_p are different hypotheses. Theorem R uses characteristic 0 in exactly one place:
     ℤ ↪ A, so that the count is recovered as an integer.
4. **Consistency with Theorem A** (`ideas-ports.md` §2.2). Contracting(char 0) ⇒ ports(char 0) ⇒ fast 3-SAT (OA), and
   contracting(char 0) ⇒ fast 3-SAT (here). Both have the same conclusion and no tension. Theorem R removes the OpenAI
   input from the 3-SAT corollary. It does not remove it from "contracting ⇒ ports", which still needs HC 4.2.
5. **Possible weak points**, ranked.
   1. Lemma 1 relies on the J.3 proof's step accounting of the plan and of the cut-packet guesses. The paper says that the
      program is "described but not printed" and that its bounds are checked only in Lean, where guesses are not tracked.
      I see no reason the bound would fail: the guessed objects are explicitly listed and sized. But it is a reading, not a
      check.
   2. Uniformity (2.4) relies on the proof of H.2 using the tower only through H.1(a)–(d).
   3. Sparsification and the program P are routine.

## Run log
- Sparse clone of anthropics/formal-math (vp-vnp), pdftotext → `scratchpad/fm/paper.txt` (4031 lines).
- Read the paper's §§1.3, 2, D, F (header, F.6), G, H, I, J, K, L, M, and the Lean files `Paper/Cuts.lean` (thm_onecut,
  thm_cut, exists_setting), `Paper/Alternative.lean` (Contracting, Flat, thm_alt), `NS1/Compose.lean` (CutD), and
  `Nc/Tower/Chain.lean` (exists_chain).
- Read OA IM §7 for the definition of Weak ETH and the sunflower sparsification.
- No code was run. Every step above is a proof or a quotation.
