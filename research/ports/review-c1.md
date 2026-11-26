# Referee report on c1d1 Part C1 (Theorems C1-OA, C1-AN, Lemma C4), spec S4, and Theorem D

Referee pass, 26 Nov 2026. Source of the claims: `research/ports/c1d1/notes.md`. Sources checked:
- HC = `survey/oa/preprints/Circuit-lower-bounds…/paper.txt`;
- IM = `survey/oa/preprints/The-logarithmic-exponent-of-integer…/paper.txt`;
- EG = `survey/oa/preprints/Euclidean-geometry…/paper.txt`;
- MM = `survey/oa/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.txt`;
- AN = `scratchpad/fm/paper.txt`, and the Lean at `scratchpad/fm/repo/vp-vnp`;
- `ports/rebase/notebook.md`, `ports/review-theoremR.md`, `mm/anti/notebook.md`.

Line numbers are those of the pdftotext files. I ran one small computation (S1, below) and nothing else.

## Summary verdict

**No fatal gap.** Theorem C1-OA, Lemma C4 and Corollary C5 are correct. They rest only on HC 13.1 as printed and on
classical facts. Theorem C1-AN is correct given Theorem R, with the padding fix, and inherits Theorem R's open
points. The M1 dependency list is right but stated more narrowly than it needs to be. Theorem D's averaging step is
correct; one side remark is wrong but harmless.

Ranked from weakest to strongest:

| # | Item | Verdict |
|---|---|---|
| 5 | C1-AN (Anthropic route in char p) | **Correct with fix, conditional on Theorem R.** No hidden scalars in AN §§G–J or in the Lean `CutD`. The padding fix is needed and sufficient. Inherits Theorem R's uniformity gap and its proof-read Lemma 1. The earlier Theorem R referee passed Corollary 1′ ("#3-SAT mod p"), which is wrong as written for two reasons; c1d1 catches both. |
| 7 | M1 dependency list | **Correct, stated too narrowly.** For B₂-circuits over F₂ any prime without ports suffices; p = 2 is needed only for part (a) (F₂-networks and parity-nondeterministic circuits). The list should also name IM §7 sparsification and the project's own Lemmas E and P. |
| 1 | HC 13.1 in char p; hash network meets its hypotheses | **Correct; one wording fix.** HC's own text allows the constants to lie in a bounded extension E₀ of F_p (l.3664–3667). That is harmless. |
| 8 | Theorem D (engine gap) averaging | **Correct with a one-line fix** (the "L bounded" remark). Threshold ½·log_β p confirmed. |
| 6 | Lemma C4, Tseitin, exponent arithmetic | **Correct.** |
| 2 | Parsimony and size of the multiplication circuit | **Correct.** For fixed a it is an XOR-only straight-line program. |
| 3 | Toeplitz pairwise independence, VV constant, one-sidedness | **Correct.** Also verified by exhaustive computation for small n. |
| 4 | Non-disjoint leaves | **Correct.** The algorithm tests each leaf separately. |
| (S4b) | Disjoint sunflower branching (only for the ⊕_p / counting variants) | **Correct**, checked against IM's depth and leaf count. |

Smaller wording points:
- "Same δ as in characteristic 0" should read "same formula for δ". The η of HC 13.1 depends on the characteristic.
- The remark on Ishai–Kushilevitz–Ostrovsky–Sahai (δ′ = δ) was not checked by me. Nothing depends on it.

---

## 5 (weakest). Theorem C1-AN: the Anthropic route in characteristic p — correct with fix, conditional

**Hidden divisions or factors: none found.**
- AN App. M, l.3470–3472, verbatim: "Sections A to L use nothing about k except that it is a field, apart from the
  element 1/2 in Proposition E.1". This confirms the notes' claim.
- I searched §§G–J (l.2398–3180) for 1/2, divisions, inverses, denominators and "characteristic". Every hit is a norm,
  a metric exponent, or "we divide the packets into batches". None is a field division.
- The laws are exact. Def. G.1, (G.2): Π_e[bits agree] = Σ_i Σ_y Π_g (node tensor). There is no scalar on the left. The
  laws come from covers. A.1 defines a cover as "s = s₁ + ⋯ + s_r with every s_j a restriction of t_j", which is exact,
  and duality (A.6) produces covers.
- After G.2 the text says: "The laws are finitely many polynomial identities with coefficients in A, so they hold over
  every commutative A-algebra."
- Ring elements in programs are exact. J.3, l.3111–3113: "An entry … is an element of A, hence a fixed sum of products
  of the generators, so multiplying by it is guessing a summand and multiplying by its factors." An integer such as 2 is
  written as 1+1, so this is exact in every characteristic.
- I.2 is parsimonious. Around l.2891: an accepting run of z "gives exactly one accepting run of the machine, with the
  same weight … and there are no others".
- The Lean confirms Def. J.1 without a scalar. `NS1/Compose.lean:25`, `CutD`: `… ∧ pv θ z = wsum Q (pvs θ)` over
  `[CommRing A]`. `Paper/Cuts.lean:570`, `exists_setting {K} [Field K] (hK : Contracting K)`, puts no condition on the
  characteristic.

**The 2^e factor and the fix.**
- The factor is real. Rebase §2.3 guesses 2^{⌈log n⌉} leaves, so sum = 2^e·#SAT with e = 2^{⌈log n⌉} − n. The Theorem R
  referee confirms this (review-theoremR l.205).
- The fix is right: fail unless every padding leaf is 0. Accepting runs then correspond bijectively to assignments,
  and sum = #SAT·1_A in every characteristic. The extra cost is O(n) steps.

**The hash test in the program model.**
- G = O(n log n log log n) gates are evaluated with values in a persistent balanced tree: O(log G) steps per read and
  per path-copying write.
- So τ₀ and |z| grow by O(n log² n log log n), which is below L = Θ(n^{1+4α} log n).
- Alternative: guess every gate value as a leaf and check each gate deterministically. This is also parsimonious,
  because the values are forced.
- Either way the instance stays τ-plain: all runs halt, the tally is empty, and there is no `use`.
- Theorem 1 of rebase needs only τ-plainness and |z| ≤ τ, so no 3-CNF structure is required.

**The map A → F_q.**
- A is a subring of a field of characteristic p and is finitely generated over ℤ (Lean `Algebra.FiniteType ℤ A`). So A
  is a nonzero finitely generated F_p-algebra.
- By Zariski, A/𝔪 is a finite field F_q, and ψ(1) = 1. The constants are ψ(θ) for the finitely many generators.
- ψ(sum(z)) = (#solutions) mod p. Correct.

**What C1-AN inherits.**
- Theorem R's open points (review-theoremR, item 4 and item 1): uniformity is unverified (`thm_tree`/`prop_pieces`
  constructivity), and Lemma 1 (guess count) is read off the printed proof.
- So C1-AN, and Theorem D items 3–4, are "(R?)" exactly as flagged.
- The non-uniform fallback still refutes nuWETH and its mod-p analogue.

**A defect in the earlier Theorem R review (not in c1d1).**
- review-theoremR l.216 says "Corollary 1′ is correct". As written, Corollary 1′ (rebase l.347) claims deterministic
  #3-SAT mod p. That is false for two reasons:
  - p = 2 with n not a power of two: sum = 2^e·#SAT ≡ 0;
  - the sunflower leaves overlap, so Σ_j #F_j ≠ #F in general.
- c1d1 C1.4 identifies and fixes both. With both fixes (padding, and the disjoint branching of S4b below), Corollary
  1′ is correct.
- Rebase l.351–352 also says that a decision algorithm in characteristic p "would need an isolation lemma … VV does
  not". C1 refutes this: a structured hash adds O(n log n log log n) gates, not Θ(n²).

## 7. Theorem M1's dependency list — correct, stated too narrowly

**Statement read** (`mm/anti/notebook.md` l.397–413). M1: "Assume [MM] Lemma 4.1 and that some prime p has no ports
(take k = F_p)." The proof is Lemma P(b) plus Lemma 4.1 with r = n², q = n.

**MM Lemma 4.1 as printed** (MM l.607–611, Nov-24 version):
> "Let the field have no ports. Consider a fixed trivalent topology with r input bits and r output bits. … If each input
> has a uniform destination on a set of q ≥ 2 outputs, the topology has size Ω(r√log q)."
- It sits under "Fix a finite field k" (MM l.291).
- "A field has ports" is [42, Def. 11.1], and MM's [42] is EG (l.6023). This is the same Def. 11.1 that HC uses for
  "characteristic admitting ports" (HC l.348–350; EG l.2820, "depends only on the characteristic").
- Nothing in the proof (l.612–643) uses the characteristic. **It holds for F₂ as printed**, and for every F_p.

**Which characteristic M1 needs.**
- Lemma E turns a B₂-circuit into a network with {0,1} tables and unique internal labellings. That network represents
  the predicate [C = AB] over every field.
- So the B₂-circuit bounds (over F₂, Boolean, (min,+), integer) need only **some** prime without ports.
- p = 2 is needed only for part (a)'s F₂-networks and the parity-nondeterministic circuits.
- c1d1 C1.4's sentence "M1 with k = F₂ needs characteristic 2 has no ports" is therefore true but stronger than
  necessary. Under rWETH, C1-OA removes ports at every p, so nothing changes.

**The corrected list.** M1, including (a) at p = 2, follows from:
- rWETH (or nuWETH, UWETH, or ⊕₂WETH with the disjoint sparsification);
- HC 13.1 at the chosen p;
- IM §7 sunflower sparsification (classical, printed in IM);
- MM Lemma 4.1 as printed;
- the project's Lemmas E and P.

Neither Theorem R nor (H1₀) is needed.

**The ⊕_pWETH entry in the C1.7 table.** It needs a deterministic exact mod-p count, so it needs the disjoint branching.
That branching is correct (S4b).

## 1. HC 13.1 in characteristic p — correct (one wording fix)

**Statement** (HC l.3069–3075), verbatim:
> "Fix a characteristic admitting ports. There is an η > 0 such that every closed bit network of volume at most s and
> maximum degree at most s^{1/20}, over any field of this characteristic, has a formula for its contraction using
> 2^{O(s^{1−η})} arithmetic operations and local entry queries. … uses fixed prime-field constants."

**What is counted.**
- HC l.2943–2945 defines the objects: "A bit network contracts local tensors by summing products over paired bit
  indices. … The volume counts tensors and wires, including one wire for each unpaired exterior index. … Loops, parallel
  wires and disconnected networks are allowed."
- So the network sums over one bit per wire, every wire. The result is a field element.
- With {0,1} tables over F_p, the result is #(consistent labellings of all wires) mod p.
- Tables are arbitrary functions into the field. XOR, AND, equality and pin tables are all admissible, and none needs
  to come from a clause.
- Volume counts tensors and wires, not table entries.

**No 3-CNF anywhere.** The proof (l.3077–3137) does the following:
- places tensors in lanes by weight "one plus its degree";
- routes the wires by Beneš;
- applies the EG 13.1 compressor;
- enumerates histories.

"Each original factor moves intact to one final position, with all of its arguments", so any tables work. Characteristic
0 appears only in the last paragraph (denominators m).

**Constants (the wording fix).**
- HC l.3049–3051: "The maps use a fixed finite list of scalars satisfying fixed integer polynomial equations. Applying
  the companion theorems over the prime field gives a solution there".
- EG 12.1 (l.3075–3083): "… fixed integer polynomial equations with a solution in F. They hold over every commutative
  unital ring with any assignment satisfying these equations."
- But HC l.3664–3667 hedges: "In fixed positive characteristic we keep the original prime and constants. … let E₀ be a
  finite field containing the constants, of degree over F_p bounded independently of n. For the prime-field choices we
  can take E₀ = F_p."
- Either way the argument survives. A finite polynomial system solvable over the closure of F_p is solvable over some
  fixed F_{p^r}. Computing over F_{p^r} costs O(1) bit operations per operation, and the {0,1}-network's contraction
  lies in F_p ⊂ F_{p^r}.
- C1.1 should say "constants in F_p, or in a fixed finite extension; immaterial".

**The hash network meets the hypotheses.**
- Gate tables are ternary: [w = u⊕u′] or [w = u∧u′]. Every fan-out, including the extra occurrence of each variable,
  goes through trees of ternary equality tables, so the maximum degree is ≤ 3 ≤ s^{1/20}.
- Total fan-out is 2·#gates, so the equality trees add O(#gates) volume.
- The constants a and b can be pinned by unary tables, or folded into the gates (XOR with 1 is NOT).
- Volume is s = O(v^{1+4α} + v log v log log v) = O(v^{1+4α}).

**Bounded occurrence is not needed.** IM §7 uses the leaf structure only to bound the clause count (O(vR²) = O(v^{1+4α}))
and the number of leaves (2^{O((v/r) log v)}). HC 13.1 needs only volume and degree. No property of the hash's
variables is required.

**Cost.**
- Formula generation takes 2^{O(s^{1−η})} bit operations per network. The topology changes per leaf and per trial,
  which is fine.
- Entry queries on {0,1} tables are O(1).
- Total: 16v · 2^{O(v^{1−α} log v)} · 2^{O(v^{(1+4α)(1−η)})}, exactly IM 7.1's exponent with this characteristic's η.

**S4(a): confirmed.** HC 13.1's proof uses characteristic 0 only in its final paragraph.

## 2. Parsimony and size of the hash circuit — correct

- For a fixed seed a, x ↦ T_a x is F₂-linear.
- Schönhage's ternary method (ring F₂[t]/(t^{2·3^k}+t^{3^k}+1), length-3^k DFTs) and Cantor–Kaltofen are bilinear
  straight-line programs over F₂ with no divisions. In Schönhage's method the inverse DFT divides by 3^k ≡ 1 mod 2,
  which is why it is ternary.
- With one operand fixed, propagating the constants leaves an XOR-only circuit of size O(N log N log log N), with
  N = 3n.
- Every wire is a function of x, so given x the labelling of every gate and copy wire is unique. The network's
  contraction is exactly |{x : F_j(x), h(x) = 0}|.
- The circuit can be built in poly(n) time.
- Depth plays no role: HC 13.1 has no depth hypothesis, and the AN route pays only O(log) steps per gate.

## 3. Toeplitz hash, VV, one-sidedness — correct

**Lemma C1.**
- For z ≠ 0 with least support index i*, row j's top index n−1+j−i* is larger than every index in rows j′ < j and than
  the other indices of row j.
- That index lies in [0, n+k−2], inside a's range. So T_a z is uniform for **every** k ≥ 1; the condition k ≤ n+1 is
  not needed.
- (h(x), T_a z) is uniform because b is independent of a. This gives pairwise independence.

**Lemma C3.**
- Pr[exactly one] ≥ |S|2^{−k} − |S|(|S|−1)2^{−2k} ≥ q(1−q), with q = |S|/2^k ∈ [1/4, 1/2].
- The minimum is at q = 1/4: **3/16**.
- A good k always exists in {2, …, n+1}: k = 2 if |S| = 1, otherwise k = ⌈log₂|S|⌉ + 1.
- With k uniform over n values the success probability is ≥ 3/(16n). With 16n rounds the failure probability is
  ≤ (1−3/(16n))^{16n} ≤ e^{−3}.

**S1 computation.** Script `scratchpad/c1ref/s1.py`.
- Exhaustive over all a, for n ≤ 6 and all k ≤ n+1: a ↦ T_a z is exactly balanced for every z ≠ 0.
- For n ≤ 5, random S with 2^{k−2} ≤ |S| ≤ 2^{k−1}, and the exact probability over all (a, b): the worst value is
  0.2058 ≥ 0.1875.

**One-sidedness.**
- The algorithm accepts iff some (trial, leaf) has a count ≢ 0 mod p.
- A nonzero residue implies a nonzero count, hence a satisfying assignment, so the algorithm never errs on an
  unsatisfiable formula.
- A count ≡ 0 mod p with many solutions only lowers the success probability, which is already accounted for by
  requiring exactly one solution.
- Final success probability ≥ 1 − e^{−3} > 1/2.

## 4. Non-disjoint leaves — correct

- IM l.1720–1721: "Both children imply the parent". So every leaf's solution set lies inside F's.
- On the event |S_F ∩ h^{−1}(0)| = 1, every leaf count is 0 or 1, and the leaf containing x₀ has count 1 ≢ 0.
- One (k, a, b) for all leaves is fine, because the event depends only on F.
- The algorithm, as specified in step 3 ("Accept if some contraction is nonzero"), never sums over leaves, so
  multiplicities cannot cancel. Sound and complete.

## 6. Lemma C4 — correct

**Tseitin.**
- XOR gate: 4 clauses of width 3.
- AND gate: 3 clauses of width ≤ 3.
- Constants become literal signs, and outputs = 0 become unit clauses.
- The encoding is parsimonious (§2), so #F′ = |S_F ∩ h^{−1}(0)|.

**Variable count.** v′ = n + O(n log n log log n).

**Exponent.**
- 16n·2^{O(v′^{1−δ})} = 2^{O(n^{1−δ}(log n log log n)^{1−δ})} ≤ 2^{O(n^{1−δ}log² n)} ≤ 2^{O(n^{1−δ′})}, for every
  δ′ < δ. The input length of F′ is poly.
- With a linear-size pairwise-independent family, v′ = O(n) and δ′ = δ. I did not check the cited result.

**(a) ⇒ (b), and Corollary C5.** (a) ⇒ (b) is trivial. On formulas with ≥ 2 solutions the promise algorithm may answer
anything. That does not matter: if F is unsatisfiable, every F′ is unsatisfiable and gets "no". Corollary C5
(rWETH ⇒ UWETH ⇒ ⊕_pWETH) is the correct contrapositive.

**C1.5 (non-uniform derandomisation).**
- There are ≤ 2^{8v³} formulas.
- (1−3/(16v))^{64v⁴} ≤ e^{−12v³} = 2^{−17.3v³} < 2^{−8v³}. Correct.
- The Impagliazzo–Wigderson step is fine: a one-sided time-T test is a circuit of size poly(T), and there are poly(T)
  seeds.

## S4(b). Disjoint sunflower branching — correct

**The children.** The petal child becomes "parent ∧ petals ∧ ¬centre", with ¬centre added as 1–2 unit clauses. The two
children then partition the parent's solutions.

**IM's counting** (IM l.1724–1738) still holds:
- Units only accumulate and persist: a unit is never a strict superset of a clause. So there are still ≤ 2v units per
  path.
- The extra units create no pairs, and only delete pairs (supersets).
- So the pair-degree bound, the O(vr) bound on new pairs, the O(vr) depth, and "the petal child consumes ≥ r units or
  ≥ R pairs" are all unchanged.

**The new petals still survive simplification.** A petal cannot contain ¬ℓ for a centre literal ℓ: the selected clause
would then be a tautology, and tautologies were removed.

**Leaf count.** It stays 2^{O((v/r) log v)}.

## 8. Theorem D (engine gap) — correct with a one-line fix

**The averaging step.**
- Suppose every ρ_ℓ > θ′. Then θ′^L < Πρ ≤ e_L/e_0 ≤ (log K_L)^{−α′+o(1)}.
- That gives L > (α′−o(1))·log log K_L / log(1/θ′).
- Together with L ≤ log_β log K_L + O(1), this is impossible for large n when θ′ > β^{−α′} = θ. It needs
  log log K_L → ∞, which holds.

**The η margin.** With θ′ = (θ+1/√p)/2 and η = (1/√p−θ)/3: (1/√p − η) − θ′ = (1/√p − θ)/6 > 0. So ρ ≤ (1−ξ)(1/√p − η)
once ξ is small, and uniformity of ξ_ℓ → 0 covers the moving level ℓ(n).

**The threshold.** θ < 1/√p ⇔ α′·log β > ½·log p ⇔ α′ > ½·log_β p. Correct.

**Lemma D2.** Correct, provided E_C ≥ 1, i.e. raw bits per copy = E_C·λ with E_C ≥ 1. Otherwise η/E_C ≠ η. This is
implicit in the definitions and should be stated.

**The fix.** The parenthesis "(if L stays bounded then e_L is bounded below and α′ = 0)" is false without FH: ρ_ℓ may
tend to 0. It is harmless, since bounded L with e_L → 0 forces some ρ_ℓ → 0, which is the desired conclusion. Replace it
with that sentence.

**Not checked by me.** The win-win theorem of review-link, and items 3–4 of Theorem D (Theorem R and C1-AN, "(R?)").

---

## Recomputed constants

| Quantity | Value |
|---|---|
| VV per-trial success | ≥ 3/16 at the right k; ≥ 3/(16v) for uniform k ∈ {2..v+1}; 16v trials give ≥ 1 − e^{−3} |
| δ in C1-OA | any δ < min{α, 1 − (1+4α)(1−η_p)}, with α < 1/4 and (1+4α)(1−η_p) < 1. η_p is HC 13.1's η for characteristic p, not char 0's |
| δ in C1-AN | δ < 187/(5H_k+187), with H_k from J.4 for the field in question |
| Hash volume | O(v log v log log v), below v^{1+4α} |
| Lemma C4 | v′ = O(v log v log log v); every δ′ < δ |
| Non-uniform advice | 64v⁴ triples, O(v⁵) bits |
| Theorem D threshold | α′ > ½·log_β p |
| Theorem D margins | θ′ = (θ+1/√p)/2, η = (1/√p−θ)/3, gap (1/√p−θ)/6 |
