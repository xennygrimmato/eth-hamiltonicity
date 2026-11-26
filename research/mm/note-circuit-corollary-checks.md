# Working checks for note-circuit-corollary.md

Executor **note**, 26 Nov 2026. Working file, not for publication. Cross-checked against
research/mm/anti/notebook.md §1 (which already quotes the paper's statements verbatim); quotations are not repeated
here unless I add something.

Sources (scratchpad sparse clone of github.com/openai/math at commit 3344da59, "Add November 24 mathematics
manuscripts and Lean formalizations"):
`/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/survey/oa`
- [MM] preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build/*.tex and paper.txt
- [43] preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/build/*.tex
- Lean: lean/OAI (added by `git sparse-checkout add lean/OAI`), lean/docs/379.md, lean/ComparatorChallenges

## 1. Quotes: cross-check of anti §1

Checked each quotation in anti §1.1–1.6 against obstruction.tex and list.tex: they agree with the LaTeX word for
word. The numbering also matches paper.txt. Pages are the printed page numbers in paper.txt:
- §2.1 definitions (bit tensor, network, trivalent, size, volume): p. 7, obstruction.tex l. 11–21.
- Theorem 2.1 (Compression of tensor powers, conditional on ω_k < 9/4): p. 7.
- Theorem 2.2 (Volume of list distinctness): p. 7, obstruction.tex l. 46–60. **Unconditional**: it carries no
  hypothesis on ω.
- Proposition 2.3 = "Over every finite field k, ω_k ≥ 9/4": pp. 7–8. Its proof holds the single embedding
  sentence (obstruction.tex l. 75–78). That sentence is about the sorting circuit only.
- Lemma 4.1 (Uniform destinations, no ports): p. 13. §4.3 (ports): p. 14.

Additions to anti:
- Definition of D_w also appears in the intro (intro.tex l. 99–112): "Given a list of 2^w words of length 2w bits,
  return one if all the words are distinct and zero if any word repeats. [...] The network sums over its internal
  bits and, for each setting of its exterior bits, must give the exact zero-one answer. With t lists it must give the
  product of their t answers. Its internal wiring may connect different lists."
- [43, §12.2 (model.tex l. 65–71)] uses the same model: "A ternary equality tensor can pass the same bit to several
  factors. The volume counts tensors and wires, including one wire for each unpaired exterior index. [...] Loops,
  parallel wires and disconnected networks are allowed."
- [43, Theorem 12.1, "Exact batches"] (model.tex l. 82–88): "Fix a finite field F of characteristic χ. There are
  constants σ, δ > 0 such that, for all sufficiently large n and every 1 ≤ k ≤ 2^{n^σ}, every trivalent bit network
  over F realizing the batch (U_n^*)^{⊗k} has volume greater than k n^{1+δ}." Here U_n^* is a clocked universal
  GapP function (signed path count) reduced into F. So it is a counting function, not a 0/1 Boolean function in P.
  (Caveat: model.tex l. 3 opens the section with "Fix a characteristic χ admitting ports". Whether Thm 12.1 is meant
  only for port characteristics is ambiguous from the text. [MM] §4.3 uses it only in the ports case, so this does
  not matter for us.)

**Does the release state the Boolean corollary anywhere?** I searched by grep, case-insensitive, for "Boolean
circuit", "superlinear", "super-linear", "element distinctness" and "list distinctness" in:
- all .tex files of the six family-379 preprints in the clone;
- CONTENTS.md, overview.tex and history.md;
- the whole lean/OAI tree, for `manyList`, `distinctPower` and `Realizes` outside MatrixExponent.

Result: no statement of a Boolean-circuit lower bound for D_w. The only "superlinear circuit lower bound" in the
catalogue is family 378, for a language in E^NP, infinitely often. [MM] mentions "Boolean gates" only inside the
proof of Prop. 2.3. The tape paper (history.tex) discusses AFKL's conditional Boolean-circuit bound and the
refutations of the multiple-unicast conjecture, and says nothing about an unconditional one. **Conclusion: not
stated in the release** (grep-level; I did not read every page of the three long companions).

## 2. Lean cone check (grep and import closure, no build)

Method: a script (scratchpad/scripts/cone.py) computes the transitive `import` closure from
`OAI.LinearAlgebra.SpectralBooks.ExactExponent`. Result: 592 OAI modules (list in scratchpad/scripts/cone.txt).

The statement chain was read in the files themselves:
1. `SpectralBooks/ExactExponent.lean`: `theorem square_exponent (F) [Field F] : formalOmega F 1 1 1 = 9/4 :=
   (formalOmega_square_eq_omega F).trans (MatrixExponent.omega_eq F)`.
2. `MatrixExponent/FieldFormula.lean`: `omega_eq F := (omega_eq_and_rigidity F).1`, and `omega_eq_and_rigidity :=
   contact_of_installations (fun p _ => Rounds.installable (ZMod p)) F`.
3. `MatrixExponent/Realization.lean`: `contact_of_installations ... := contact_of_network_estimates (fun p _ =>
   BatchDescent.hard (ZMod p)) ...`. Its docstring reads "Exact many-list hardness holds over all finite fields."
4. `MatrixExponent/Obstruction.lean`: `contact_of_network_estimates (hard : ∀ p [Fact p.Prime], Tagged.Hard (ZMod p))
   ...` ends with `exact incompatible (seed _) (Tagged.manyList_of_tag (hard p)) shrink.lists`.
   - `seed` is the sorting network, i.e. the upper bound.
   - `manyList_of_tag (hard p)` is Theorem 2.2.
   - `shrink` is the compression, i.e. Theorem 2.1.
   This is exactly the structure of the proof of Prop. 2.3.
5. `MatrixExponent/BatchDescent/Hard.lean`:
   ```lean
   theorem hard (F : Type) [Field F] [Finite F] : Tagged.Hard F :=
     Processor.hard_of_descent (descent fun bad => compilation_of_encoded (encoded bad))

   theorem manyList_full (F : Type) [Field F] [Finite F] :
       ∃ η : ℝ, 0 < η ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ,
         1 ≤ t → (t : ℝ) ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + η)) → Realizes F w t m →
         (t : ℝ) * listBits w * (w : ℝ) ^ η < m :=
     Tagged.manyList_full (hard F)
   ```
6. The definitions in `MatrixExponent/Network.lean` (96 lines, read in full) and `ListBounds.lean`:
   - `listBits w = 2*w*2^w`.
   - `Wire` is a binary tree of bits.
   - `Net F a b k m` is built from:
     - `table` (any k : Val a → Val b → F with `wd a + wd b ≤ 3`, counting 1 vertex);
     - `par` (product);
     - `comp` (sum over the shared bits);
     - `trace` (loops);
     - free rewirings.
   - m counts vertices.
   - `distinctPower F w t x = ∏_lists [the 2^w words of 2w bits are Nodup]`.
   - `Realizes F w t m := ∃ v, Net F (lists w t) .unit (distinctPower) v ∧ m = v + t*listBits w`, i.e. m is the
     paper's *size* (vertices plus exterior bits).

   So `manyList_full` is Theorem 2.2 in its size form, with t up to 2^{w^{1+η}} (wider than the paper's t ≤ 2^w)
   and with constant 1 in front.
7. No `sorry`, `admit` or `axiom` in the 592 cone files. The only grep hits are the English word "admit" in
   docstrings. I did not check for `native_decide`/`implemented_by` beyond the same grep, which also found none.
8. Top-level Lean route: `hard` has only `[Field F] [Finite F]`, so the statement carries no ports/no-ports
   hypothesis. The proof goes `Processor.hard_of_descent` → `hard_of_resists (resists F K q)`, a "descent" plus
   "resistance" (diagonal) argument. I did not trace whether Lemma 4.1's metric argument appears deeper. It is not
   needed at the top level.
9. Embedding infrastructure in Lean: `FunctionNetwork.lean` defines `DNet F a b f m` (the graph tensor
   [f x = y] with ≤ m vertices) with `table`, `comp`, `par`, `id`, `dup` (copy, 1 vertex per bit), `discard`.
   `Distinctness.lean` has `pin` (add 1 vertex to turn a Bool-valued graph tensor into the 0/1 tensor) and builds
   the sorting seed with ≤ 2000·n_w·w² size. **A general "Boolean circuit ↦ network" lemma is not stated in Lean**,
   and no Boolean-circuit corollary of `manyList` exists anywhere in lean/OAI (grep for `manyList`/`distinctPower`
   outside MatrixExponent: only `LinearAlgebra/MatrixExponent.lean`, another assembly of the same theorem).
10. lean/docs/379.md does not mention Theorem 2.2 in its prose. It lists only top-line results, and says the
   ⌈n^{9/4}/2⌉ per-n bound is unformalised.

**Answer.** Theorem 2.2 is formalised, as `BatchDescent.manyList_full` (and `manyList`), and it is in the
dependency cone of `square_exponent`. So the Lean proof of ω = 9/4 rests on it. A Boolean-circuit corollary is
not stated in Lean. What we did not do: build the project, run the Comparator, or check that the Lean build of this
commit succeeds.

## 3. Derivation (full), with failure points

**Circuit model.**
- N inputs; gates from any basis of fan-in ≤ 2 (B₂ = all 16 binary functions, plus NOT and the constants).
- Unbounded fan-out; one output; size s = number of gates.
- Fan-in ≤ b for fixed b changes only the constants.

**Lemma E (ours).** For every finite field k, a circuit of size s on N inputs computing f: {0,1}^N → {0,1} yields a
trivalent k-network representing f exactly (value 1 ∈ k if f(x) = 1, else 0) with at most 3s + N + 2 vertices,
hence size ≤ 3s + 2N + 2.

*Construction.*
1. Gate g = op(u, v) becomes a vertex with table T_g(a, b, c) = [c = op(a, b)], arity 3. A NOT gate gets arity 2,
   a constant gets arity 1.
2. A node (input or gate) with fan-out f ≥ 2 gets a chain of f − 1 copy vertices E(a, b, c) = [a = b = c].
   Fan-out counts the output use too.
3. An input with fan-out 0 gets a vertex with table ≡ 1 of arity 1. Its position is exterior, so nothing is summed.
4. The output wire ends in a vertex P(c) = [c = 1].
5. Inputs are the exterior bits. Every other position is paired by a wire.

*Count.*
- Σ fan-outs ≤ 2s + 1, so there are at most 2s + 1 copy vertices.
- Vertices ≤ s + (2s + 1) + N + 1.
- Arity ≤ 3 everywhere.

*Correctness.* Fix x. In a product that is nonzero, every copy table forces equal values and every gate table
forces its output wire to equal op of its input wires. So, by induction in topological order, every internal wire
carries the value the circuit computes. The product is 1 if P accepts and 0 otherwise. Hence at most one term of
the sum is nonzero, and the value is [f(x) = 1] in every characteristic. Every wire carries a bit, so there is no
issue with field values on wires.

*Lean cross-check.* The same construction is `DNet.table/comp/par/dup/discard` + `pin`. Lean's costs are 1 per
table, `wd a` per dup/discard of a bundle, and 1 for the pin. These match my count.

**Corollary.**
- Take f = D_w, N = n_w = 2w·2^w and t = 1 in `manyList_full`: N·w^η < 3s + 2N + 2. Hence
  s > (N(w^η − 2) − 2)/3.
- log₂N = w + log₂(2w), so w ≥ log₂N − log₂log₂N − 1 for large N.
- Result: s ≥ (1/3 − o(1))·N·(log₂N)^η for all large N of the form n_w, for some η = η(k) > 0, ineffective.
- Using the paper's volume form instead: volume ≥ size, and the volume of the Lemma E network is ≤ (5/2)·#vertices
  + N. This gives the same bound with another constant.
- σ: unconditionally only "some σ > 0" (Lean: some η > 0). [MM] §4.2 gives any σ < 1/2 if the characteristic has
  no ports. §4.3 gives σ < min{a/4, bδ/4, 1/4} if it has ports. Which case holds is open in the release.
- k: any finite field works. k = F₂ is the natural one, and then the corollary uses η(F₂) only.
- All input lengths: let f_N be D_w on the first n_w bits, for n_w ≤ N < n_{w+1} (n_{w+1}/n_w → 2). Then
  s(f_N) = Ω(N (log N)^η) for all large N.

**What else follows (each is a [D] reading; flags in brackets).**
1. *Bounded fan-in b.* A gate of fan-in f ≤ b is itself a function on f bits. Replace it by a fan-in-2 circuit of
   O(2^f) gates, so the constant becomes O_b(1). [safe]
2. *Mod-p counting (parity) circuits.*
   - Let C(x, y) have guess bits y. Make each guess bit an internal bit with its copy chain. A guess bit of fan-out
     0 must be deleted: an internal wire summed against a ≡1 table doubles the count.
   - The network value is #{y : C(x, y) = 1} mod p.
   - So: if #{y : C(x,y)=1} ≡ D_w(x) (mod p) for all x, then |C| = Ω(N (log N)^η). Here |C| counts gates; guess
     bits enter through their copy vertices, and the count ≤ 3s + N + 2 still holds when guess bits are counted as
     nodes.
   - p = 2 gives ⊕-circuits (count must be odd exactly when the words are distinct). Unambiguous circuits (count
     ∈ {0,1}) are covered over any p.
   - [Flag: the count must be ≡ 1 when the words are distinct and ≡ 0 when they are not, not merely nonzero mod p.
     Ordinary nondeterministic circuits (OR over witnesses) are NOT covered.]
3. *Sanity check against nondeterminism.*
   - ¬D_w ("some word repeats") has nondeterministic circuits of size O(N). Guess i ≠ j (2w bits); two
     multiplexers, each O(2^w·2w) = O(N) gates; compare.
   - So D_w has co-nondeterministic circuits of size O(N).
   - Theorem 2.2 therefore says that mod-p counting cannot simulate this co-nondeterministic linear-size circuit at
     linear size. No contradiction with anything known to me, but experts should see it.
   - [Flag: this is the place where an expert could find a clever linear-size mod-p construction. I tried:
     #collisions mod p and Fermat tricks give [#collisions ≢ 0 mod p], not [#collisions = 0]; the
     inclusion–exclusion network costs ~N·2^w.]
4. *Direct sum.*
   - A multi-output circuit of size s computing D_w on t lists (tN inputs, t outputs), followed by an AND tree of
     t − 1 gates, gives a network for D_w^{⊗t}. So tN·w^η < 3(s + t − 1) + 2tN + 2, i.e.
     s ≥ (tN(w^η − 2) − 3t)/3.
   - The same holds for a single-output circuit computing the AND of the t answers.
   - Range: t ≤ 2^{w^{1+η}} (Lean) or t ≤ 2^w (paper).
   - Comparison: direct-sum statements for general circuits are rare. Uhlig-type results show they fail for some
     functions (hardest functions on n bits, t ≤ 2^{o(n/log n)} copies), which is no conflict here. [memory]
5. *F_q-arithmetic circuits evaluated on Boolean inputs* (functional correctness).
   - Each F_q gate is a table on O(log q) bits, which is O_q(1) trivalent vertices. So the bound transfers for
     fixed q. [safe]
   - It is not new for q = 2, since that model is the Boolean circuit model again.
6. *Formulas and branching programs: not new.*
   - Nechiporuk-type counting already gives near-quadratic bounds for element distinctness. The subfunction count
     of one word is ~2^{w·2^w}, giving ≈ N²/(log N)² for BPs and ≈ N²/log N for B₂ formulas. [D, standard
     calculation, constants unchecked]
   - So only general circuits are of interest.
7. *Membership in AC⁰.* D_w = ∧_{i<j} ∨_{b} (x_{i,b} ⊕ x_{j,b}) has polynomial size and depth 3–4. It is also in
   uniform AC⁰. Upper bound O(N log N) gates via AKS: O(2^w w) comparators of O(w) gates each; Batcher gives
   O(N log² N). [safe]

**Where our reading could be wrong.**
(a) "Represents" means equal as functions {0,1}^{ext} → k. Lean `distinctPower` confirms this.
(b) Volume vs size: these differ only by constants. Lean uses size, with constant 1.
(c) Trivalency: gates of arity 3 = 2 inputs + 1 output. Lean `table` requires `wd a + wd b ≤ 3`, which confirms it.
(d) Input length: Lean `listBits w = 2w·2^w` confirms n_w.
(e) Possible hidden restriction of networks, e.g. "no cycles" or "no fan-out": the restriction goes the other way.
    Networks are more general than circuits: loops and traces are allowed, and tables are arbitrary.
(f) Unused exterior inputs: handled.
(g) The only real risk is that Theorem 2.2 / `manyList_full` is false, i.e. that the paper or the Lean build is
    wrong. We have not verified either.

## 4. Literature (web-checked 26 Nov 2026 unless marked [memory])

- Li–Yang, "3.1n − o(n) circuit lower bounds for explicit functions", STOC 2022 (ECCC TR21-023): B₂, affine
  dispersers. [web] arXiv papers from Feb and Apr 2026 still cite 3.1n as the record. [web] A search snippet
  mentioned an ECCC 2026 "3.5n − o(n)" report; I could not confirm it. Say "3.1n, to our knowledge".
- Find–Golovnev–Hirsch–Kulikov, (3 + 1/86)n − o(n), FOCS 2016. [web]
- Blum, 3n − o(n), 1984. [memory]
- Lachish–Raz 4.5n − o(n) (STOC 2001) and Iwama–Morizumi 5n − o(n) (MFCS 2002), both for basis U₂. Joint journal
  version by Iwama–Lachish–Morizumi–Raz. [web]
- Limits of gate elimination: Golovnev–Hirsch–Knop–Kulikov (2016/2018). A formalisation of gate elimination cannot
  give more than about 5n. [web snippet; exact statement unchecked]
- Natural proofs:
  - Razborov–Rudich (1997). [memory]
  - Miles–Viola (CRYPTO 2012; JACM 2015), candidate PRFs of quasi-linear size n·polylog n. With those candidates,
    natural proofs cannot beat roughly n^c circuits; the relevance to n·polylog bounds is through quasi-linear
    PRFs. [web]
  - Careful wording: a natural property useful against size N·polylog N would break quasi-linear-size PRFs, if the
    candidates are secure. Whether the [MM] argument is "natural" is unclear. It quantifies over spectral points
    supplied by existence theorems, and the Lean route is diagonal.
- Network coding:
  - Afshani–Freksen–Kamma–Larsen, "Lower bounds for multiplication via network coding", ICALP 2019
    (arXiv:1902.10935): the Li–Li conjecture implies Ω(n log n) for constant-degree Boolean circuits for
    multiplication, via shifts. [web]
  - Farhadi–Hajiaghayi–Larsen–Shi, "Lower bounds for external memory integer sorting via network coding", STOC
    2019 (arXiv:1811.01313). [web] (Its circuit consequences: [memory], not cited in the note.)
  - **New since 2019:** the multiple-unicast (Li–Li) conjecture has been refuted, all as unrefereed preprints:
    - Braverman–He, "The multiple unicast conjecture is false", arXiv:2610.10108: coding gap Ω((log n)^ε) after
      amplification [BGS17].
    - Zhang–Li–Li, arXiv:2610.09367: routing ≤ K/(log n)^c while coding approaches 1, formalised in Lean.
    - Li–Li–Liu, arXiv:2610.20079: faster external-memory integer sorting, built on OpenAI's tape-multiplication
      construction.
    - So the premises of AFKL19/FHLS19 are now believed false. Relevance: [MM]'s bound is a "coding cannot help
      much" statement in the tensor-network model. It gives only (log)^σ with σ < 1/2, which is consistent with
      polylogarithmic coding gaps of small exponent. Experts will want to see this checked: a coding gap of
      (log n)^{c}, c > 1/2, realised by a circuit routing many permutations would conflict with the no-ports σ
      range (not with σ small).
- Element distinctness elsewhere:
  - Ben-Or, Ω(n log n) for algebraic decision trees (1983). [memory]
  - Ajtai, superlinear time for linear-space (R-way) branching programs / RAMs (1999; ToC 2005 for the Boolean
    version, which is for a different function). [web]
  - Beame–Saks–Sun–Vee, T = Ω(n√(log(n/S)/log log(n/S))) for randomized branching programs (FOCS 2000 / JACM 2003).
    [web]
  - Beame–Clifford–Machmouchi, element distinctness easier than sorting for randomized BPs: Õ(n^{3/2}/S^{1/2})
    (FOCS 2013). [web; the search summary garbled the authors, so do not cite names without checking; I use only
    BSSV in the note]
- Other lower bounds in the same release (lean/docs/379.md):
  - Abelian Fourier transforms: Ω(n√log n) binary linear gates and O_ε(n(log n)^{1/2+ε}), both in Lean; batched
    version in Lean.
  - Formal polynomial multiplication: lower bound Ω(Jn√log n) paper only; upper bound in Lean.
  - Integer multiplication on tapes: upper bound in Lean; Ω(n√log n) only under Weak ETH, in Lean.
  - VF ⊊ VBP ⊊ VP ⊊ VNP over every field (Lean).
  - Hamiltonian cycle / permanent: superpolynomial arithmetic bounds in Lean; the exp(c log²N/(log log N)²) bound is
    paper only.
  - ⌈n^{9/4}/2⌉ per-n bound: unformalised.
  - Family 378: superlinear circuit bounds for E^NP, infinitely often.

## 5. Risk check

1. **Already stated?** Not in the release (§1 grep). It could be stated in some other 2026 commentary we did not
   find. A quick web search for "list distinctness" together with "Boolean circuit" "nine fourths" found nothing.
   That is weak evidence, since the release is two days old. Mitigation: the note says "we did not find it stated".
2. **Misread model making the bound trivial?**
   - Volume ≥ number of exterior bits = N, so a bound of order N would be trivial. The claimed bound is
     N·w^σ, a superlinear factor.
   - Lean has constant 1 in front: t·n_w·w^η < m.
   - Nothing trivialises it.
3. **Circuits fail to embed with linear overhead?** No. Lemma E is elementary and mirrors Lean's DNet combinators.
4. **Input length?** n_w = 2w·2^w, confirmed in the LaTeX and in Lean `listBits`. log N ≈ w, so
   "(log N)^σ" is right.
5. **σ unknown / ineffective.** Must be said plainly. The headline is "Ω(N (log N)^σ) for some σ > 0".
6. **The theorem itself may be wrong.** The note must not imply we checked the proof. The Lean formalisation is in
   the cone of the headline theorem, which raises the stakes either way: if the Lean build is sound, the corollary
   holds; if the corollary is false, then a Lean theorem in the cone of `square_exponent` is false, so the build or
   its definitions are unsound.
7. **"First superlinear bound for P":** the in-world comparison is family 378 (E^NP, infinitely often). The real
   literature record is 3.1n. I am confident that, outside this release, no superlinear lower bound for an explicit
   function was known as of mid-2026.
8. **Wording about natural proofs and AFKL** must be careful. Done in the note.

**Confidence** that our reading is correct, i.e. that Theorem 2.2 as stated (and `manyList_full` as stated in
Lean) implies the Boolean corollary with the stated form: **≈ 95%**. The residual 5% is for a Lean/LaTeX convention
I misread. That the release does not state the corollary: ≈ 90%. That the corollary is *true*: this is the
correctness of the release, which we did not assess.
