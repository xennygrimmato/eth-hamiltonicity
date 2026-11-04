# Three recent Hexagon papers that overlap the project

4 Nov 2026. Read from the public abstract pages (hexagonmath.org/<id>) and the TeX sources
(hexagonmath.org/src/<id>v1). The JSON API (`/api/v1/works/...`) redirects to an ORCID sign-in, so
nothing came from it. The sources were read through a summarising fetch tool, not saved locally:
the scratchpad volume was full during the session. So the quotes below are as the tool returned
them. Every statement marked **[unverified]** concerns a part of a source I could not read in full.
None of the three papers cites this repository or any of our notes.

---------------------------------------------------------------------------------------------------

## 1. hexagon:2610.00692v1, de Brito (text by Claude), "The partition exponent in the graded pieces … is optimal for pieces of that shape"

Submitted 30 Oct, posted 31 Oct. cs.CC, math.CO. No Lean. Python checks (`rank_count.py`,
`lemma9_check.py`, `kernel_check.py`) in exact rational arithmetic.

### What it proves
* **Definition 2.1 (Theorem B's shape).** V = ⊕_{W≥0} V_W is graded and finite-dimensional in each
  degree. The data are arbitrary linear maps P_{x,s,i}: V_W → V_{W+s−h+i} and R_{v,s,i}, for
  i = 0..2h and s ∈ [−2h, 2h]. Only two conditions are imposed: (b) Q_s = 0 for |s| > 2h, and
  (c) Σ_s Q_s(x,v) = d[x=v]·Id on V_h. **Lemma 9(a) (the two-order identity) is not assumed.** Nor
  are locality and integrality.
* **Theorem 2.2 (count).** Set T_V(h) := Σ_{s=−2h}^{2h} Σ_{i=0}^{2h} dim V_{s+i}. Then
  |𝒳|·dim V_h ≤ T_V(h) ≤ (4h+1)·dim V_{≤4h}. The proof is subadditivity of rank: the term (s,i)
  passes through V_{s+i}, and the sum is d times a permutation-type matrix of rank |𝒳|·dim V_h.
  I checked the argument and it is correct.
* **Corollary.** If log dim V_{≤W} = (c+o(1))W^α with 0 < α < 1/2 and dim V_W is nondecreasing,
  then families of this shape exist at only finitely many weights h.
* **Proposition 3.1.** The costs are weight counts (certified dimensions, as in our §3.1), not
  true ranks.
  * (i) At the least admissible h, ρ = 2^{α−1} + o(1).
  * (ii) Wherever a family exists, ρ ≥ 2^{−α} − o(1).
  * (iii) Hence ρ ≥ max(2^{α−1}, 2^{−α}) − o(1) ≥ 1/√2 − o(1).
  * (iv) If (c) holds on all of V_h, then ρ ≥ 2^α/(2(4^α−1)) − o(1), which exceeds 1 for
    α < 0.357.
  * I re-derived (iv). Take λ ≤ f(4h) − f(h) = (4^α−1)f(h) from Theorem 2.2 and the cost
    2f(2h) = 2·2^α f(h) at s = 0. Then 4ρλ ≥ 2f(2h), which gives the stated value; at α = 1/2 it
    is exactly 1/√2.
* **"Rank-tight up to a polynomial factor".** T(h) ≈ h·p(4h) and p(4h) ≈ √3·h·p(h)², so
  T(h) = Θ(h²)·p(h)². The claim compares the **total** weight count with the floor p(h)² of the
  sum. It says nothing about the true ranks of individual pieces, and the "≈" steps are asymptotic.
* **Proposition 4.1 (sparse Heisenberg).** Take V_S = ℚ[t_s : s ∈ S] with S co-infinite, and
  single-mode operators t_n[r] = c_n(r)∇_{−r}, with arbitrary coefficients. If Lemma 9(a) holds for
  all s, then c_n(r)c_m(−r) = 0. The paper's words are "Lemma 9 fails on V_S with the paper's
  coefficients". The result covers one-part monomials only.
* **Squares.** For partitions into squares (α = 1/3), the inequality of Theorem 2.2 fails for
  every h ≥ 5891, by exact arithmetic.
* The paper states "The floor ρ ≥ 1/2 remains open."

### Relation to ours
* **Theorem 2.2 is weaker than our spread lemma in one respect and stronger in another. It does not
  give the same theorem.**
  * Our Thm 3.3 / Cor 3.4 (`rho-lower-bound.md`, committed 28 Oct, before them) gives
    ρ ≥ f(2h)/(2f(h)) ≈ 2^{β−1}. That is exactly their part (i)/(iii) branch 2^{α−1}. Our
    note left β < 1/2 open as hypothesis (G) / (O-G).
  * Their rank floor closes that case **for Theorem-B-shaped families**. With fixed spread 2h and
    the 2h+1 degrees s−h+i, a space with β < 1/2 either has no family (at the minimal weight) or
    costs ρ ≥ 2^{−α} > 1/√2.
  * The argument uses only (b) and (c). It needs no two-order identity, no locality and no vertex
    algebra. This is a technique we lack. It is short and should be added to `rho-lower-bound.md`
    §3 as a new result on (G), with citation. It removes the need for β ≥ 1/2 in Cor 3.4 within the
    shape.
* **It does not contradict `sparse-fock.md` Thm 2.1.** That theorem says every family of pieces is
  a graded two-order decomposition on every V_S, at +2 bits per piece. Those embeddings do **not**
  have Theorem B's shape: the degrees and the spread are not s−h+i over 2h+1 terms. So (O-G) in
  our general sense is still equivalent to `Exist ρ c` and still open. Their result is a statement
  about the shape, which their own title says.
* **Their Prop 4.1 overlaps our `sparse-fock.md` Thm 3.1 (29 Oct).** Ours says locality with any
  Laurent annihilator forces mode sets with bounded gaps. Ours is more general. Theirs is a direct
  computation for single-mode operators with free coefficients. Their abstract phrase "no choice of
  coefficients repairs it" holds only within single-mode operators: by our Thm 2.1, general linear
  maps on V_S do carry pieces.
* **Rank-tightness agrees with our §3.4 numerics.** Our numerics give true rank / count = 0.93–0.97
  per piece for h ≤ 10. Ours is per piece and numerical. Theirs is total and asymptotic. Neither
  rigorously lower-bounds per-piece true ranks, and both papers leave (O-T) open.
* **Wording point, not an error in the mathematics.** "The floor ρ ≥ 1/2 remains open" cannot mean
  the inequality itself. ρ ≥ 1/2 − O(log λ/λ) is a theorem from clause (a): our Cor 2.2 (rank
  inequalities R1–R2), and for any two-grouping schedule, `clique-evaluation.md` §4.3. The sensible
  reading is "whether ρ* = 1/2 is attained", or "whether ρ* < 1/√2". Our §2.2 shows that question
  cannot be settled by rank counting alone, which is consistent with them.
* **Our `clique-evaluation.md` §4.3 has no counterpart in their paper.** That is the α′ ≤ 1 cap for
  every min-over-two-groupings recursion. Nor does our zero-mode loophole (O-H): their shape fixes
  the spread at 2h.
* **Lean.** They formalise nothing. Our `lean/EthFollowup/Barriers/SpreadLemma.lean` covers Thm 3.3
  in abstract form, using dimensions only. Their Theorem 2.2 has the same flavour: a dimension
  count plus rank subadditivity. It would be a cheap addition next to `SpreadLemma.lean` and
  `RankBounds.lean`.

### Cite in
* `research/permanent/rho-lower-bound.md`: §3.2 (Cor 3.4, hypothesis (G)), §5, §7 (O-G).
* `research/permanent/sparse-fock.md`: §0, next to Thm 3.1.
* `research/permanent/rate.md`: the law ρ = 2^{β−1}.

---------------------------------------------------------------------------------------------------

## 2. hexagon:2610.00594v1, Bhattacharjee, "Subexponential Weighted Counting and Exact Optimisation"

Submitted 28 Oct, posted 29 Oct. cs.CC, math.CO, cs.DS. Code at github.com/creelie/eCon v1.4.0
(Zenodo 10.5281/zenodo.23718560). **No Lean**: the paper says OpenAI's Lean "is not used here".
The text is mixed human and AI; Claude Code is listed among the tools.

### Exact claims
* **Main theorem.** Factor systems on n Boolean variables, ≤ cn factors, scope ≤ k, valued in a
  commutative ℚ-algebra 𝒜. Time poly(n)·2^{O_{k,c}(ρ(n))} operations in 𝒜, with
  ρ(n) = n(log log n)²/√log n. That is a (log log n) factor worse than OpenAI's rate, which the paper
  says it does not remove.
* **Max-k-SAT and Max-Cut.** m ≤ cn constraints, integer weights in [0, Ω]. Time
  poly(n, Ω)·2^{O(ρ(n))}. The output is the optimum, the number of optima and the full profile.
  Max-Cut also gives bisections.
* **Introduction only [unverified]:**
  * Max-Cut at average degree o(√(log n / log log n)).
  * Dense graphs near blow-ups of small graphs.
  * Tutte on (x−1)(y−1) = q for bounded-degree graphs and positive integer q. This includes the
    chromatic and flow polynomials at q and q-state Potts. The Tutte polynomial as a polynomial in
    q is explicitly excluded.
  * Ising/Potts density of states.
  * Minimum distance and ML decoding of sparse parity-check codes.
  * "Every problem in SNP" is in SE.
* **Vertex Cover.** Nemhauser–Trotter / Chen–Kanj–Jia kernel to ≤ 2k vertices, then
  τ = n′ − α(G′) by the independence-polynomial routine, which adds degree branching. Time
  2^{O(k(log log k)²/(log k)^{1/4})} + poly(n).

### Mechanism: white box, not black box
They reproduce OpenAI's algorithm (§§3–4) and **run it over truncated polynomial rings
ℚ[W]/(W^N)**. Their words: "every step of the algorithm that is used below is" OpenAI's. They add
their own branching on frequent variables and, for the independence polynomial, on high-degree
vertices.

So the poly-weight results are **not** a corollary of OpenAI's top-level theorem. Our row B15
(`fine-grained-map.md`, survey-note row B15) stands as written. It says that from the Main Theorem
alone we get unweighted or O(1)-bit weights. Poly(n) weights cost O(n log n) Tseitin variables,
and a counter at rate n(log log n)²/√log n on n log n variables is not 2^{o(n)}.

What their paper adds is a **second, independent route** to poly weights. It changes the import:
it needs the white-box claim that OpenAI's steps are ring-agnostic. Our route is (H_A), Anthropic's
network theorem with Kronecker weights (`tsp-theorem.md` §2.2).
* Q[W]/(W^N) is the same device as our Kronecker substitution. Kronecker substitution is the
  integer encoding of that ring, so this is no new idea.
* The new part is the claim that **OpenAI's** engine, and not only Anthropic's network, tolerates
  ring values. It is useful to us only if we audit OpenAI's algorithm for steps that are not
  ring-safe: comparisons, divisions by non-units, or anything that inspects values. I did not do
  that audit.

### Overlap and priority
| claim | ours | theirs | relation |
|---|---|---|---|
| Max-Cut / Max-k-SAT, O(n) constraints, poly weights | via (H_A) and Kronecker, informal (`fine-grained-map.md` l.149; survey l.418) | white-box OpenAI over a ring, poly(Ω) | same conclusion, different engine; theirs posted first (29 Oct), our map rows are from 4 Nov |
| unweighted / O(1)-bit, counts by value | B15, from Main Theorem Cor 6, black box | covered as Ω = O(1) | ours is the weaker import (black box) |
| Tutte on H_q | `tutte-plane.md` Thm P1 (note dated 29 Oct, committed 30 Oct 00:07): m edges, whole restriction T_G\|_{H_q}, uniform in q, 2^{O(m log(q+1)/√log m)}, also log q = o(√log n) | bounded degree, positive integer q [unverified detail] | ours is stronger: m = O(n) not bounded degree, the whole hyperbola, explicit q-uniformity, and the y = 1 line. Theirs was public first, so cite as independent and earlier |
| TSP / HC / ATSP with weights | `tsp-theorem.md` TSP-1, TSP-2 **machine-checked** in Lean (`theoremTSP`, `theoremATSP`) | not treated | ours only |

### Gaps and errors
1. **Hidden blow-up in the number of weight functions.** The budget theorem's algebra has
   dimension ∏ N_i ≤ (1+nΩ)^{s+1}, exponential in s, but this is hidden in "constants depending
   only on s".
2. **Knapsack inconsistency.** The knapsack corollary states poly(n, Ω^{s+1}), while the theorem
   gives poly(n, (1+nΩ)^{s+1}).
3. **Pseudo-polynomial only.** All bounds are pseudo-polynomial in Ω (and E_max for Ising). The
   corollaries do not say that exponential weights are excluded.
4. **SNP.** The claim is right only with IPZ's measure (size of the witness relation, under SERF
   reductions), not input length. Check how they state it [unverified].
5. **Vertex Cover depends on the unchecked density theorem.** The kernel G′ is dense, so the result
   rests on the degree-branching / density theorem (average degree o(√(log n/log log n))). That
   theorem's c-dependence I could not see. The (log k)^{1/4} exponent is consistent with branching
   at a slowly growing degree threshold, but it is unverified.
6. **Garbled sentence.** In the bounded-occurrence proof, the sentence "λ^β+1 ≤ λ^{β+1} is not
   needed" is garbled.
7. **Thresholds.** n_0(β) is never made explicit. "Theorem explicit" needs log n ≥ 2^{30} log log n.

### Cite in
* `research/fine-grained-map.md` B15 and l.149.
* survey-note rows B15 and B17, and l.393 and l.418: note that the paper is independent and
  white-box, and that it removes (H_A) for poly-weight Max-Cut / Max-k-SAT if OpenAI's internals
  are ring-safe.
* `research/tutte-plane.md` §0.
* `research/tsp-theorem.md` §2.2, as a parallel weighted-counting route.

---------------------------------------------------------------------------------------------------

## 3. hexagon:2611.00004v1, Nguyen (approach and Lean by "GPT 6.1 Sol"), "A Sublinear Treewidth Exponent for Binary Constraint Satisfaction"

Submitted 1 Nov, posted 2 Nov. cs.CC.

**Lean.** The paper reports Lean 4.33.1 with 82 downstream modules and a 633-module upstream
closure.
* Imported, not proved: the recursion and grouping theorems (Prop 3.1, from Anthropic's
  formal-math `eth`, rev 16a5ce4), OpenAI's spectral certificate, and the native simulation bound.
* No sorry count is given for the central endpoints.
* Not all 1050 upstream modules were replayed.
* The link between `MarxConjecture.not_statement` and Marx's text is informal.

### Exact claims
* **Theorem 1.2.** For complete-table binary CSP with k ≥ k_Δ variables, domain D ≥ 2, primal max
  degree ≤ Δ and length L: exact **counting** of solutions in time A_Δ·L^{p_Δ}·D^{C_Δ k/√log k}.
  The constants depend on Δ only.
* **Domain-uniform bound.** It holds for arbitrary relations R_ab ⊆ [D]² (0/1 tables). The count is
  unweighted. The imported engine supports integer weights, but the theorem is not stated for them.
* **Exponent.** It comes from the imported recursion e_j ≤ A_0/√log₂ K_j, an upper bound. **Nothing
  beyond Anthropic's 1/√log K**: no Θ claim, no improvement.
* **Marx conflict.** Graphs H_n from OpenAI's spectral port family have bounded degree and
  N_n/16 ≤ tw+1 ≤ N_n, so tw = Θ(k). The bound gives ‖I‖^{O(tw/√log tw)}, which contradicts the
  **literal** text of Marx 2010 Conj. 1.4, quoted as having no ETH hypothesis. They keep Marx's
  ETH-conditional Thm 1.3 as "valid", but do not say plainly that the refutation is of the literal
  form only.

### Relation to ours
* **Theorem 1.2 is the same mechanism as our `tutte-plane.md` Thm P1.** Both apply Anthropic's
  network engine with log D (or log q) label bits per edge.
  * Cost: 2^{O(U/√log U)} with U = O(Δ k log D), hence D^{O(k/√log k)}. The constants are uniform
    in D because the engine's rate is in U and the tables are reached by queries.
  * Their "domain-uniform" is our "uniform in q".
  * Their bounded-degree hypothesis is our m = O(n): the engine's exponent is in total label bits
    ~ |E| log D, so it is in k only when |E| = O(k).
  * On a dense primal graph this is our (K,λ)-clique problem with λ = log D. The cost
    2^{e_K K² λ} = D^{e_K K²} is not D^{o(k)}.
  * **They get nothing for `clique-evaluation.md`.** They do not touch dense or complete primal
    graphs, and they do not move e_K.
  * Δ enters only through the row capacity P = Δ·b·s (b = bits(D)) and the constants. The paper
    never says what breaks for unbounded Δ; the reason is the label-bit count above.
* **Tutte plane: nothing beyond P1, and less than P1.**
  * With D = q and tables [σ_a ≠ σ_b], their theorem gives the chromatic polynomial at integer q on
    bounded-degree graphs in q^{O(n/√log n)} = 2^{O(n log q/√log n)}. That is one point
    (1−q, 0) of H_q.
  * Their theorem does not cover:
    - weighted Potts tables (1+v[σ_a=σ_b]),
    - the Kronecker decoding of the whole of T_G|_{H_q},
    - the line y = 1,
    - m = O(n) with unbounded degree.
  * Our P1 already has all of these, with the same exponent m log(q+1)/√log m. So it adds no
    citation-worthy new case. Cite it as an independent instance of the same q-uniform bound.
* **Treewidth and the survey.** Our survey says "Nothing parameterised by treewidth or pathwidth"
  (survey-note l.422), and row B20 has "binary CSP ∉ f(G) n^{o(k/log k)}, premise refuted". Nguyen
  gives a **conclusion-side** statement for bounded-degree classes: binary CSP beats treewidth by a
  √log factor. So row B20 should say "premise refuted; on bounded-degree classes the conclusion
  fails at the √log scale (Nguyen, conditional on the imported engine)". Line 422 needs the same
  qualification.

### Gaps and errors
1. **The Marx "counterexample" is to the literal unconditional text.** An unconditional
   ‖I‖^{o(tw)} lower bound would imply P ≠ NP, so the intended form is ETH-conditional, and that
   form is vacuous once ETH is false. The substantive content is the algorithm. It remains a gap
   against Marx's ETH lower bound o(tw/log tw): √log versus log.
2. **Inconsistent constants wording.** The "fixed before k" constants use F_Δ(k) = F·36^p·72^{β(k)},
   which depends on k. It is absorbed into f(G), so the theorem survives, but the wording is
   inconsistent.
3. **The D = 2 case is not new.** It gives #IS on bounded-degree graphs in 2^{O(k/√log k)}. That
   already follows from #ETH-refutation corollaries (Anthropic Cor 6–7; survey row B17).
4. **The separator lemma is only sketched** (escaping mass ≤ σ, stationarity bookkeeping).
5. **Notation clash.** Δ is used for the port-set size |𝒟| in the graph family, separate from the
   degree bound.

### Cite in
* survey-note row B20 and l.422.
* `research/tutte-plane.md` §0 (P1), as independent; it does not give priority over us, since it is
  dated after us.
* `research/permanent/clique-evaluation.md` §4.5 (Marx barrier), adding the bounded-degree form.

---------------------------------------------------------------------------------------------------

## 4. Actions
1. `rho-lower-bound.md` §3 and §7: add de Brito's rank floor (Thm 2.2) as closing (G) for
   fixed-shape families. Keep (O-G) open in the general (sparse-fock Thm 2.1) sense. Consider a
   Lean lemma next to `SpreadLemma.lean`.
2. Survey-note rows B15, B17, B20 and l.418, l.422: add Bhattacharjee (independent route to poly
   weights, white-box OpenAI, unrefereed, no Lean) and Nguyen (treewidth conclusion on
   bounded-degree classes).
3. `tutte-plane.md` §0: cite Bhattacharjee (public 29 Oct, before our 30 Oct commit; weaker scope as
   stated) and Nguyen (one point of H_q, bounded degree).
4. Optional: audit OpenAI's algorithm for ring-safety. If it is ring-safe, our B15 could carry poly
   weights without (H_A).
