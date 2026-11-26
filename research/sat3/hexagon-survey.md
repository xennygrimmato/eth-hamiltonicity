# Hexagon survey for the 3-SAT engine work (27 Nov 2026)

Scout report. Everything below was read from the Hexagon catalogue (hexagonmath.org) and the PDFs it serves.
Nothing here is refereed. Almost every paper listed declares itself "primarily AI-generated", and several say
that no human has checked any of their content (the declarations are quoted in the table). Status tags: **[read]**
means the full text was read for the parts summarised; **[abs]** means abstract and provenance only.

## Usable now (summary)

1. **Recursive composition of crossing identities attains the Euclidean value on k wires with 2^{k−1} cuts**
   (hexagon:2611.01066, Sra, Lemma 4.2 + Lemma 4.1). Crossing decompositions of two groups of wires are substituted
   into one two-factor crossing. The result is an identity for k wires jointly, with exponent ‖β‖₂, i.e. value 1/√k
   for k equal wires. A plain tensor product of crossings gives only √2·⌊k/2⌋. It has integer coefficients and
   holds over every field. This is the only multi-wire, non-product piece construction I found. Whether it fits a
   p-net level (merges are partitions of nodes, not transversal cuts of independent wires) is the question for us;
   see §c.1. Already flagged to main.
2. **Khoruzhii's integral (fermionic) crossing lemma** (Lemmata repository, not Hexagon; cited by 2611.01066 and
   2611.00994). This is App. B of the 3-SAT paper with the bosonic Fock space replaced by an exterior algebra, so
   strict partitions into half-integer modes take the place of partitions. Coefficients are in ℤ and it works over
   every field with unit normalisation (App. B needs h!), still at ρ = 1/√2. Useful for anything we do in
   characteristic p (result 4 of `ports/README.md`), and as the two-factor input to item 1.
3. **A conditional two-merge floor matching our bimedian result** (2611.01066 Thm 3.2 / Cor 3.3). Assuming
   OpenAI's Euclidean price theorem (EP), any grouped decomposition of the two-wire identity has log rank
   ≥ √((log n)² + (log m)²) − O(√log). This is ρ ≥ 1/√2 for every two-merge piece family, with explicit finite-size
   constants and for border rank. Proof: put the terminals at ±e_i and the hubs at ±t·v_ε. It overlaps our
   unconditional CAT(0) bimedian statement (§e).
4. **Two-merge barrier literature is now dense.** Besides Majdoddin, there are de Brito 2610.00692 (graded pieces of
   App. B shape: α = 1/2 is optimal; ρ ≥ max(2^{α−1}, 2^{−α})) and Fradj 2611.00627 (Kleinian-code graded spaces:
   window cost ≥ 1/√2 + η_J, strictly). The project's own barrier paper 2611.00149 is also on Hexagon. All of these
   concern two merges or grids; **none touches three merges, nets or Latin squares.** The window for net engines in
   `notes.md` is not addressed by anything on Hexagon.
5. **Lean infrastructure worth taking:**
   - NativeTrust (2611.00373, github.com/GasStationManager/ReplaceNativeDecide): re-proves `native_decide` facts in
     the kernel. This bears directly on the ≈365 auxiliary axioms of our MC = 7 proof, though `bv_decide` facts are
     a separate question (see §d).
   - The F₂ matrix-multiplication rank certificate checkers of Tomar (2610.00548, 2611.00372, 2611.00375), built on
     Rudich–Rousseau's Lean formalisation of R(⟨3,3,3⟩) ≥ 22.
   - The Mathlib-Turing-machine time-bound endpoints of the factoring note 2610.00600 (Palomar entry; 13-line
     statement).
6. **Nothing improves or proves optimal the 3-SAT exponent.** Nothing decides flat/contracting or ports. Nothing
   pre-empts MC(2×2, F₂) = 7, the K_{2,m} rates, 3/√10, or exact twin-prime counting.

---

## (a) Access

- The site is **hexagonmath.org** ("Hexagon", public beta, Hexagon Mathematics Foundation). I reached it directly
  with no restriction: plain `curl` worked, while Python's urllib got HTTP 403 (user-agent filtering).
- **JSON API:** `https://hexagonmath.org/api/v1` (OpenAPI at `/api/v1/openapi.json`). `GET /api/v1/works?limit=100`
  with cursor pagination returned the **whole catalogue: 1638 works**, from 1 Sep 2026 to 26 Nov 2026. Of these,
  1600 were posted from 1 Oct on: 940 declare "no-human-author-claimed", 556 "mixed", 142 "human".
  `GET /api/v1/works/{id}` returns the provenance text, bibliography and `formalizations` (Palomar links).
  `/pdf/{id}` and `/src/{id}` serve the PDF and the source. Our earlier note `research/hexagon-related.md` (4 Nov) says
  the API redirected to ORCID sign-in; it now works anonymously. There is also an RSS feed (`/rss/all`) and an MCP
  endpoint (`/mcp`, not used).
- **Method:** I downloaded all 1638 records. I filtered the 1600 recent ones by subject (cs.CC, cs.DS, cs.LO, cs.DM,
  cs.FL, quant-ph, …) and by keywords (SAT, ETH, tensor, spectrum, price, CAT(0), Latin, matrix multiplication, Lean,
  …), which left 473 candidates. I read every candidate title, the relevant abstracts, and the full text of nine
  papers (marked [read]).
- **"Lean" filter:** the records have a `tools` field, and 82 recent works list Lean. The `formalizations` field is
  almost always empty: only 2610.00600 has a Palomar entry. In practice, Lean repositories are linked in the
  provenance or the paper text.
- **Not accessed or not available:**
  - the Lean overlay of 2611.00004 (an "artifact" is mentioned, but no public URL is given);
  - the Lean of 2611.00954 (VP ≠ VNP) and of 2610.00577: not re-read, because the project already uses them;
  - the OpenAI 24 Nov preprints themselves: not re-read, known to the project.
  The external Lemmata page for Khoruzhii's crossing lemma (lemmata.iol.berlin/crossing-decomposition, v. 4 Nov) was
  read.
- The Tulsyan papers (2610.00672, 2611.00088, 2611.00090, 2611.00115, 2611.00116, 2611.00149) cite
  github.com/xennygrimmato/eth-hamiltonicity, `lean/EthFollowup/...`. **These are this project's own deposits**, so
  they are listed only for completeness.

## (b) Table of relevant recent papers

Authorship declaration codes:
- **AI** = "primarily AI-generated";
- **mix** = "mix of human-written and AI-generated";
- **hum** = human-written.

The human-understanding declaration follows the slash: all, some or none.

### Engines, ETH and counting

| id | title | authors (as listed) | date | decl. | Lean? | relevance |
|---|---|---|---|---|---|---|
| 2610.00577 | A 2^{o(n)} Time Algorithm for 3-SAT | Anthropic (org.) | 27 Oct | AI/some | yes: anthropics/formal-math `eth/` (MainResults.lean: ETHIsFalse, MainTheorem) | the source; known |
| 2610.00692 [read] | The partition exponent in the graded pieces of the Claude 3-SAT algorithm is optimal for pieces of that shape | Carlos Stein Naves de Brito (NightCity Labs) | 31 Oct | AI/some | no (SymPy checks) | two-merge barrier for App.-B-shape graded pieces; known (`hexagon-related.md` §1) |
| 2611.00627 [read intro] | Thermodynamic saturation and prescribed window barriers for Kleinian-code graded spaces | Mohamed Fradj | 19 Nov | AI/some | no (Arb certificates; github.com/MFRADJ/graded-window-barrier-certificates) | window cost ≥ 1/√2 + η_J for code-graded spaces; two-merge only; **new to us** |
| 2611.00149 | What the ETH refutations do not give: barriers for the counting engines, with machine-checked lemmas | Vaibhav Tulsyan | 6 Nov | AI/some | yes (project repo) | our own |
| 2610.00672 / 2611.00088 / 2611.00090 / 2611.00115 / 2611.00116 | Hamiltonian cycles, Euler circuits, quantum amplitudes, class numbers, parity of π(x) | Vaibhav Tulsyan | 31 Oct – 5 Nov | AI/some | yes (project repo) | our own |
| 2611.00004 | A Sublinear Treewidth Exponent for Binary Constraint Satisfaction | Troy Tri Nguyen | 2 Nov | AI/some | Lean 4.33.1 overlay of 82 modules on both labs' code; not publicly linked. Top theorem `not_statement` (negation of Marx's Conj. 1.4) | domain-uniform count D^{O(k/√log k)} for bounded-degree complete-table CSPs from Anthropic's recursion; known (`engine3-literature.md`) |
| 2610.00574 | On counting satisfying assignments via polynomial separation | Scott Kominers (Harvard / a16z) | 27 Oct | mix/some | no | exposition of OpenAI's engine (deformation + Hermite interpolation) |
| 2610.00572 | Some exposition of "The ETH Is False" | Ryan O'Donnell (CMU) | 27 Oct | AI/none | no | exposition of OpenAI's parity polynomial |
| 2610.00594 | Subexponential Weighted Counting and Exact Optimisation | Deep Bhattacharjee | 29 Oct | mix/some | no (github.com/creelie/eCon) | OpenAI's engine extended to weights in commutative ℚ-algebras: Max-k-SAT, Tutte on hyperbolas, SNP. Consequence-type |
| 2610.00600 | Deterministic Factoring in Time N^{o(1)} | Isaac Rudich, Louis-Martin Rousseau (Polytechnique Montréal) | 29 Oct | mix/some | yes: Palomar PALOMAR-2026-10-28-000015; 13-line Mathlib-only statement (a TM computes the least prime factor in C_k·2^{n/k} steps); ≈35k lines; re-proves only the needed part of the engine | Lean TM-time template (§d) |
| 2610.00613 | What Does the Refutation of ETH Mean for Learning Theory? | Xiaoyu Li (UNSW) | 29 Oct | AI/some | no | consequences only |
| 2611.00132 | Fast Attention after SETH | Xiaoyu Li | 6 Nov | AI/some | no | consequences only |
| 2611.00388 | Which Fine-Grained Lower Bounds Survive the Refutation of 3SUM and APSP? | Tejasvi Singh Tomar | 12 Nov | mix/all | no | cites Majdoddin's 3SUM extension (ε < 0.172 → 0.17843); not SAT |

### Tensors, spectrum and prices

| id | title | authors | date | decl. | Lean? | relevance |
|---|---|---|---|---|---|---|
| 2611.00954 | VP ≠ VNP over every field | Anthropic (org.) | 23 Nov | mix/some | yes (Lean release; `thm_alt` etc.); one numbered statement not formalised (p. 3) | K-AN; known |
| 2611.01066 [read] | Euclidean Tensor Prices and Sharp Multiquadratic Composition Bounds | Suvrit Sra (TU Munich) | 25 Nov | AI/**none** | no | **§c.1**: k-wire composition; conditional two-merge floor |
| 2611.00994 [read §1–3] | Sharp exponential circuit lower bounds for the noncommutative permanent and determinant | Yilin Liu | 24 Nov (v2 26 Nov) | AI/none | no | planar prices: "two-site uncrossing inequality"; three-interval cut; regular r-gon placements. §c.3 |
| 2611.00972 [read §1–2] | A uniform exponent bound for asymptotic tensor rank | Yilin Liu | 24 Nov | AI/none | no | every relaxed spectral point has a CAT(0) realisation with a one-hub (Fermat–Torricelli) bound, Lemma 2.1, from AN Prop. A.7/C.3. Asymptotic rank ≤ d^{ω/√3}. §c.4 |
| 2611.01073 [read] | An exponential lower bound on the exact stabilizer rank | Yinchen Liu, Huanyi Zhou (Tsinghua) | 26 Nov | mix/all | no | an application of OpenAI's Euclidean prices: a spectral point with d(EPR) ≤ 2/3 on a triangle and a witness above 2^j |
| 2611.01113 | The tensor rank of the permanent | Yilin Liu | 26 Nov | AI/none | no | row-factor tensor rank of per_n = 2^{n−1} (char ≠ 2); Glynn optimal |
| 2611.01116 / 2611.01115 | Border rank of the five-row permanent (16); border Waring rank of (x₁⋯x_n)^{d−1} | Yilin Liu | 26 Nov | AI/none | no | peripheral |
| 2611.00433 | Explicit determinantal formula for Sinkhorn limits of matrices and tensors | Shankar Sivarajan (U. Michigan) | 15 Nov | AI/all | no | scaling limits; peripheral to quantum functionals |
| 2611.01046 | Counterexamples to the positivity and saturation hypotheses of GCT VI | Floris Alderliefste | 25 Nov | AI | no | peripheral |
| 2611.00911 | Tensor semistability from rectangular Specht lattices | Sihan Chen | 23 Nov | AI/some | no | peripheral |

### Matrix multiplication, circuits and SAT certificates

| id | title | authors | date | decl. | Lean? | relevance |
|---|---|---|---|---|---|---|
| 2610.00548 | The rank of 3×3 matrix multiplication over F₂ is 23 | Tejasvi Singh Tomar | 26 Oct | mix/all | yes: Lean 4 certificate checkers in two builds (compiled; kernel-only, standard axioms only); zenodo 10.5281/zenodo.23047901 | §d, §e |
| 2611.00372 | The rank of 4×4 matrix multiplication over F₂ is at least 35 | Tejasvi Singh Tomar | 12 Nov | mix/all | yes (Lean 4.30, one compiled evaluation); zenodo 23749576 | §d |
| 2611.00375 | Local optimality of rank-47 schemes for 4×4 MM over F₂ | Tejasvi Singh Tomar | 12 Nov | mix/all | yes; github.com/jakobmoosbauer/flips | §d |
| 2610.00671 | Improved basis-change transformations for 2×2 MM | Hugo Nielsen (KU Eichstätt) | 31 Oct | hum/all | no | peripheral to MC = 7 |
| 2611.00373 | Re-proving native_decide facts in Lean's kernel | Tejasvi Singh Tomar | 12 Nov | mix/all | yes: github.com/GasStationManager/ReplaceNativeDecide | §d |
| 2611.00389 | Subplanes of order 3 and maximal arcs in projective planes of order 12 | Tejasvi Singh Tomar | 12 Nov | mix/all | certified SAT refutations; zenodo 23717956 | uses Egan–Wanless classification of triples of MOLS of order 9; Latin-square data, not engines |
| 2611.00873 | A Steiner triple system with a broken chromatic spectrum | Peter Graham | 23 Nov | AI | DRAT-trim + separate checker | SAT-certificate pipeline example |
| 2610.00152 | A Verified Constructive Reduction of the Cook–Levin Theorem in Lean 4 | Jonathan f(n) Reed | 8 Oct | mix/all | Lean v4.28.0 (no repo link found) | TM → CNF in Lean; §d |
| 2611.01127 | Formally verified asymptotic optimality of parallel find-any search … in Lean 4 | Robert Kadlec (Masaryk) | 26 Nov | AI/some | Lean 4.35 | peripheral |
| 2611.00634, 2611.00652, 2611.00696 | ROABP PIT; deterministic almost-linear matching/flow; sparsification from barriers | Yilin Liu | 19–20 Nov | AI/none | no | peripheral (LP/flow; not strongly polynomial LP) |
| 2611.00439 | Average sensitivity of PTFs (edge comparison 3/2) | David Niedbala Giraudin | 15 Nov | AI/none | no | refines an OpenAI weighted-grading argument; peripheral |

Searched with no relevant hit:
- CAT(0) or metric geometry of the spectrum, beyond 2611.00972;
- weak ETH or Stearns–Hunt;
- multiplicative complexity / AND gates;
- K_{2,m} or Okamura–Seymour rates;
- twin-prime counting (J. Ni's paper is not on Hexagon);
- Latin squares or nets in an engine context.

## (c) The papers that matter for focus 1

### c.1 hexagon:2611.01066 (Sra). Read in full.

**What is proved.** There are two external inputs, and the author states that he verified the proof of neither:
- **(EP):** OpenAI's 24 Nov Euclidean price theorem. On a finite site set S ⊂ ℝ^d there is a spectral point F_S with
  H(T) = W(S)·log F_S(T), where W is the mean width. A q-wire of length ℓ costs ℓ·log q.
- **(CR):** Khoruzhii's crossing lemma.

The results:
- **Lemma 2.1 (sum bound).** Under (EP), H(Σ_j T_j) ≤ max_j ℓ_j + W(S)·log J. This also holds for Zariski closures,
  via a symmetric-power span argument.
- **Theorem 3.2 (finite bound, under EP).** Take any decomposition of I_n = ⊗_i I_{n_i} (k wires) into terms each of
  rank r_ε across one of the p = 2^{k−1} transversal cuts ε. Write a_i = log n_i, A = Σ a_i, L = ‖a‖₂, and let W_k be
  the mean width of {±e_i}. Then for 0 < t ≤ L/A:
  - log r_max ≥ L − At/2 − W_k·log p/(2t);
  - log Σ r_ε ≥ (same) + log p.
  The proof puts terminals at ±e_i, hubs at ±t·v_ε with v_ε = L^{−1}·Σ ε_i a_i e_i, spokes of dimension n_i, and a
  central wire of dimension r_ε.
  For k = 2 this is the two-merge crossing floor ρ ≥ 1/√2 at finite sizes (Cor. 3.3, eq. (3.6)):
  log SOS(n,m) ≥ √((log n)² + (log m)²) − √(2√2·log(nm)).
- **Lemma 4.1 (under CR).** P_F(⌈n^a⌉, ⌈n^b⌉) ≤ n^{√(a²+b²)+o(1)}, with integer coefficients, over every field.
- **Lemma 4.2 (composition, unconditional, over every field, no division or signs).** Split the k wires into groups
  A₀ and B₀. Then P_F(n) ≤ 2^{k_A+k_B−2} · P_F(P_A, P_B). Mechanism: take a cut-summand Σ_α U_α ⊗ V_α of rank r for
  group A and Σ_β X_β ⊗ Y_β of rank s for group B. Their product is a linear image of the two-wire identity I_r ⊗ I_s.
  A crossing decomposition of I_r ⊗ I_s then maps to terms rank-one across "cut(A) ∪ cut(B)" or
  "cut(A) ∪ complement(cut(B))", both transversal. Induction gives **exponent ‖β‖₂ for every fixed k**. A tensor
  product of crossings on disjoint pairs gives only (√2 + o(1))⌊k/2⌋ + (k mod 2) (§5).
- **Theorem 1.1 (under EP + CR).** The exponent of k-fold multiquadratic composition, PT rank and products of forms
  is exactly ‖β‖₂ (fixed k), also in the border model. Further: SOS_ℂ(n,n) = n^{√2+o(1)}, and noncommutative
  circuits for Perm_N and Det_N have size ≥ 2^{N/2−O(√(N log N))} (Thm 6.2, with Liu's interval cut).
- §7: "nothing here uses or decides the contracting hypothesis of [VP ≠ VNP] over ℚ."

**Technique.** Hub placement in the Euclidean price, and recursive substitution of crossings.

**How we could use it.**
1. **Template for a non-product multi-way identity.** Lemma 4.2 is exactly a construction in which different wires
   are coupled through the rank spaces of earlier decompositions. It is not a product over bundles, so it is not
   obviously inside Majdoddin's Prop. 4.23 class (filter F4: "a three-way identity must couple different bundles";
   this does). It attains the Euclidean (flat) value on its configuration. That configuration is k independent
   wires with all 2^{k−1} transversal cuts: value 1/√k with p = 2^{k−1} "merges", far from balanced in our sense.

   The concrete test: write a 3-net level (or Δ₃) in the form "groups of wires + transversal cuts". Each merge of
   the net must be a union of transversal cuts the composed identity can use. For example, compose a row/column
   crossing with a crossing whose second factor is the rank space of the first, so that the diagonal class is
   served by the nested cut "cut(A) ∪ complement(cut(B))". Then compute the price-method value of the resulting
   cost profile against our floors 0.6124 and 2/3.

   Caveat: in Lemma 4.2 every term is rank-one across a bipartition of the 2k wire ends. A net merge is a partition
   into g groups. So the cost of a composed term in a merge is the rank across the coarsest bipartition compatible
   with that merge, and it need not be small. I have not done this computation.
2. **Two-merge floor.** Theorem 3.2 (k = 2) with (EP) gives the two-merge crossing floor of 1/√2 at finite sizes and
   for border rank. Our `notes.md` §3 bimedian result gives the same unconditionally from CAT(0). Cite both; ours
   needs no EP. The method of Theorem 3.2 (hubs along the signed log-size direction) is also a ready recipe for
   finite-size floors on nets once a Euclidean placement of the net's nodes is chosen. Under EP every Euclidean
   placement is a price, so a net placement in ℝ^d gives flat floors unconditionally. The project already treats
   the flat floor as unconditional, so this only confirms it.

### c.2 Khoruzhii, "Crossing decomposition for subquadratic noncommutative circuits"

Lemmata repository, v1 2 Nov, last 4 Nov; not on Hexagon; read. Text at lemmata.iol.berlin/crossing-decomposition.

- **Theorem 2 (finite fermionic Fock identity).** E_L = Λ_ℤ(t₀..t_{L−1}) with modes of energy i + 1/2, plus a second
  colour u. M(ξ)_{I,J} = ε_J·[t_I u_J] K_ξ, where K_ξ = ξ(θ₀, …)·Π(1 + t_k u_k) and
  θ_m = Σ_k (C(k,m) t_k + C(−k−1,m) u_k). Then
  Σ_{r=1−h}^{h} (M_{−r}(η) M_r(T_{h,r}ξ) − σ_h M_r(T_{h,r}ξ) M_{−r}(η)) = λ_h(ξ,η)·Id on W_E for L ≥ E + h.
  This holds over ℤ: commutators for integer h, anticommutators for half-integer h.
- **Lemma 1 (integral crossing).** Let Q(T) be the number of strict partitions into half-integer parts with energy
  ≤ T. If Q(H) > 2Hn, then δ_ik δ_jℓ = Σ_{s≤r} ((A_s)_ij (B_s)_kℓ + (C_s)_iℓ (D_s)_kj) with integer matrices of size
  n × Q(E) and r ≤ 2H·Q(H+E). The normalisation is unit, not h!. Since log Q(T) ~ κ√T, this gives again ρ = 1/√2.
- **Use for us.** (i) A characteristic-free crossing piece (every field, integer coefficients) for the
  characteristic-p results. (ii) Together with de Brito: fermionic and bosonic Fock spaces both sit at α = 1/2,
  confirming that the square-root growth is forced for two-order graded pieces. (iii) It is the base case for the
  composition in c.1. Khoruzhii also has "A square-root bound for asymptotic tensor rank" (Lemmata 2610.00005, with
  Lean), which the project already lists.

### c.3 hexagon:2611.00994 (Liu, v2). Read §1–3.

Under OpenAI's planar prices:
- a "two-site uncrossing inequality" shows that the one-excitation (W-type) tensor attains its full mean-width price
  on every planar polygon;
- Lemma 2.1 (three-interval cut): a circuit's coefficient tensor is a sum of ≤ (N+1)³ tensors, each of low rank
  across three arcs whose triangle contains the centre;
- regular r-gon placements give coefficients r·sin(π/r)/π → 1.

**Use:** evaluations of explicit non-wire tensors under Euclidean prices. This is the kind of computation the
"interpolation gap" in `notes.md` §7 needs: spectral points on non-wire tensors, attainment via AN Thm A.6. It is a
lower-bound tool, not a piece construction.

### c.4 hexagon:2611.00972 (Liu). Read §1–2.

**Lemma 2.1:** for every relaxed spectral point φ on parties I and every T with local ranks r_i, there are points x_i
in a complete CAT(0) space with d(x_i, x_j) = log φ(wire_ij) and log φ(T) ≤ inf_y Σ_i log r_i · d(x_i, y). It is
proved from AN Prop. A.7 and C.3 by repeated midpoint insertion. It is a one-hub (Fermat–Torricelli) upper bound,
and the proofs use the CAT(0) variance inequality (line ≈319 of the text). This is the same toolkit as our floors:
it is an independent use of AN's CAT(0) theorem for prices, and its midpoint-insertion construction may help the
product-of-pods "is a price" step [D] in `notes.md` §4.

### c.5 hexagon:2611.00627 (Fradj) and 2610.00692 (de Brito)

Two-merge filters only:
- de Brito: Thm 2.2, |X|·dim V_h ≤ (4h+1)·dim V_{≤4h}; Prop. 3.1, ρ ≥ max(2^{α−1}, 2^{−α}). Already summarised in
  `research/hexagon-related.md` §1.
- Fradj: for isotropic Kleinian codes at fixed density h/m ∈ J, the central-window cost is
  ≥ 1/√2 + η_J − C_J·m^{−1/2}, with η_J > 0 but not evaluated (≈ 0.005 illustratively). As h/m → ∞ it saturates to
  1/√2 for codes of 2-rank ≤ m.

Effect on us: code- or lattice-graded spaces give no route below 1/√2 even for two merges. They are irrelevant to
nets unless someone grades a three-way identity by a code.

## (d) Lean libraries worth reusing

| source | what it provides | use for us |
|---|---|---|
| anthropics/formal-math `eth/` (commit 16a5ce4) | Mathlib Turing machines, explicit cost recursion (`ExplicitCost.recursionSolves`, `groupingExplicit`), pieces (`PiecesCounted.halfPieces`, `GeneralPieces.PartA.K_lt_le`) | known; 2611.00004 shows that a 633-module dependency closure suffices for the counting endpoints |
| 2610.00600, Palomar PALOMAR-2026-10-28-000015 | 13-line Mathlib-only TM statement; re-proves only the needed part of the engine in ≈35k lines, importing nothing from the labs | a template for a short, auditable TM-time statement if we ever claim a new exponent |
| 2611.00373 NativeTrust, github.com/GasStationManager/ReplaceNativeDecide | converts `native_decide` facts to kernel proofs (98.2% of 52,821 facts in 16 packages); a "kernel first" import; a source rewriter | our MC = 7 Lean proof has ≈365 auxiliary axioms. The two `native_decide` orbit checks are the natural target. The `bv_decide` cubes are LRAT-checked and are not covered by this tool, as far as the abstract says |
| 2610.00548 / 2611.00372 / 2611.00375 (Tomar), Rudich–Rousseau [RR26]; zenodo 10.5281/zenodo.23047901, 23749576, 21895176; github.com/jakobmoosbauer/flips | Lean-verified certificate checkers for substitution-method lower bounds on F₂ matmul ranks; ⟨3,3,3⟩ = 23 with a kernel-only build (standard axioms only); flattening arguments in Lean; ⟨n,m,p⟩ tensors over F₂ | matmul tensors and rank over F₂ in Lean: reuse the definitions next to our MC(⟨2,2,2⟩) = 7 and MC(⟨1,2,3⟩) = 6 |
| 2610.00152 | constructive Cook–Levin (TM → CNF) in Lean 4.28 | possibly useful for TM ↔ CNF glue; no repository URL found |
| 2611.00004 overlay (not public) | adapter from Anthropic's engine to finite-alphabet native machines; imports from both labs under one Lean version | ask the author for it if we need cross-lab imports |
| 2611.00146 | "Formalization of robust strictly positive real synthesis for fourth-order interval polynomials" (Lean) | interval polynomials; not checked whether it has reusable interval arithmetic |

Not found on Hexagon:
- a Lean library for the asymptotic spectrum or for CAT(0) spaces (beyond what is inside AN's VP ≠ VNP release);
- Latin squares or nets in Lean;
- LRAT checking other than Lean's built-in `bv_decide` path. 2611.00389 and 2611.00873 use DRAT-trim externally.

## (e) Overlaps with our own results

- **Bimedian / two-merge floor.** 2611.01066 Thm 3.2 + Cor 3.3 gives the two-merge floor ρ ≥ 1/√2 for every
  crossing decomposition, at finite sizes and for border rank, **conditional on OpenAI's EP**. Ours (`notes.md` §3)
  is unconditional via CAT(0) and also covers K₄ and the Euclidean cap E/√p for balanced configurations. Not a
  pre-emption, but it must be cited.
- **Euclidean cap / flat value attained.** 2611.01066 Lemma 4.2 shows that the flat value ‖β‖₂ is attained for k
  wires with all transversal cuts, by composition. If we state "flat floor attained" for any configuration,
  compare with it.
- **MC(2×2, F₂) = 7 AND gates.** No Hexagon paper on multiplicative complexity. Adjacent: tensor (bilinear) rank of
  ⟨3,3,3⟩ over F₂ = 23 (2610.00548, Lean-checked) and ⟨4,4,4⟩ ≥ 35 (2611.00372). These concern bilinear rank, not
  XOR-AND multiplicative complexity, so there is no overlap with "exactly 7". 2610.00548 does show that the
  substitution method plus Lean certificates is current practice.
- **K_{2,m} rates, 3/√10, Okamura–Seymour:** nothing on Hexagon.
- **Exact twin-prime counting in subexponential time:** nothing. The nearest are our own parity-of-π paper
  (2611.00116) and natural-boundary papers on prime-pair Dirichlet series (2611.00971, 2611.01112), which are
  unrelated.
- **Engine-barrier and two-merge window statements:** the project's 2611.00149 is cited by 2611.00627 (§1.3,
  Tulsyan [7]: Thm 4.3, Prop. 4.4) as prior work on the central-spread mechanism. So our earlier barrier work is
  known externally.

## Raw data

Scratchpad (not durable):
- `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/hx/works.json` (all 1638 records);
- `…/hx/cand.txt` (473 candidates);
- `…/hx/pdf/*.txt` (full texts read);
- `…/hx/kh.txt` (Khoruzhii page).
