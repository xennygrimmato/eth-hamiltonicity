# prior-barriers: is exponent > 1/2 of log n already excluded (or promised) by published work?

> **Correction, 27 Nov.** §0 item 3, §5.2 and §5.3 below are superseded by `q2-notes.md`: the metric statement
> "Q2" of §5.3 is false in every metric space (Lemma N there), and the dismissal of the restriction route in
> the last paragraph of §5.3 was wrong: OpenAI's HC Thm 3.1 does transfer to the clique wire tensor, by
> restriction with rotating star centres (Theorem T there, conditional on HC Thm 3.1; at a referee).

Reader's report, 26 Nov 2026. Nothing here is committed, machine-checked or refereed.

Tags: **[K]** quoted from a source, with location; **[R]** proved here in full (short); **[D]** derived here,
unreviewed; **[C]** conjecture or heuristic. "Line n" refers to the pdftotext file named at first use.

Texts used (paths relative to the session scratchpad directory, the one that holds `survey/oa` and `anth/`):

| tag | source | local text |
|---|---|---|
| OA-ETH | OpenAI, "The Exponential Time Hypothesis is False", 17/25 Oct 2026, https://github.com/openai/math/tree/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026 | `pb/oaeth/paper.txt`, `pb/oaeth/quantitative-reduction.tex` (fetched today) |
| AN-ETH | Anthropic, "A 2^{o(n)} time algorithm for 3-SAT", 26 Oct 2026, https://raw.githubusercontent.com/anthropics/formal-math/main/eth/paper.pdf (hexagon:2610.00577) | `pb/aneth/paper.txt` (fetched today) |
| AN-VP | Anthropic, "VP ≠ VNP over every field" | `anth/paper.txt` |
| EG, HC, FT, IM, MM | OpenAI family 379 (24 Nov 2026): Euclidean geometry; Hamiltonian cycle/permanent; Fourier transforms; integer multiplication on tapes; matrix multiplication 9/4 | `survey/oa/preprints/*/paper.txt` |
| MJ | R. Majdoddin, "Lowered crossover points of Anthropic's subexponential 3-SAT algorithm", arXiv:2610.41622v1, 30 Oct 2026 | `pb/arx/p.txt` (fetched today, read §§1, 4, 5 in full) |

Correction to the brief: `scratchpad/anth/paper.txt` is Anthropic's VP ≠ VNP paper, not its ETH paper. The ETH
paper was fetched separately. Both are used below.

---

## 0. Bottom line

**(B), with one sharply defined gap (C).** Nothing in the two labs' papers, in arXiv:2610.41622 or in any
follow-up found excludes a net engine (three or more merges per level) with exponent of log n above 1/2, under
any hypothesis. Nothing found states or suggests that it can be done either. No improvement of the exponent 1/2
has been published by anyone as of 26 Nov 2026.

What exists:

1. **Two merges are closed unconditionally** (given EG Thm 1.2): EG Cor. 6.2 is the sharpness of the crossing
   trade at √(t²+u²), i.e. ρ = 1/√2. [K + D]
2. **The proved floors that apply to net engines are far from 1/2.**
   - AN-VP Prop. E.10 (flat case; flats exist by EG Thm 1.2): every arithmetic circuit for the clique-wire
     polynomial f_{k,ℓ} has ≥ 2^{ℓk^{3/2}/16} gates. Per edge bit: e(K) ≥ 1/(8√K). This covers every oblivious
     algebraic algorithm, with any number of merges and any term sets, and allows polynomial decay. [K]
   - MJ: e(K) ≥ 1/log₂K for grid algorithms, ≥ (log₂K)^{−3} for balanced homogeneous two-merge algorithms; three
     or more merges are explicitly left open. [K]
   - Ours: conditional exclusion only above 0.7075 for three merges (sat3 Theorem S). [D]
3. **The "ports" lower bounds of OpenAI do not transfer.** Each of FT Thm 1.1/1.2, IM Thm 8.1/8.4, MM Lemma 4.1
   and MM Thm 2.2 bounds the size of **one** circuit, network or topology. The one result that handles a sum whose
   terms each have their own cut, HC Thm 3.1 (no ports ⇒ n^{Ω(d/√log d)}), is proved for a purpose-built tensor
   that nearly attains the star bound, not for wire tensors. [K + D]
4. **The gap (new observation, §5.3).** HC Thm 3.1 and Anthropic's engine have the same shape: for a
   set-multilinear polynomial of degree d on n variables per row, size n^{Θ(d/√log d)}. If HC's argument could
   be run on the complete-graph wire tensor, then *under no ports every oblivious algebraic clique-sum algorithm,
   net engines included, would have exponent ≤ 1/2*, and with IM Thm 7.1 the chain
   "exponent > 1/2 ⇒ ports ⇒ Weak ETH fails" would hold. The missing lemma is a metric statement (Q2 in §5.3).
   A two-line computation shows it is not excluded by the triangle inequality, and that it is borderline. [D/C]

So the improvement we are chasing is **not known** to be equivalent to refuting Weak ETH. The realistic reading:
under ports, 3-SAT is power-saving by a different algorithm and the engine question is moot; under no ports
(implied by Weak ETH in characteristic 0), the natural conjecture from HC is that 1/2 is the right exponent for
algebraic engines of every kind, and that conjecture is open at exactly one named step.

---

## 1. OpenAI's release

### 1(a) OA-ETH: the exponent, and no optimality statement

- [K, abstract] "our algorithm uses poly_k(n, m) space and runs in time (n + m)^{O_k(1)} 2^{n/(log n)^{1/2+o(1)}}."
- [K, Thm 1.1] time "(n + m)^{O_k(1)} 2^{O_k(n log log n/√log n)}"; for m ≤ Dn, "2^{O_{k,D}(n/√log n)}". "The
  rational interpolation argument in Section 6.4 gives the weaker exponent O_k(ρ(n)), where
  ρ(n) = n(log log n)²/√log n = n/(log n)^{1/2+o(1)}. Appendix D proves both bounds in Theorem 1.1 by tensor
  contraction."
- Why 1/2. [K, App. D.1, `quantitative-reduction.tex` l. 59–63] "With M wires and u retained valuation levels, the
  number of mode monomials is 2^{O(M/√u)}, and each monomial factors into contractions with at most M/8 wires. At
  recursion depth d, M = O(s8^{−d}) and u = Θ((log s)/2^d). The exponents therefore sum geometrically to
  O(s/√log s)."
  So the square root is a one-level law (monomials of bounded weight, a partition-type count); the recursion only
  sums a geometric series. In the main text it is the degree O(√·) of a polynomial that interpolates (−1)^j on a
  short interval (§1.1.5).
- **No lower bound, optimality statement or open problem about the exponent.** I searched `paper.txt` and the
  four TeX sources for optimal, barrier, cannot, best possible, improve, open, lower bound, Weak, conjecture: the
  only hits are in the related-work survey. The paper closes §1.1 with "Theorem 1.1 invites a renewed search for
  algorithms for problems whose known hardness results relied on ETH or SETH" [K, l. 325–327]. Nothing on ports;
  the word does not occur.
- Outside the paper: R. Williams, quoted by TechCrunch (27 Oct 2026,
  https://techcrunch.com/2026/10/27/frontier-ai-labs-say-their-models-refuted-the-exponential-time-hypothesis-what-does-that-mean/):
  "I also think that this is probably not the final answer either. I don't think that OpenAI's algorithm could
  possibly be the best algorithm you can get." [K] An opinion, with no argument attached.

### 1(b) Fourier transform and integer multiplication: what is lower-bounded, in which model, under what

**FT (unconditional, linear circuits).**
- [K, FT abstract] "The minimum number of binary linear gates for a finite abelian Fourier transform of order N
  is N(log N)^{1/2+o(1)}."
- [K, FT Thm 1.1] for the direct sum T of J Fourier transforms of order N:
  "c·JN·√log N ≤ C_K(T) ≤ C_ε·JN(1 + log N)^{1/2+ε}", where "C_K(T) [is] the smallest number of gates in an
  acyclic linear circuit computing a matrix T over a field K."
- [K, FT Thm 1.2] robust form: T in the Zariski closure of sums M + B + Z with M a linear system with feedback
  on s states, rank B ≤ βh, |supp Z| ≤ ηh·2^{√log N/8}; "Then s ≥ c·h·√log N."
- Hypotheses: **none**. No ports assumption, no Weak ETH. The proof uses a Euclidean plane of prices (FT Thm 2.1,
  from EG Thm 1.1) and a "rectangle test" on one four-legged tensor.
- What is bounded: the gate count of **one fixed circuit** (or one linear system plus corrections) computing a
  fixed matrix. Nothing adaptive.
- [K, FT l. 55–56] "Theorem 1.1 leaves open an upper bound with ε = 0."

**IM (conditional on Weak ETH, tapes).**
- [K, IM abstract] "A single deterministic multitape Turing machine multiplies two n-bit integers exactly in
  n(1 + log n)^{1/2+o(1)} time [...]. Under the variable-count Weak Exponential Time Hypothesis for 3-SAT, every
  deterministic multitape multiplier requires Ω(n√log n) steps in the worst case at each sufficiently large
  length."
- [K, IM Thm 7.1] "If characteristic zero admits ports, then for some δ > 0 a deterministic algorithm decides
  3-SAT on v variables in 2^{O(v^{1−δ})} bit operations times a polynomial in the input length. In particular,
  under variable-count Weak ETH, characteristic zero does not admit ports." Proof: HC Thm 13.1 (contraction of
  bit networks in 2^{O(s^{1−η})} under ports) plus sunflower sparsification.
- [K, IM l. 1752–1756] "Under Weak ETH, for a regular graph on P ≥ 2 vertices of fixed positive degree, the
  Poincaré constant valid for all placements in X must grow at least as log P, up to a degree-dependent factor.
  One can therefore choose a placement with mean squared distance one between independent vertices and mean
  squared distance O(1/log P) along an edge."
- [K, IM Thm 8.1] what is bounded: "a rational tensor network [of] maximum degree D in edge bundles, each of
  width at most DN bits" that transposes correctly "on a fraction at least 2^{−ρN²} of all binary N × N inputs"
  "has Ω_{D,ρ}(N√log N) vertices". One network, bounded degree.
- Adaptivity is handled by fixing a coarse trace, not by pricing adaptive terms: [K, IM §8.4] "At each epoch
  boundary record just the block containing each head. [...] there are at most 2^{O_M(1+T/N)} records [...].
  Keep a record shared by the largest number of inputs". The trace count 2^{O(T/N)} is absorbed in the entropy
  slack ρ < 1 − 1/√2. This works because T/N = o(N²); it is a counting argument over few layouts, each of which
  is one bounded-degree network.
- [K, IM l. 60] "Whether O(n√log n) time is attainable remains open."

**MM Lemma 4.1** (the "one fixed topology" lemma). [K, MM l. 607–612] "Let the field have no ports. Consider a
fixed trivalent topology with r input bits and r output bits. Suppose that for every permutation in the support
of a distribution, some choice of vertex tables realizes the r independent wires joining each input to its
assigned output. If each input has a uniform destination on a set of q ≥ 2 outputs, the topology has size
Ω(r√log q)." Tables may depend on the permutation; the graph may not.

**Summary for 1(b).** All three √log lower bounds are for a single object (one circuit, one network, one
topology). For IM and MM the bounded degree is essential: their √log comes from HC Thm 4.2, whose bound is
log n/log(d+1). FT's comes from a Euclidean rectangle test on one matrix. None covers a rewriting algorithm in
which each term has its own layout. The only result of that kind is HC Thm 3.1 (1(d) below).

### 1(c) List distinctness: the exponent

- [K, MM Thm 2.2, l. 329] "There is a constant σ > 0, depending only on k, such that for all sufficiently large w
  and every integer 1 ≤ t ≤ 2^w, vol_k(D_w^{⊗t}) > t·n_w·w^σ."
- No ports: [K, MM l. 648] "this proves (2.2) for any fixed 0 < σ < 1/2". So **a version with exponent 1/2 − ε
  exists exactly in the no-ports case**, through Lemma 4.1.
- Ports: [K, MM l. 675] "Choose b > max{2, 2/ξ} and 0 < σ < min{a/4, bδ/4, 1/4}", with a, δ, ξ unspecified.
- Lean `manyList_full` (as read in `mm/anti/notebook.md` Step 2′): "∃ η : ℝ, 0 < η ∧ ∀ᶠ w ..."; η is not
  given a value, and the Lean route has no ports split.
- It bounds the volume of one network for a batch of tests. Not relevant to rewriting.

### 1(d) HC Theorem 4.2, and why the trade cannot be iterated without ports

- [K, HC Thm 4.2, l. 854–858] "Let P be the walk on a d-regular multigraph with n ≥ 2 vertices, d ≥ 1, and
  uniform stationary law π. Suppose that V_π(x) ≤ β E_P(x) for every placement x in every member of a class of
  Hadamard spaces without ports. Then β ≥ c·log n/log(d + 1) for an absolute constant c > 0."
  Note the denominator. For the incidence graph of a net of order g (g² nodes, 3g lines, line degree g) the
  bound is of order log(g²)/log(g+1) = O(1): **Theorem 4.2 says nothing about one net level.** [R]
- Why iteration needs ports. [K, EG §13, l. 3244–3249] "A block has two stages. Several applications of the
  six-party identity reduce the leading coefficient of a quadratic energy bound while increasing the degree. The
  port graph then restores the original degree with a multiplicative loss independent of the intermediate degree.
  This independence permits iteration." [K, HC §13.1 item 1] "Local tensor identities derived from a comparison
  of Dirichlet energies reduce the leading coefficient in the energy bound while raising the degree. The ports
  restore bounded degree at a fixed cost. Grouping enough shrinking steps into each block gives the factor
  2^{−t} in the bound on total width."
- The trade itself has two layouts: [K, EG Lemma 12.2 and after, l. 3204–3238] "Take t = 1/2 [...] There are
  rational positive supply masses [...] for which r·d²_AB + d²_CD ≤ (31/16) Σ q_e d_e²" and "one common layout
  suffices to discard at least half of their total supply energy. [...] the leading coefficient on the demand
  energy is therefore H′/2 < 1." So OpenAI's compressor also trades between **two** layouts, on a six-party
  motif, with factor 31/32 per step in energy.
- Neither paper says what the compressor yields without ports, and neither relates it to the √log of OA-ETH.
- **HC Part I, the one bound for term-dependent cuts.** [K, HC §1.3, l. 154–168] "A small circuit expresses this
  tensor as a sum of terms, each of low matrix rank across some balanced partition of the rows. The cut may
  change from term to term. [...] Part I chooses one placement of the rows at which every low-rank term is cheap
  to supply. [...] Every balanced cut saves order d/√log d in transport per unit separation, to first order. In
  Euclidean space some bisection of any centered set of unit vectors gains only O(√d), by averaging over random
  bisections. Failure of expansion yields directions with the larger gain through an entropy inequality for
  random walks."
  - [K, HC Lemma 3.3] "the coefficients that use one variable in each of d rows of the output of a size-s circuit
    form a sum of at most 2^d tensors. Each summand has rank at most 2^{O(d)}(s + 1) on its own balanced cut,
    with at most one summand per cut."
  - [K, HC Thm 3.1] with m = ⌈log₂ d⌉, w = ⌈a·d·m^{3/2}⌉: "There is a tensor T_d with entries in {0, 1} on d rows
    of common side q₀, with w ≤ log q₀ ≤ Cw, such that over every field F whose characteristic has no ports,
    L_F^{[d]}(f_{T_d^{⊗h}}) ≥ exp(c·h·d·w/√m) (h ≥ 1)."
  - [K, HC Cor. 3.2] "For each fixed sufficiently large even d and all n ≥ d·q₀(d), grouped powers of the same
    T_d give a uniform VNP family of degree d, using at most n variables and requiring size n^{Ω(d/√log d)}".
  - [K, HC Thm 7.1] the placement: "unit points x₁, …, x_n of barycenter zero and two points Z_{ℓ,0}, Z_{ℓ,1} per
    layout, such that d(Z_{ℓ,0}, Z_{ℓ,1}) ≤ 1, ‖Z_{ℓ,v}‖ ≤ C√(m + log L), Σ_i ⟨x_i, Z_{ℓ,b_ℓ(i)}⟩ ≥ cn/√m".
  - What the target tensor must satisfy: [K, HC §3.2, l. 591–607] "A tensor that nearly attains the star bound.
    [...] B_x(Û) ≥ d·F(1) − O(d) [...] The witness comes within O(1) per row of this benchmark."

### 1(e) Explicit statements "improving 1/2 would imply ports" or "is equivalent to"

**None, for SAT or for the Fourier transform.** Full-text search of EG, HC, FT, IM, MM for satisfiab, 3-SAT,
Exponential Time, Weak ETH, subexponential:
- EG l. 209: "Related methods of compressing wire assignments occur in algorithms for satisfiability [23,
  Appendix D] and in crossing decompositions [12]."
- HC l. 189–190: "This use of an algorithm to prove hardness has precedents in circuit complexity [29, 59] and in
  tensor-network algorithms for satisfiability [16, 43]."
- MM l. 192–193: "The use of fermionic contractions to reduce wiring is related to the crossing construction of
  [32, 42] and to compression in subexponential satisfiability algorithms [17, 40]."
- IM: Thm 7.1 and its uses (ports ⇒ power-saving 3-SAT), and l. 122–125: Weak ETH "is equivalent to the
  Stearns–Hunt hypothesis [...]. Subexponential algorithms for 3-SAT [16, 46] refute the original Exponential
  Time Hypothesis [33] and are compatible with this weaker assumption."
- FT: no occurrence at all.

The only implication printed is one-directional: ports ⇒ 2^{O(v^{1−δ})} (IM Thm 7.1). No converse, and no
statement about exponents between 1/2 and 1.

The closest thing to an optimality statement for the SAT trade is EG Cor. 6.2 [K, l. 1511–1517]: "Fix t, u > 0
and the wire dimensions d_X, d_Y from Theorem 4.1 at δ = 0. Let R_n be the least R for which the two-wire tensor
is a sum of two tensors of flattening rank at most R on their respective crossing cuts. Over every field,
lim log₂R_n/n = √(t² + u²)." At t = u this is c_row = c_col = √2·λ, i.e. ρ = 1/√2. It is stated for two summands
and a common rank bound. The extension to 2^{o(λ)} pieces and to min-max over pieces is ours (flat floor, `c1d1`
D1.5). [D] EG does not draw the consequence for the SAT exponent.

---

## 2. Anthropic

### 2.1 AN-ETH: no optimality claim, two directions only

- [K, Def. 7, l. 1510] "Let 1/2 ≤ ρ < 1 be real and c ≥ 1 an integer. Pieces with parameters (ρ, c) consist [...]
  (b) A_i factors through c_i^row bits as a function of (x, y) and (u, v), and through c_i^col bits as a function
  of (x, u) and (y, v), where c_i^row + c_i^col ≤ 4ρλ + c·log(2λ)".
- [K, Thm A, l. 1587] "Suppose that there are pieces with parameters (ρ, c), and let α′ = log(1/ρ). [...] counts
  the satisfying assignments [...] in time 2^{O(km/(log m)^{α′})}". [K, l. 1708] "With the pieces of Lemma 2,
  α′ = log(12/11) = 0.125…; with those of Appendix B, α′ = 1/2."
- [K, Thm B] "There are pieces with parameters (1/√2, c), for an absolute constant c."
- The only floor stated is the pigeonhole one. [K, App. H, l. 2969–2971] "if λ^{O(1)} pieces add up to a nonzero
  multiple of the crossing of strings of λ bits, one of them needs 2λ − O(log λ) bits row-wise, which leaves it
  at most about (4ρ − 2)λ column-wise." Hence ρ ≥ 1/2.
- A remark that reads as an invitation: [K, App. H, l. 3001–3003] "log dim V_E ≈ c_HR·√E grows like a concave
  function of E. If it grew like E, the sum would be 4λ again; if it grew like E^α with 0 < α ≤ 1, the same
  calculation would give ρ = 2^{α−1}."
- **Nothing on optimality of 1/√2 or of the exponent 1/2.** No use of the words optimal or lower bound for ρ.
  The only "we do not know" is about the factor log log n (l. 747–748).
- **More than two merges, nets, Latin squares: not considered.** The level is always the g × g grid with rows
  and columns. [K, §1, l. 213–216] "We partition this graph not into two but into some larger number of pieces
  [...] merge each piece into a single node". [K, App. G, l. 2787–2789] "it writes Z, times a power of 2, as a
  signed sum of many networks, and merges rows in some terms and columns in others."
- App. G relates the two-direction count to Hurwitz-type problems (P(N), Hrubeš's N^{1.62}); no barrier is
  drawn. Issue anthropics/formal-math#45 (7 Nov 2026) asks whether Thm B gives P(N) ≤ N^{√2+o(1)}; one reply,
  not read.

### 2.2 AN-VP: a floor for all circuits of the clique-wire polynomial (flat case)

- [K, AN-VP §2.3, l. 294–306] "In the flat case we prove a lower bound (prop_flat_rate) for the polynomial of a
  network of wires on the complete graph, which for k ≥ 2 and ℓ ≥ 1 is f_{k,ℓ} = Σ_σ Π_{a=1}^{k} x_{a,σ_a}." This
  is the clique sum of AN-ETH with the tables as variables.
- [K, AN-VP Prop. E.10] "In the flat case, for k ≥ 2 and ℓ ≥ 100√k every circuit over k for f_{k,ℓ} has at least
  2^{ℓk^{3/2}/16} gates."
- [D] In engine units: S = ℓ·k(k−1)/2 edge bits, so e(K) ≥ (K^{3/2}/16)/(K(K−1)/2) > 1/(8√K) per edge bit. An
  oblivious algebraic clique-sum algorithm is such a circuit. This is the only floor in either lab's papers that
  holds for **all** engines (any number of merges, hyperedge pieces, non-product term sets). It is polynomial in
  K, so it bounds no exponent of log. It is the source of our `vpvnp/b1` floor.
- [K, AN-VP remarks, l. 3462–3466] "Two quantities limit the argument in the flat case: the k bits that name a
  balanced set, and the scaled exponent c·g_φ(P) of the set P of all ends, which Proposition E.9 bounds by about
  √k. We do not know whether the bound in the flat case can be improved."
- [K, l. 291–292] "We do not know which of the two hypotheses holds, even over R, nor do we show that the two are
  mutually exclusive." AN-VP never mentions 3-SAT or its ETH paper.

---

## 3. arXiv:2610.41622 (Majdoddin), read in full for §§1, 4, 5

**Class.** [K, Def. 4.2] a "rewrite-and-merge level": (L1) configurations partition the edge set; (L2) per block
an exact identity f_C|block = Σ_{i∈I_C} π_{C,i} with |I_C| ≤ 2^{o(m)}, "every choice is a term (product
identities)"; (L3) "Merges. Partitions P₁, …, P_p of [K]. Merge k is usable only if every configuration meets at
most two groups of P_k."; (L4) each term is evaluated under one usable merge, a piece costs the log of its rank
across the two groups; (L5) "Building a table costs at least its number of entries; no other charge". "RM_p is
the class of algorithms all of whose levels have at most p merges."

**Hypotheses.** None. Tools: rank subadditivity, the quantum functionals of Christandl–Vrana–Zuiddam (complex
tensors), the four-party rank inequality of Song–Chen–Sun–Hu. No ports, no flats, no Weak ETH.

**What is proved.**
- [K, Prop. 4.8] "the per-level factor of any two-merge identity on C satisfies ρ ≥ 1/2."
- [K, Lemma 4.11] configurations on at most three of the four cells of two merges do not trade.
- [K, Thm 4.13] "Every grid algorithm has exponent at least 1/log₂K on K-node instances: f(K) ≤ log₂K." (a × b
  grids, rows and columns, rectangles, any pieces.)
- [K, Thm 4.12] "every algorithm of RM₂^{bh} whose base methods satisfy the base condition has exponent at least
  (log₂K)^{−3}". [K, Cor. 4.21(a)] "no running time 2^{n^{1−c′}} with c′ > 0 arises".
- [K, after Thm 4.12] "The exponent 3 is an artefact of the proof. The square grid with ideal pieces [...] attains
  f(K) = log₂K, so no bound of the form f(K) ≤ (log₂K)^γ with γ < 1 can hold if such pieces exist; the true
  exponent for RM₂^{bh} lies between 1 and 3 in that case, and the pieces of [1, App. B], which exist, give e(K)
  of order (log K)^{−1/2}."

**Does it bound the exponent of log?** Only from far away: exponent ≤ 1 for grids, ≤ 3 for balanced homogeneous
two-merge levels. It proves nothing at 1/2. [K, Open problem 1] "Is there a four-leg piece family with per-merge
factor ρ below 1/√2 whose tables are built near their size? Equivalently, close the window ρ ∈ [1/2, 1/√2]".
(Given EG Thm 1.2 that window is closed at 1/√2 by the flat floor; MJ predates EG. [D])

**Three or more merges, nets.** Not covered by any theorem, and discussed as open:
- [K, §4.8 "Three or more merges"] "In the d-dimensional grid with line merges [...] the pigeonhole then forces
  every identity to pay at least 1 − 1/r of the subcube's bits, so line merges are worse than the two-dimensional
  grid. Three pairwise orthogonal merges can have a floor as low as 1/3, but orthogonality again forces squaring.
  Below 1/2 one would need identities beyond those we know: we argue that pieces that are products of factors on
  disjoint pairs of strings cannot go below ρ = 1/2 on the smallest configuration that escapes the known
  obstructions, the translation matching of the affine plane AG(2, 4) with three of its other parallel classes as
  merges; and for every configuration whose nodes split into two halves, each meeting every block of every merge
  at most once, the uniform quantum functional proves ρ ≥ 1/2 for all pieces. What is not covered is a piece
  that is not a product over pairs of strings on a configuration without such halves [...]. With p merges the
  analogue of Lemma 4.11 concerns 2^p cells. Even a success here would be a lever on ρ, i.e. on α′, not a change
  of the type of decay."
- [K, Prop. 4.23] on AG(2,3) with rows, columns, diagonals and the six-edge configuration C from two lines
  x + y = const: "if every piece of a block identity on C is k-local for some k, some piece costs at least
  6m − log₂|I_C| under every merge for which it is local [...]: ρ = 1 on C." "Left open on C are pieces coupling
  different bundles, hyperedges under the merge, for which Section 4.8 gives ρ ≥ 1/2."
- [K, Open problem 4] "Extend the class barrier [...] to three or more merges (the four-cell lemma for 2^p cells;
  the open case is non-pair pieces on pairwise orthogonal designs)."
- [K, abstract] "The class leaves one door open, configurations that meet three or more groups of a merge; we
  argue that a usable crossover point needs it, and that opening it is not enough."

**Consequences for us.**
- A p-net level whose configurations are lines of a further class meets ≥ 3 groups of each merge, so it is
  outside (L3). With single edges or rectangles as configurations it is inside RM_p, p ≥ 3, for which MJ has no
  theorem.
- The idea "three pairwise orthogonal merges with squaring" is in print (30 Oct), as an open problem, with the
  target stated as ρ < 1/2. The window ρ ∈ (1/2, 1/√2) on nets, which is ours, is not discussed there.
- MJ's unconditional floors for three merges (1/3 by pigeonhole, 1/2 on some configurations) are weaker than
  our flat floor 1/√3; they give exponent caps log₂3 and 1.

---

## 4. Other work since October 2026

**No published improvement of the exponent 1/2, and no barrier at 1/2 for engines with more than two merges.**

| item | what it does | relevance |
|---|---|---|
| C. S. N. de Brito, hexagon:2610.00692v1, 31 Oct, https://hexagonmath.org/2610.00692v1 [read, text from search tool] | For graded families of the shape of AN-ETH App. B with log dim V_{≤W} ~ W^α: existence needs α ≥ 1/2 (rank count), and the weight count is ρ ≥ max(2^{α−1}, 2^{−α}) ≥ 1/√2. "The √E of Hardy–Ramanujan is the optimum of this shape". Escapes listed in its Remark 3.2. "The floor ρ ≥ 1/2 remains open." | closes the reading of AN-ETH App. H as an invitation, for two directions and that shape only |
| MJ Prop. 4.24 | within the App. B shape with a concave profile, ρ_B ≥ 2/3; "App. B is optimal among power profiles" | same |
| F. Dias, Y. Lima, arXiv:2611.00517, 31 Oct [abstract and §§5, 8, 9 read via search tool] | limits for the clause-product form of OA-ETH's interpolation algorithm: 2^{Ω(√tw)}; "The preprint's parity form and tensor contraction escape these limits [...] whether similar limits hold for them is the natural next question." | no bound on the exponent of log |
| V. Tulsyan, hexagon:2611.00149v1, 6 Nov [abstract read] | "ρ ≥ 3/8 for correlated decompositions of full grid levels"; "Majdoddin notes that no barrier is known for decompositions whose terms are not products"; "an unconditional cap on oblivious algebraic algorithms would separate VP from VNP" | two merges; it cites the repository eth-hamiltonicity, so apparently this project's own earlier paper |
| S. Szeider, Zenodo 10.5281/zenodo.23688832, .23797197, .23981772 | crossover sizes; k×k Clique hypothesis; "The lower bounds I could prove are for restricted models (a single tensor network, tree-like resolution), and as far as I can see they do not cover the two algorithms." [K, comment of 9 Nov on ethdiscussion.blog] | none |
| MIT Hardness Group, arXiv:2611.02650, 2 Nov | Stearns–Hunt ⇔ Weak ETH (IM's ref. [41]) | the hypothesis only |
| V. Vassilevska Williams, O. Zamir, arXiv:2611.09764; J. Alman et al., arXiv:2611.05082 | k-Clique in n^{(ω/3−c)k}; hypercliques in n^{k−ε_k}; both use a decomposition lemma distilled from OA-ETH | constant savings at fixed arity; nothing on the SAT exponent |
| P. Vrana, J. Zuiddam, arXiv:2611.34664, 25 Nov | the asymptotic spectrum is path-connected; non-crossing upper quantum functionals are spectral points | tools; not read beyond the abstract |
| H. Zhou, arXiv:2610.34273v2 | asymptotic rank of the K_n graph tensor: edge exponent n/(2(n−1)) → 1/2 | rank model; the flattening floor, not engines |
| T. T. Nguyen, hexagon:2611.00004; Strassle–Subercaseaux, arXiv:2611.11832; others in the 1 Nov thread | consequences of the algorithms as black boxes, all at rate √log | none |

Venues checked: arXiv and Hexagon through two search engines; https://ethdiscussion.blog (working group of
Impagliazzo, Paturi, Williams; posts of 26 Oct to 12 Nov, the "New Results" thread with 30 comments up to 16 Nov:
no announcement of a better exponent and no verdict); Shtetl-Optimized, post of 26 Oct and the search tool's extract of its comments (up to #133);
GitHub issue lists of anthropics/formal-math (#15–#57) and openai/math (0 issues, history.md last entry 24 Nov).

- Shtetl-Optimized [K, comment #31, 27 Oct, https://scottaaronson.blog/?p=10239] "They should've said: 3SAT
  appears to require exp(n^{1−o(1)}) time. [...] if this 'Weak ETH' were also to fall, then I'd substantially
  update my probability of P=NP". Opinion about 2^{n^{0.99}}; nothing about exponents of log.
- Not found: any post by Lipton–Regan, Fortnow (beyond the announcement of 28 Oct), or a Williams group page that
  discusses improving the exponent. Not accessed: X/Twitter threads, Zulip, the ETH_Repository list of the
  working group, MathOverflow/cstheory beyond search snippets.

**Has anyone proposed or analysed more than two merges?** Yes, MJ §§4.7–4.8 and Open problem 4 (quoted in §3):
AG(2,3) with rows, columns and diagonals; AG(2,4) with three parallel classes; line merges in d-dimensional
grids; target ρ < 1/2; pair-product pieces excluded (proved on one configuration, argued on another). Nobody
else. Nobody has a three-merge identity.

---

## 5. Synthesis [D unless marked]

### 5.1 The chains that do hold

1. **Two merges.** EG Thm 1.2 (flats over every field) ⇒ flat floor ⇒ every rectangle-type family has a piece
   with c_row, c_col ≥ √2λ − o(λ) ⇒ ρ ≥ 1/√2 ⇒ certified exponent ≤ 1/2 for (2, 2, 𝒞)-engines, unconditionally
   (`c1d1` D1.5). EG Cor. 6.2 is the two-summand case in print. Our CAT(0) Theorem 3.2 shows no price argument
   can do better.
2. **Three merges above 0.7075.** sat3 Theorem S: α′ > 0.7075 on nets with index-4 subgroups ⇒ a subset of a
   product of pods is not a price ⇒ contracting holds (sat3 Thm 4.3, from AN-VP's thm_alt_rank_price) ⇒
   power-saving 3-SAT (our Theorem R; or
   via ports: `literature-check.md` A.2 notes that EG Lemma 11.3/Prop. 11.2 is OpenAI's own "uniform gap ⇒
   ports", and IM Thm 7.1 finishes). Every link after the first is ours or printed; the first rests on our
   unreviewed Theorem 4.3.
3. **All engines, weak.** AN-VP Prop. E.10 ⇒ e(K) ≥ 1/(8√K) for every oblivious algebraic clique-sum algorithm.
   With K ≤ m^{1/q} this caps the power saving such an algorithm could reach, not the exponent of log.

### 5.2 Where "net engine with α > 1/2 ⇒ [OpenAI] ⇒ ports" breaks

- **Via Lemma 4.1 / IM Thm 8.1 / FT.** These need one bounded-degree network realising a family of routings.
  An engine has one layout per term and no family of permutations. IM's trick for adaptivity (few traces, pick
  the most popular) does not help: an engine's terms are all needed at once, they are not alternative runs on
  different inputs. This is `c1d1` D1.6, confirmed against the texts.
- **Via HC Thm 4.2 applied to a level.** The Poincaré obstruction is log n/log(d+1). A net's incidence graph
  has diameter 4 and degree g = √(#nodes); every two nodes are at most four incidences apart in any metric. So
  absence of ports gives no non-Euclidean room at the scale of one level. [R] The non-Euclidean prices that do
  raise the three-merge floor (sat3 §5, pods) come from failure of *contracting*, a different hypothesis.
- **Via the price method per level (sat3).** The cap for all prices on a p-net is 1/√2 (Cor. 3.4), the best
  known floor 0.6124. The chain needs Q1 (a price with value E/√2 on 3-nets).

So the earlier diagnosis stands, and one more route (Thm 4.2 on a level) is closed for a reason that can be
stated in one line.

### 5.3 The one result of the right kind, and the missing lemma

HC Part I is the only place where either lab bounds a **sum whose terms each have their own cut**, which is
what an unrolled engine is.

**Same shape.** [D]
- An oblivious arithmetic algorithm for the (K, λ)-clique sum with 2^{eS} operations is an arithmetic circuit of
  that size for a set-multilinear polynomial of degree d = K with n = N^{K−1} variables per row (this is AN-VP's
  f_{k,ℓ}). With e = Θ((log K)^{−α}): size n^{Θ(d/(log d)^α)}. Anthropic's engine: n^{O(d/√log d)}.
- HC Cor. 3.2, no ports: an explicit degree-d family needs n^{Ω(d/√log d)}.
- AN-VP Prop. E.10, flats: f_{k,ℓ} needs n^{Ω(√d)}. HC's own remark explains the difference: Euclidean bisections
  gain O(√d), no-ports directions gain d/√log d.

**The chain that would give (A) for every algebraic engine, nets included.**

  α > 1/2 for some oblivious algebraic clique-sum algorithm
  ⇒ [HC Lemma 3.3] the wire tensor T_K(λ) is a sum of ≤ 2^K terms of rank ≤ 2^{O(K)}·2^{S/(log K)^α}, each on its
    own balanced cut
  ⇒ [**missing: HC Thm 3.1 for T_K**] impossible in a characteristic without ports
  ⇒ ports ⇒ [IM Thm 7.1, characteristic 0] 3-SAT in 2^{O(v^{1−δ})}, i.e. Weak ETH fails.

Lemma 3.3 does not care how many merges a level has, whether configurations are hyperedges, or whether term
sets are products. So this chain, if completed, would cover everything listed as "outside the class of Theorem S"
in sat3 §8 except non-oblivious (instance-adaptive) algorithms.

**Where exactly it breaks.** HC's proof compares, at one placement, the price of the target with the cost of
supplying a low-rank term from two suppliers. It needs a target "within O(1) per row" of the star bound, and
builds one from exterior tensors. A product of wires has price exactly λ·Σ_{u<v} d(x_u, x_v).

- [R] Let K sites at distance 1 from a common point o have suppliers y₀, y₁ for a cut into two halves, with leg
  lengths r_i = d(x_i, y_{b(i)}) and Σ_i r_i = K − σ. For
  u, v on one side d(x_u, x_v) ≤ r_u + r_v, and across the cut d ≤ 2. Summing,
  Σ_{u<v} d(x_u, x_v) ≤ K(K−1) − (K/2 − 1)σ. A rank-R term on that cut costs at most
  λ(K−1)(K − σ) + d(y₀, y₁)·log R. Hence
      price(T_K) − cost(term) ≤ λ·(K/2)·σ − d(y₀, y₁)·log R.
  So the wire tensor can beat the terms by at most half of the first-order saving. With HC's numbers
  (d(y₀, y₁) ≤ τ, σ ≈ τ·cK/√m) this allows, and does not give, log R ≥ c·λK²/(2√log K) = Θ(S/√log K).
- [D] For the bound to be attained the placement must have all pairs nearly antipodal:
  mean(2 − d(x_u, x_v)) ≲ 2ηc/(K·log K), i.e. pairwise angles π − ε′ with ε′² ≲ 8ηc/(K log K), **and** keep the
  saving Σ_i ⟨x_i, Z_{b(i)}⟩ ≥ cK/√log K. If all pairs have angle ≥ π − ε′, at most one site makes an angle below
  π/2 − ε′/2 with a given Z, so the saving is at most ‖Z‖(1 + Kε′/2) ≤ C√(log K + K)·(1 + Kε′/2), which is of
  order K/√log K: the **same order** as required. The two demands meet at the level of constants (one needs
  roughly C²·η ≳ c with η small). First-order counting neither proves nor excludes the placement.
- HC Thm 7.1 as stated controls savings and radii only. It gives no lower bound on pairwise distances between
  rows, and in the lamp construction there is no reason for them to exceed the Euclidean √2. At √2 the wire
  tensor is a factor 1/√2 below the star bound and the comparison yields nothing.

**Q2 (the missing lemma).** In a class of Hadamard spaces without ports, are there K unit points and, for every
balanced cut ℓ, suppliers at distance ≤ τ with total leg saving σ_ℓ, such that
Σ_{u<v} (2 − d(x_u, x_v)) ≤ (1 − δ)(K − 1)·min_ℓ σ_ℓ for a fixed δ > 0, with σ_ℓ/τ ≥ cK/√log K?
- If yes: under no ports e(K) ≥ c′/√log K for every oblivious algebraic clique-sum algorithm; Anthropic's rate is
  optimal in that class; exponent > 1/2 by any net engine ⇒ ports ⇒ Weak ETH fails (characteristic 0; all
  characteristics under randomised Weak ETH by `c1d1` C1). The realistic target would then be Weak ETH itself.
- If no: algorithms slip through whose terms are cheap for a reason HC's supply argument cannot see, namely
  terms that are products of wires rerouted through hubs. A three-merge engine is exactly of that kind (its
  terms are wire networks on hubs, priced by wire lengths), so it would not be touched.
- [C] I have no evidence either way. The antipodality requirement is tree-like (pods), while the saving
  requirement is anti-tree-like (in a pod the saving is O(‖Z‖) = O(√K) ≪ K/√log K). A space that is a pod to
  first order and has no-ports directions at second order is not obviously contradictory, and not obviously
  available.

A second, independent version of the same gap: is HC's T_d (or any tensor meeting its (3.2)) a restriction of a
complete-graph wire tensor on O(d) nodes with O(w) bits per node? Prices do not forbid it (it needs only mean
pairwise distance ≥ 2w/B with B the bits per node). If it were, an engine with α > 1/2 would contradict HC
Thm 3.1 directly. The trivial representation uses (d−1)·w bits per node, which is useless. [C]

### 5.4 What kind of algorithm slips through today

With what is proved, the following are not excluded under any stated hypothesis:
- net engines with ρ* ∈ [0.6124, 0.7071) when contracting fails, i.e. α′ ∈ (1/2, 0.7075] (sat3);
- anything with hyperedge configurations, non-product term sets or growing lists of configurations, down to the
  polynomial floor e(K) ≥ 1/(8√K) (AN-VP E.10), and down to (log K)^{−1/2} if Q2 holds and ports fail;
- anything in a characteristic with ports (where 3-SAT is power-saving anyway).

A three-merge net engine with pieces that are hyperedges under each merge is inside the first two classes. MJ
Prop. 4.23 removes one subclass: pieces that are products over bundles (pair-local) give ρ = 1 on the AG(2,3)
configuration, so any three-merge identity must couple bundles. That agrees with sat3 §7 item 5.

### 5.5 Statements suggesting the exponent can be improved

None with content. AN-ETH App. H's "ρ = 2^{α−1}" remark is neutralised by hexagon:2610.00692 and MJ Prop. 4.24
for its own shape. MJ's "ideal pieces" (ρ = 1/2, exponent 1) are excluded by flats. Williams's quoted opinion
has no argument. OpenAI's FT and IM leave open only the removal of the o(1) ("ε = 0"), not a smaller exponent,
and prove 1/2 optimal for their problems.

Circumstantial evidence for 1/2 being a barrier in the no-ports world: three unrelated problems have matching
√log bounds there (Fourier transform, unconditionally; tape multiplication and transposition; routing through a
fixed topology), HC's term-dependent-cut bound has the same √log, and both labs' SAT algorithms land on 1/2 by
different mechanisms. This is a pattern, not a theorem. [C]

---

## 6. What I would do with this

1. Treat Q2 as the decisive question, ahead of Q1. Q1 concerns one design family and the price method per level;
   Q2 would settle every algebraic engine at once, in the direction "improvement ⇔ ports".
2. A referee should check the two-line inequality of §5.3 and the angle count (15 minutes), then read HC §§5–7
   to see what the lamp construction gives for pairwise row distances. If they are Euclidean-like (≈ √2), ask
   whether Thm 7.1 can be redone with the rows on a pod factor: sites x_i = (pod leaf i, lamp point i) in a
   product, where the pod factor supplies antipodality and the lamp factor the saving. In an ℓ₂ product the
   saving and the deficit both scale with the weights of the factors, so this is a one-parameter optimisation.
3. Until Q2 or Q1 is decided, the attainment search in the window (1/2, 0.7075] is not known to be equivalent to
   refuting Weak ETH, and is not known to be possible. A positive answer to Q2 would make it equivalent to
   proving ports.

## 7. Not done

- HC §§5–11 and EG §§7–16 were not read line by line; statements were taken from the theorem texts and the
  section introductions.
- hexagon:2611.00149, arXiv:2611.00517, 2611.02650, 2611.09764, 2611.05082, 2611.34664 and hexagon:2610.00692
  were read through the search tool's extracts, not from the PDFs.
- "Paths, trees and grids" was scanned for ports/SAT/optimality only (nothing relevant); the sunflower paper was
  not opened.
- The inequality and the angle count in §5.3 are unreviewed.
