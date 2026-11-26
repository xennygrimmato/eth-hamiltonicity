# The ports question: statements, dictionary, geometry, attacks

Strategist notes, 26 Nov 2026. Tags: [K] quoted or known, with pointer; [D] my derivation (unreviewed);
[C] conjecture; [N] computed. "OA" = OpenAI's unrefereed 24 Nov 2026 release; "AN" = Anthropic's
"VP ≠ VNP over every field". Anything tagged [K-OA] rests only on OpenAI's papers (or on their Lean, read but
not built by us).

Paper names and where the text is (pdftotext copies in the scratchpad clone `survey/oa/preprints/…/paper.txt`):

- **EG** = "Euclidean geometry in the asymptotic spectrum of tensors" (the release's [42]/[44]/[48]).
- **HC** = "Circuit lower bounds for Hamiltonian cycle and the permanent" ([43]/[49]).
- **IM** = "The logarithmic exponent of integer multiplication on tapes".
- **MM** = "The matrix multiplication exponent is nine fourths".
- **AN** = Anthropic's paper (`scratchpad/anth/paper.txt`).

The five findings that matter most are collected in §0. Parts 1–6 follow the order of the brief.

---

## 0. Headlines

1. **[D] Anthropic's contracting hypothesis implies ports.** AN Theorem F.6 (thm_poincare) gives, under the
   contracting hypothesis, a Poincaré inequality on the Cayley graphs of the unitriangular groups U_h(F₂) with
   constant C₀·(h−1) at degree h−1 and order 2^{h(h−1)/2}. OA's logarithmic obstruction (HC Theorem 4.2; Lean
   `exists_logarithmic_placement`) says that without ports every graph has constant ≥ c·log n / log(d+1), which here
   is of order h²/log h. For large h this is a contradiction. So
   **contracting ⇒ ports ⇒ (characteristic 0) 3-SAT in 2^{O(v^{1−δ})}**, and **Weak ETH ⇒ no ports in
   characteristic 0 ⇒ the contracting hypothesis fails in characteristic 0 ⇒ the rank metric √rk on Mat_μ(F₂) is a
   price for every μ.** (Part 2.)
2. **[D] The same object decides both labs' case split.** OA's Lemma 11.3 (Grassmannian inequality B_m ≤ (m−η)B₁)
   and AN's contracting inequality D(μ) ≤ s·D(1), s² < μ, are the same inequality: Mat_μ(F₂) is the big cell of
   the Grassmannian of μ-planes in F₂^{2μ} (a ↦ graph of a), and rk(a−b) = dim(Γ_a+Γ_b) − μ. (Part 2.)
3. **[D] The Izeki–Nayatani route to ports is closed unless contracting holds.** If √rk on Mat_μ(F₂) is a price
   for all μ, the class of spectral spaces has Izeki–Nayatani invariant tending to 1 (I get δ ≥ 1 − 4/(μ−1), §3.3), and it
   contains the square-root snowflake of a genuine expander Cayley graph (rank-one generators, spectral gap ≥ 1/2,
   degree 2^{2μ}, order 2^{μ²}) whose nonlinear Poincaré constant is μ ≈ 2·log n/log d: exactly the borderline rate
   of HC Theorem 4.2. So "spectral gap ⇒ nonlinear gap" fails for spectral targets in that case. (Parts 3–4.)
4. **[D] Ports is an (ℓ₂) network-coding question for tensors.** By Strassen duality the best asymptotic rate
   at which EPR pairs on the edges of a graph G can be converted by restriction into EPR pairs on demand pairs is
   an LP over spectral wire metrics. Because all spectral metrics are CAT(0) (AN thm_cn, EG Theorem 4.3), the
   shortest-path metric of any graph with a 4-cycle is not spectral, so **tensor coding strictly beats routing**
   (e.g. on the Okamura–Seymour instance K_{2,3} the tensor rate is > 3/4, the flow rate). Ports says the gain
   over routing on expanders is the full factor log n; no ports says it is at most √log n. (Part 4.)
5. **Odds [C]:** no ports in characteristic 0: 93%. Provable by us in weeks: ports < 1%, no ports < 2%. The
   reachable results are (i) the rigorous dictionary of item 1 as a short note, (ii) small-case facts about which
   five-point CAT(0) metrics are spectral, (iii) the conditional algorithm statement re-based on Anthropic's paper
   (contracting ⇒ power-saving simulation of nondeterministic time). (Parts 5–6.)

---

## Part 1. Exact statements

### 1.1 The class of spaces

**Spectral point** [K-OA, EG §2.1]: on a finite set J of ≥ 2 parties over a field k, a function F from J-tensors
to [0,∞) with F(0) = 0, F(1) = 1, monotone under restriction (a linear map at each party), multiplicative under ⊗,
additive under ⊕. H = log₂F is a price. This is a point of Strassen's asymptotic spectrum.

**Wire distance** [K-OA, EG §2.2]: d(a,b) = H(E_ab(2)), E_ab(2) the two-dimensional identity ("binary wire")
between a and b. It is a pseudometric (triangle inequality by contracting two wires).

**Spectral space** [K-OA, EG §2.2, verbatim]: "A spectral space is a metric space equipped with prices H(T; x) for
all finite placements over k. Inserting trivial slots leaves prices unchanged, and a binary wire has price equal to
the distance between its ends. On each finite set S of positive diameter, all prices must have the form
δ(S) log₂ F_S(T) for one spectral point F_S on S."

**Hadamard spectral space** [K-OA, EG Theorem 4.3, verbatim]: "Every complete geodesic spectral space X is
CAT(0). In particular every spectral space embeds with prices in such a space, called below a Hadamard spectral
space." HC §2.2: "Let X_χ denote the class of Hadamard spaces admitting spectral prices over a field of
characteristic χ. The geometry depends only on χ."

**What is known to preserve the class** [K-OA, HC §2.2]: "Three operations preserve spectral realizability. One
can rescale the metric and all prices by a common positive factor, pass to a closed convex subspace, or take a
pointed ultralimit." Also: restriction to subsets, metric quotient, duplication of sites.
**Not known:** closure under ℓ₂ products. HC Theorem 6.1 only produces, by Zorn's lemma, a *subclass* without
ports that is closed under finite ℓ₂ products. So products of spectral spaces are not known to be spectral.

**Finite form** [K-OA, EG after Def. 11.1; Lean `RealizableConfigurations`]: a Hadamard space is in X_χ iff every
finite subset, with its distances, is c·d_F for some spectral point F and scale c > 0 (limits allowed). So the
class is determined by the closed cone of finite spectral wire pseudometrics on n points, for each n.

**Dependence on the characteristic only** [K-OA, EG Def. 11.1 text + Lemma 2.3]: "This property depends only on
the characteristic, since it concerns only joint prices of binary wires (Lemma 2.3)." Lemma 2.3: for k ⊆ K the
possible joint values of spectral points on tensors defined over k are the same over the two fields; binary wires
are defined over the prime field.

**Anthropic's version** [K, AN Def. 2.1]: a spectral point φ is multiplicative, φ(1) = 1, and subadditive on
covers (φ(s) ≤ Σφ(t_j) whenever s = Σ s_j with s_j a restriction of t_j). A price is a pointwise limit of c·d_φ.
[D] Every OA spectral point is an AN spectral point (s ≤ ⊕ t_j, then additivity and monotonicity), so
{OA finite spectral metrics} ⊆ {AN prices}. Consequences for directions: an inequality for all AN prices holds for
all OA spectral metrics; an OA existence statement (e.g. Euclidean flats) gives AN prices.

### 1.2 The definition of ports

[K-OA, EG Definition 11.1, verbatim, with the two energies defined just before it]:

> E_G(x) = (1/|V|) Σ_{i,j} G_ij d(x_i,x_j)², V(x) = (1/|V|²) Σ_{i,j} d(x_i,x_j)².
> "A field has ports if it admits a family of regular, symmetric multigraphs of unbounded order and bounded degree,
> and a constant γ such that V(x) ≤ γ E_G(x) for every graph in the family and every assignment into a spectral
> space over the field. Here G denotes normalized adjacency. A diagonal arc keeps the walk at its current vertex."
> "This property depends only on the characteristic […]. By Theorem 4.3 one may test either finite spectral points
> or complete CAT(0) spectral spaces. […] every port graph is connected."

So: the inequality is the **squared (p = 2) nonlinear Poincaré inequality** E_{u,v} d(x_u,x_v)² ≤ γ·E_{(u,v) edge}
d(x_u,x_v)²; "admits" means one family and one γ for **all** spectral spaces of the characteristic at once
(equivalently, for all finite spectral wire pseudometrics on the vertex sets). Restated identically in HC §1.3,
§2.2, §6; IM §7 ("Characteristic zero admits ports when…"); MM §4.2.

[K-OA, EG Proposition 11.2]: "If a finite field F has a largest spectral flat dimension k, then F has ports."
Proof route: cube exclusion (the corners of the (k+1)-cube are uniformly not spectral) ⇒ Lemma 11.3 on the
Grassmannian of m-planes in F₂^{2m}: B_m ≤ (m−η)B₁ ⇒ sparse matrices whose Poincaré constants grow like α^j,
α < m, on m^j-fold exponent ⇒ zig-zag / replacement amplification (after Mendel–Naor) to bounded degree. EG
Theorem 1.2 then shows the hypothesis never holds (flats of every dimension exist over every field), so this route
to ports is closed, as the brief says.

[K-OA, HC Theorem 4.2, verbatim]: "Let P be the walk on a d-regular multigraph with n ≥ 2 vertices, d ≥ 1, and
uniform stationary law π. Suppose that V_π(x) ≤ β E_P(x) for every placement x in every member of a class of
Hadamard spaces without ports. Then β ≥ c log n / log(d+1) for an absolute constant c > 0."
The proof is one page (Lemma 4.1 = barycentric smoothing of a walk, then a replacement product) and uses only
that the targets are Hadamard. Contrapositive, which I use repeatedly:

> **Finite certificate for ports [K-OA; D for the phrasing].** If ONE regular graph on n vertices of degree d has
> Poincaré constant β over all spectral spaces of the characteristic with β < c·log n/log(d+1), then the
> characteristic has ports. In the Lean (`exists_logarithmic_placement`) the constant is explicit: order 2^s,
> degree 2^e, bound s/(10000(e+3)).

This is a dichotomy of the Mendel–Naor type: the best Poincaré constant of bounded-degree graphs over the class is
either O(1) along some family or ≥ c·log n for every graph. (The trivial upper bound for an expander against any
metric space is O(log n)² in squared form, by Bourgain/Matoušek.)

### 1.3 What "ports ⇒ fast 3-SAT" uses, step by step

[K-OA, IM Theorem 7.1, verbatim]: "If characteristic zero admits ports, then for some δ > 0 a deterministic
algorithm decides 3-SAT on v variables in 2^{O(v^{1−δ})} bit operations times a polynomial in the input length. In
particular, under variable-count Weak ETH, characteristic zero does not admit ports."

The chain [K-OA]:

1. **Poincaré inequality ⇒ exact tensor identities** (EG Theorem 12.1 "Conversion of a fixed motif"). If
   Σ_{e∈D} p_e d_e² ≤ H Σ_{e∈S} q_e d_e² for every spectral point (D demand edges, S supply edges), then the product
   of demand wires W_D(b) is a **sum** of products of supply wires W_S(c) with ‖c‖_q ≤ √H‖b‖_p (up to rounding),
   with local maps whose entries satisfy a fixed finite system of polynomial equations. The tool is Strassen
   duality in the strict form (EG Lemma 2.2: F(X) < F(Y) at every spectral point ⇒ K·Y^m ≥ X^m for a fixed K and
   all m). The sum is needed because the optimal supply widths c_e ∝ q_e d_e depend on the spectral point.
2. **Two motifs.** A fixed six-party motif (EG Lemma 12.2) that reduces a quadratic width energy, raising the
   degree; and the port graphs, which replace the all-pairs demand among the D ports of one vertex by wires on the
   bounded-degree port graph ("This is exactly the metric comparison needed to convert the dense demand into
   bounded-degree supply", EG §13.4). Ports is used only here: to restore bounded degree at constant cost.
3. **Iterated compression** (EG Theorem 13.1): a network with P₀ positions of degree d₀ and widths ≤ W₀ has an
   exact expansion by T blocks with √(L_T) ≤ 2^{−T}(√L₀ + O(P₀)) (shared bits shrink by 2^{−T}), while fields and
   local contractions grow by C₂^T.
4. **Enumerable contraction** (HC Theorem 13.1): "Fix a characteristic admitting ports. There is an η > 0 such
   that every closed bit network of volume at most s and maximum degree at most s^{1/20} […] has a formula for its
   contraction using 2^{O(s^{1−η})} arithmetic operations and local entry queries." Proof: route the network onto
   h·2^h ≈ s^{9/10} positions (Beneš), take T = ⌊a log₂ s⌋ blocks; shared bits O(s^{1−a} log s), histories
   O(P polylog s) bits, private bits ≤ s^{1/2} per position. In characteristic 0 the fixed scalars can be taken
   rational and counts are exact integers.
5. **3-SAT** (IM proof of Theorem 7.1): sunflower-style sparsification with r = ⌈v^α⌉ gives 2^{O(v^{1−α} log v)}
   leaves, each a 3-CNF with O(v^{1+4α}) clauses; a leaf is a degree-3 bit network of volume O(v^{1+4α}) whose
   contraction is the number of satisfying assignments; total exponent O(v^{1−α} log v + v^{(1+4α)(1−η)}).

**δ in terms of the port data [D, from the proofs].** η = min(a, 1/10)−o(1) up to the choice in step 4, where a
must satisfy b₀·a·log₂ s ≤ h ≈ (9/10)log₂ s and C₂^{a log₂ s} ≤ s^{1/2−1/10}, so
a ≈ min(0.9/b₀, 0.4/log₂C₂); then α < η/(4(1−η)) and δ < min(α, 1−(1+4α)(1−η)). So
δ ≈ η/5 ≈ c/ log C₂ where C₂ = C₂(γ, d₀) is the growth factor per block; one block must contain enough motif steps
to halve the width energy and one port replacement, so log C₂ grows at least like log(γ d₀) [D, not tracked in the
papers; they say only "exponents in the length estimates may depend on χ and the port constants", HC §12].
The algorithm is non-uniform in a weak sense only: the motif maps are a fixed finite list of rational scalars
whose existence comes from Strassen duality (Zorn), not from a construction.

**What the algorithm is, in one sentence.** It is not a new SAT idea; it is a size-s^{1−η} "separator" for
arbitrary tensor networks in which the separator is algebraic: the network is rewritten as a sum of 2^{s^{1−η}}
networks that fall apart into pieces of size ≤ s^{1/2}. Ports are what allow the rewriting to keep bounded degree.

### 1.4 The other uses of ports in the release

- **HC Theorem 1.1** (Hamiltonian cycle / permanent ≥ exp(c (log N)²/(log log N)²)): no ports ⇒ Part I (one
  placement making all balanced cuts cheap; uses HC Theorems 4.2, 5.1, 6.1); ports ⇒ Part II, HC Theorem 12.2:
  "L(HC_N) > 2^{N^ε}" (stretched exponential) by compression + a counting diagonal argument. Either way a bound.
- **HC Theorem 12.1** (exact batches, ports case): trivalent networks for (U*_n)^{⊗k} over a finite field of a port
  characteristic have volume > k n^{1+δ}.
- **MM Theorem 2.2** (list distinctness needs volume > t n w w^σ): MM §4.2 "Fields without ports": Lemma 4.1 (a
  topology that realizes r wires with q uniformly random destinations has size Ω(r√log q)), any σ < 1/2. MM §4.3
  "Finite fields with ports": cheap distinctness would give cheap tagged permutations, which with EG Proposition
  14.1 (descent with tagged-permutation gates, needs ports) would contradict HC Theorem 12.1; some σ > 0.
- **IM Lemma 8.2 / Theorem 8.1** (tape lower bound Ω(n√log n) under Weak ETH): Weak ETH ⇒ no ports in
  characteristic 0 ⇒ HC Theorem 4.2 gives a placement with E d(x_U,x_V)² = 1 and edge energy O(1/log P).
- **EG itself** (Theorem 1.2, flats exist): assume a largest flat ⇒ ports (Prop. 11.2) and local routing tests ⇒
  amortised self-simulation ⇒ contradiction.
- The Fourier paper does not use ports (no occurrence of ports, Poincaré, or Weak ETH in its text) [K-OA, grep].

### 1.5 Lean status [K-OA, read in `lean/`, not built by us]

| Statement | Lean | Where |
|---|---|---|
| Definition of ports, finite-spectral-point form | yes: `HasWireExpanders k` | `OAI/Computability/VPVNP/WireExpanders.lean` |
| Prop. 11.2 in cube-exclusion form | yes: `wire_expanders_of_cube_exclusion` (¬RealizableUpToScale k (cubeDistances ℓ) → HasWireExpanders k) | same file; `OAI/ThreeFlat/Expander*.lean` |
| Ports in characteristic 0 (Hadamard form) | yes: `PortZero` | `OAI/Computability/MultitapeWeakETH/Price.lean` |
| IM Theorem 7.1 (ports ⇒ 3-SAT power saving) | yes: `middle_count_bridge : PortZero → PowerSavingDecision …` and `price_of_variable_weakETH : WeakETH → ¬PortZero` | `…/MultitapeWeakETH/MiddleDecision.lean` |
| HC Theorem 4.2 (log obstruction), char 0 | yes: `exists_logarithmic_placement`, constant s/(10000(e+3)) | `…/MultitapeWeakETH/Cloud.lean` |
| IM tape lower bound under Weak ETH | yes (comparator `main_of_weakETH`) | `ComparatorChallenges/MultitapeWeakETH.lean` |
| HC Theorem 1.1 with the (log N)² exponent | no ("remains unformalized", `lean/docs/379.md`); Lean has only N^C for every C | docs |
| HC Theorem 6.1 (product theorem), Theorem 5.1 (entropy) | not located; the superpolynomial HC bound in Lean may use a different route | not checked |
| MM Theorem 2.2 | yes for every finite field (`manyList_full`, per our LOGBOOK), with no top-level ports split | LOGBOOK 26 Nov |
| Which characteristics have ports | open; no statement | — |

`lean/docs/379.md` does not mention ports at all; the split is internal to the proofs.


---

## Part 2. The dictionary with Anthropic's paper and with our notes

### 2.1 The two hypotheses are the same kind of statement

| | Anthropic (AN Def. 2.1 / D.1) | OpenAI (EG Def. 11.1) |
|---|---|---|
| Targets | all prices (limits of c·d_φ, φ multiplicative and cover-subadditive) over the field k | all spectral wire metrics over the field (⊆ AN prices, §1.1) |
| Graph | Cayley graph of Mat_μ(F₂) with the rank-one matrices as generators (degree ≈ 2^{2μ}, order 2^{μ²}) | any family of bounded-degree regular graphs |
| Inequality | D(μ)² ≤ s²·D(1)², s² < μ: mean square over rank-μ differences vs. over edges. The trivial bound is s² = μ (quadrilateral inequality) | E_{pairs} d² ≤ γ·E_{edges} d². The trivial bound is O(log n)² |
| Meaning | every price falls short of the Euclidean μ-cube by a fixed factor | some sparse graphs are expanders for all prices |
| Used for | Poincaré on U_h (AN F.6) → rerouting laws (G.2) → trees (H.2) → cuts (J.4) → no accelerators (K) | motif conversion (EG 12.1) → compression (EG 13.1) → enumerable contraction (HC 13.1) → counting diagonal (HC 12) |

Both are uniform squared Poincaré inequalities over all prices. Both labs then use the same engine: Strassen
duality turns the inequality into exact identities that reroute wires along the sparse graph, and a diagonal
argument finishes. The contracting inequality is the weak, dense-graph form; ports is the strong, bounded-degree
form. OpenAI's own "rigid" hypothesis (a largest flat dimension, i.e. cube exclusion) is used exactly once to get
a contracting-type inequality: EG Lemma 11.3, B_m ≤ (m−η)B₁ on the Grassmannian of m-planes in F₂^{2m}.

**[D] Lemma 11.3 and the contracting inequality are one inequality.** a ↦ Γ_a = graph of a embeds Mat_μ(F₂) as
the big cell of the Grassmannian of μ-planes in F₂^{2μ}, and dim(Γ_a + Γ_b) − μ = rk(a−b). So B_r is the
Grassmannian version of D(r)², and "B_m ≤ (m−η)B₁" is "D(m)² ≤ (m−η)D(1)²" averaged over the whole
Grassmannian instead of the big cell. Define the **Grassmann metric** σ_m(U,V) = √(dim(U+V) − m); then
ρ_μ = σ_μ restricted to the big cell, and c1's lattice embedding (L_a in the building of GL_{2μ}(F₂((t)))) is the
statement that σ_m is the metric on the type-m vertices of the link of a vertex of that building.

### 2.2 Theorem A [D]: contracting ⇒ ports

**Statement.** Let k be a field of characteristic χ. If the contracting hypothesis (AN Def. D.1) holds over k,
then χ admits ports (EG Def. 11.1). In particular, if it holds over ℚ (or any field of characteristic 0), then
3-SAT is in 2^{O(v^{1−δ})}·poly by IM Theorem 7.1; and under variable-count Weak ETH the contracting hypothesis
fails over every field of characteristic 0.

**Proof, every step referenced.**

1. [K-AN, Theorem F.6 (thm_poincare), verbatim; standing assumption of AN §F: "we are in the contracting case,
   and we fix μ and s"; U_h = upper unitriangular h×h matrices over F₂, generators x_j = 1 + E_{j,j+1}, 0 ≤ j < h−1]:
   "There are an integer u ≥ 2 and a real number C₀ ≥ 0 such that for every l ≥ 2, h = lu, and every price on U_h,
   E_{g,a}|a, ga|² ≤ C₀ Σ_{j<h−1} E_a|a, x_j a|²", g and a independent and uniform in U_h.
   The contracting hypothesis is used for one pair (μ, s) only; C₀ and u depend on (μ, s).
2. [D] Translation. Let G_h be the Cayley graph of U_h with the h−1 involutions x_j (x_j² = 1 over F₂, so G_h is a
   simple (h−1)-regular graph). n = |U_h| = 2^{h(h−1)/2}. The left side of F.6 is V(x) (ga is uniform and
   independent of a). The right side is C₀(h−1)·E_{G_h}(x). So G_h has Poincaré bound
   β_h = C₀(h−1) for every AN price on U_h, hence for every OA spectral wire pseudometric over k (§1.1), hence for
   every placement in every Hadamard spectral space of characteristic χ (the finite subsets of such a space are
   spectral over some field of characteristic χ, and by EG Lemma 2.3 the cone of finite spectral wire metrics is the
   same for all fields of one characteristic: it is the cone over the prime field).
3. [K-OA, HC Theorem 4.2]: if the class X_χ has no ports, every d-regular n-vertex graph has
   β ≥ c·log n/log(d+1), c absolute. Lean form (characteristic 0, `exists_logarithmic_placement`): order 2^s,
   degree 2^e, s ≥ 10000(e+3): some placement has V > (s/(10000(e+3)))·E.
4. [D] Arithmetic. Pad G_h with loops to degree 2^e, e = ⌈log₂ h⌉; this at most doubles the bound:
   β ≤ 2C₀(h−1). Here s = h(h−1)/2. The threshold is s/(10000(e+3)) ≥ h(h−1)/(20000(log₂h + 4)). So no ports
   would force 2C₀(h−1) ≥ h(h−1)/(20000(log₂ h + 4)), i.e. h/(log₂h + 4) ≤ 40000·C₀, false for all large
   multiples h of u. Hence X_χ has ports. ∎

**Field bookkeeping.** AN's hypothesis is about the field k; OA's ports is about the characteristic. Step 2 needs
only: OA spectral points over k are AN spectral points over k (immediate), and OA's class depends only on the
characteristic (EG Lemma 2.3 [K-OA]). So "contracting over ℚ" gives ports in characteristic 0, which is exactly
the hypothesis of IM Theorem 7.1 (Lean: `PortZero`, stated over the algebraic closure of ℚ). I did not need the
converse transfer (AN prices over ℚ versus over ℚ̄).

**What Theorem A rests on.** AN F.6 (Anthropic; in the paper's Lean per its formalisation table, name
thm_poincare; I did not open the Lean). HC Theorem 4.2 (OpenAI; one-page proof which I read line by line: Lemma
4.1 is the standard barycentric smoothing, the iteration is a replacement product with Cesàro-averaged walks as in
Mendel–Naor; I found no gap; a Lean version exists). IM Theorem 7.1 for the 3-SAT conclusion (OpenAI; Lean
`middle_count_bridge`). To make it independent of OpenAI, see 2.5.

**A second derivation [D] (consistency check).** OA's proof of Prop. 11.2 uses cube exclusion only in the last
line of Lemma 11.3 ("The equality argument produces the excluded Q_ℓ"). Before that line it shows: if the
uniform gap fails, a limit placement of the Grassmannian has all squared distances equal to dim(U+V) − m, i.e.
σ_m is spectral. So the proof gives verbatim:

> **Proposition 11.2′ [D from K-OA].** If for some m (a power of two in their proof) the Grassmann metric σ_m is
> not a spectral metric over F, then F has ports.

Since ρ_m ⊂ σ_m, "ρ_m not a price" gives "σ_m not spectral" (for OA metrics; an AN price that is not an OA metric
is the only gap between the two derivations), which gives ports. The two routes agree.

### 2.3 Theorem B [D, from c1 + Theorem A]: a finite test for a faster 3-SAT algorithm

c1 Prop. 1 [our note; the referee in `next/review-link.md` called its use "correct but unnecessary" for Cor. 1′;
the equivalence itself was read there only in the direction (ii)⇒(i) and the pull-back monotonicity; direction
(i)⇒(ii) is AN's own Steps 2–7 of Theorem D.2 and Remark D.3, which says in so many words that outside the
contracting case √rk(a−a′) is a price for μ ≥ 3]:

- ρ_μ(a,b) = √rk(a−b) on Mat_μ(F₂). If ρ_μ is a price then D(μ) = √μ·D(1), so contracting fails at μ. [trivial]
- If ρ_μ is a price, so is ρ_{μ′} for μ′ ≤ μ (pull back along a ↦ diag(a,0)). [trivial]
- If contracting fails (at every μ), ρ_μ is a price for every μ ≥ 3. [K-AN, D.2 proof + D.3]

So **contracting over k ⇔ ρ_μ is not a price over k for some μ ⇔ ρ_μ is not a price for all large μ**, and

> **Theorem B.** (i) If for some μ ≥ 2 the metric √rk on Mat_μ(F₂) is not a price over ℚ (for instance μ = 3, 512
> points; or μ = 2, 16 points), then characteristic 0 has ports and 3-SAT is decidable in 2^{O(v^{1−δ})}·poly.
> (ii) If the five-point set M5 = {0, I, e₁₁, e₂₂, e₁₁+e₁₂} ⊂ Mat₂(F₂) (squared distances 2 on the pairs
> 0–I, e₁₁–e₂₂, (e₁₁+e₁₂)–e₂₂ and 1 on the other seven) is not a price over ℚ, the same conclusion holds.
> (iii) Contrapositive: under variable-count Weak ETH, for every μ there is a spectral point over ℚ on 2^{μ²}
> parties whose wire metric is (arbitrarily close to a multiple of) √rk; in particular M5 is a price. These are
> metrics of vertex sets of the Bruhat–Tits building of GL_{2μ}(F₂((t))) (c1 §2), not embeddable in Hilbert space
> (c1 §4, x5) and not tree metrics (they contain unit squares).

Proof of (i): ρ_μ not a price ⇒ ρ_{μ′} not a price for all μ′ ≥ μ, in particular for some μ′ ≥ 3 ⇒ (by AN D.2
and D.3: if contracting failed, ρ_{μ′} would be a price) contracting holds ⇒ Theorem A. (ii): M5 ⊂ Mat₂(F₂) with the restricted metric (x5 [N]: checked exactly),
and a restriction of a price is a price, so M5 not a price ⇒ ρ₂ not a price. This is the claim of
`ideas-dichotomy.md` Idea 2, with the same direction; it is correct. (iii) is the contrapositive plus IM 7.1.
A caution on (i) at μ = 2: "ρ₂ is not a price" gives "ρ₃ is not a price" by pull-back, and it is the latter that
contradicts D.3; the chain is fine.

"Finite" means: the object is one metric on 5, 16 or 512 points. Deciding whether it is a price is not a finite
computation: by c1's cover characterisation it is the asymptotic question whether the complete network on those
parties with √rk-weighted bonds has a cheaper cover. A single cheaper cover (one tensor identity, checkable by
machine) would prove (i) or (ii). There is no finite certificate known for the other side.

**Reading of (iii) as an existence theorem.** Under Weak ETH, OpenAI's and Anthropic's theorems together force a
spectral point over ℚ realising a higher-rank building-like metric. No explicit spectral point does this (c1 §3:
flattenings, quantum and support functionals give only partition-star metrics). This is the "wild space" asked
about in the brief; see Part 4.

### 2.4 Side by side: what each lab gets in each case

OpenAI's EG Theorem 1.2 says flats of every dimension exist over every field, so (given OA) the flat hypothesis
of AN holds. AN's thm_alt says flat or contracting; it does not say they exclude each other, and they need not:
Euclidean pull-backs to Mat_μ(F₂) have D(μ)²/D(1)² < 2 (c1 §4), so flats never contradict contracting. The open
question is exactly whether contracting ALSO holds, and beyond that whether ports holds.

Implications among the hypotheses, all for one characteristic:

    no flats of some dimension  ⇒  contracting  ⇒  ports            (AN D.2;  Theorem A)
    (false, given OA EG 1.2)        ⇔ ∃μ: ρ_μ not a price            (c1)
    no ports ⇒ not contracting ⇒ all ρ_μ, hence all flats, are prices
    not contracting ⇒ ports or no ports: OPEN  (see Part 4: the Grassmann graphs sit exactly at the borderline)

| Cell (flat true throughout) | Consistent? | (a) 3-SAT | (b) permanent / HC circuit size | (c) Boolean and network lower bounds | (d) our engine |
|---|---|---|---|---|---|
| **contracting, ports** | not excluded unconditionally; contradicts Weak ETH in char. 0 | char. 0: 2^{O(v^{1−δ})} deterministic (IM 7.1). Char. p: the count mod p of any volume-s network in 2^{s^{1−η}} (HC 13.1); a decision algorithm needs an isolation lemma of near-linear volume [C] | AN: 2^{c(log m)²/log log m} (thm_contracting) and also the flat bound 2^{c(log m)^{4/3}}. OA: 2^{N^ε} (HC 12.2). By Theorem A the OA bound applies whenever AN's contracting case does | list distinctness needs volume > n·w^{1+σ} for some small σ > 0 (MM 2.2, ports branch; Lean `manyList_full`), so our circuit corollary survives with a small exponent; the exponent-1/2 theorems S and M are NOT available | floors of b2 stay true (they need only flat); a 2^{v^{1−δ}} algorithm exists anyway, see below |
| **contracting, no ports** | **impossible** (Theorem A) | — | — | — | — |
| **not contracting, ports** | not excluded | as in the first row | AN: only the flat bound. OA: 2^{N^ε} | as in the first row | as in the first row |
| **not contracting, no ports** | the expected cell (forced in char. 0 by Weak ETH) | no algorithm from this source | AN: 2^{c(log m)^{4/3}}. OA: exp(c(log N)²/(log log N)²) (HC Part I) | Ω(n√log n) gates for polynomial/integer multiplication and shifts, Ω(n²√log n) for matrix products (our S, M; MM Lemma 4.1), tight by OA's upper bounds | floors true; nothing new |

Remarks.

- **OpenAI's unconditional permanent bound versus Anthropic's contracting-case bound.** HC Theorem 1.1 is
  exp(c(log N)²/(log log N)²) unconditionally. AN's contracting-case bound is 2^{c(log m)²/log log m}, larger by one
  factor log log in the exponent; AN's unconditional bound is 2^{c(log m)^{4/3}} (the flat case is the bottleneck).
  So OA's unconditional claim is essentially AN's contracting-case strength, in every case. OA gets it in the
  no-ports case from a different placement (one placement for all balanced cuts, built from non-expansion), and in
  the ports case from the much stronger 2^{N^ε}.
- **AN's contracting bound is weaker than what contracting gives.** AN's laws live on U_h and cost powers of
  log per cut (Λ = (lg M)^C in H.2), which is why AN stops at (log m)²/log log m. Via Theorem A and OA's
  bounded-degree compression the contracting case gives 2^{m^ε}. This is a statement about Anthropic's own case
  that Anthropic's paper does not contain [D, given K-OA HC 12.2].
- **(d) Is a ports algorithm compatible with our floors?** Yes, and it is a piece family. A rerouting identity
  is precisely "product of wires = sum of products of wires on another graph", i.e. an identity Σ A_i = f_C of
  the kind b2's Theorem 3 bounds. The flat floor for a configuration is the best Euclidean placement. For a
  crossing or Δ₃ it gives 1/√2 or 1/√3 per merge, which is what pins the engine. For "complete demand on the
  ports of a vertex, supply on an expander" the Euclidean floor is the scalar spectral gap of the graph, a
  constant. The port identity therefore does not beat any flat floor; it sits on a configuration where the floor
  is harmless. The six-party motif obeys the ℓ₂ law as well (‖c‖_q ≤ √H‖b‖_p in EG 12.1 is the same √ law).
  What ports add to the engine is not a better exponent per trade but **bounded degree restored at constant
  cost**, which lets the trade be iterated a·log s times (shared bits ×2^{−T}) instead of the engine's bounded
  number of levels with growing degree. So 2^{n/√log n} (engine, unconditional) and 2^{n^{1−δ}} (ports) are
  consistent with all our floors; the floors do not bear on which holds.

### 2.5 Re-basing on Anthropic's paper alone [D-sketch]

Theorem A's conclusion "fast 3-SAT" uses OpenAI's IM 7.1. Anthropic's own contracting-case machinery gives a
power-saving simulation directly:

- [K-AN, Theorem J.4 (thm_cut), contracting case]: "There are a multiple H ≥ 272 of 16 and constants C_cut, v₀
  such that […] whenever v ≥ v₀ and α satisfy (lg v)^{C_cut·α} ≤ v. For all τ and s with v^H ≤ τ ≤ v^{Hα} and
  s·v^{48} ≤ τ, some program of size at most v^H cuts (τ, s) into (v^H, v^{H−32}) with at most τv²/v^H pieces in
  at most τ/v^{24} steps."
- Meaning: the weighted sum over accepting runs of a nondeterministic τ-step computation equals a sum, over the
  ≤ 2^{O(τ/v^{24})} runs of the cutting program, of products of sums of pieces of v^H steps each.
- [D] Take α = 2, τ = v^{2H}. Brute force on the pieces costs 2^{O(v^H)} = 2^{O(τ^{1/2})}; enumerating the cutting
  runs costs 2^{O(τ^{1−12/H})}. So **under the contracting hypothesis over k, sums over the runs of a
  nondeterministic τ-step tape computation with weights in the finitely generated ring A ⊂ k are computable in
  2^{O(τ^{1−12/H})} operations.** With k = ℚ the ring A is ℤ[1/N] and the count is exact. A verifier for a
  sparsified 3-CNF with v variables and v^{1+4α′} clauses runs in τ = v^{1+4α′}·polylog steps on tapes, so
  3-SAT is in 2^{O(v^{1−δ})} for a small δ > 0.
- Not checked: uniformity of "some program of size at most v^H" in v (the laws are a fixed finite list, so it is
  at worst a fixed finite advice); the exact machine model of AN §I for the verifier; the polylog losses. This
  needs one careful reading of AN §§I–J by an executor (2 hours). If it holds, **"Anthropic's contracting
  hypothesis over ℚ contradicts Weak ETH" is a corollary of Anthropic's paper alone**, with no OpenAI input, and
  with it: under Weak ETH, AN's permanent bound in characteristic 0 is the flat-case bound, and ρ_μ is a price
  over ℚ for all μ.

### 2.6 Which known necessary conditions could exclude M5 or ρ₃, and which constructions could realise them

Necessary conditions on prices, and their verdict on ρ_μ (all [K] from our notes unless marked):

| Condition | Source | Verdict on ρ_μ / M5 |
|---|---|---|
| Triangle inequality, CAT(0) four-point (quadrilateral / Bruhat–Tits CN), flat rectangle rigidity | AN thm_cn, C.4; EG 4.3–4.5 | satisfied: ρ_μ is a subset of a Euclidean building (c1 §2) |
| Every inequality valid in all CAT(0) spaces (Reshetnyak, Sturm's variance inequalities, Gromov's Cycl_k, …) | follows from the above for any metric of a CAT(0) space | satisfied for the same reason. **So no LP/SDP over "CAT(0) conditions" can exclude ρ_μ.** |
| Crossing inequality B.3 with hubs | AN B.3 | holds in Hilbert space [R, c1]; no violation found for ρ₂, ρ₃ with hubs in Mat_μ(F₂), trees, hyperbolic plane [N, c1]; [C] holds in every CAT(0) space. x5 [R]: no composition of crossing identities can refute a space satisfying B.3 |
| Four-party rank inequalities (subadditivity, CHLW 1–2, L2) | w1 | these constrain flattening ranks of one tensor, i.e. the explicit cut-type points; they give lower bounds on covers, not obstructions to a price. They cannot exclude ρ_μ |
| Shared-label prices: diam(S) ≤ δ(S) ≤ tree length; on flat pieces δ(S) = mean width; submodularity on intersecting sets | EG (2.1), 5.2, 5.3 | constrain the extension of a price to diagonal tensors on the flat squares of ρ_μ. No contradiction is visible: two flat squares sharing a diagonal each get mean-width prices. Untested systematically |
| Joint convexity of prices along geodesics | EG 3.3 | a constraint on all tensors, not on the wire metric alone |

Verdict: **nothing known excludes M5 or ρ₃**, and no metric-only argument can, because the wire metric is CAT(0).
An exclusion must be a new tensor identity (a cheaper cover of an M5-weighted network; x5 found none).

Constructions of prices, and whether they reach M5:

| Construction | Reaches M5 / ρ_μ? |
|---|---|
| Flattening ranks, quantum and support functionals (partition-star metrics) | no: they satisfy the four-point equality on four blocks; ratio to M5 lengths 0.71–0.89 (x5 [N]) |
| Euclidean flats (EG 1.1) | no: M5 has Gram determinant −1/4 (x5) |
| Trees (laminar families of cuts; AN thm_tree; MM §7 valuation trees) | no: M5 contains a unit square with diagonals √2 |
| ℓ₂ products of trees and flats | not known to be prices at all (HC 6.1). Also `ideas-dichotomy.md` reports tree×tree does not contain M5; my own quick derivation agrees for axis-parallel squares [D] |
| Rescaling, convex hulls, ultralimits | preserve the class but create nothing non-Euclidean from flats and trees: the closure of {Hilbert, trees} under these is {Hilbert spaces, ℝ-trees} |
| Valued prices / Gauss lift (MM §5–6): prices over a field with a valuation | the natural source of building-like geometry (lattices in F₂((t))^n are exactly c1's L_a). MM uses them only to produce trees under its strict-saving hypothesis. Whether a valued price over F((t)) induces an ordinary price on lattice classes with the building metric is the most promising constructive question [C] |
| Non-constructive: "not a price ⇒ contracting ⇒ ports ⇒ contradiction" | the only known route (OA proved flats this way, with cube exclusion supplying a second ingredient). With Weak ETH as the contradiction it is Theorem B(iii) |

---

## Part 3. What is known in metric geometry

### 3.1 Definitions

For a finite regular graph G and a metric space Y, the nonlinear spectral gap is
λ₁(G,Y) = inf over non-constant placements of (edge energy)/(pair energy), with squared distances; G_n is an
expander family with respect to Y if λ₁(G_n,Y) is bounded below. Ports = "some bounded-degree family is an
expander family with respect to the whole class X_χ, uniformly".

### 3.2 Results (exact pointers; search results noted where I could not open the paper)

1. **Gromov's cones; Kondo.** [K] Gromov ("Random walk in random groups", GAFA 2003) noted that the Euclidean
   cone over a graph of girth g, with edges rescaled to length 2π/g, is CAT(0), so large-girth expanders are not
   expanders with respect to their own cones. Kondo ("CAT(0) spaces and expanders", Math. Z. 271 (2012)) built the
   first complete CAT(0) space with Izeki–Nayatani invariant δ = 1, containing such configurations. (I confirmed
   by search that Kondo's is cited as the first δ = 1 example, e.g. in Toyoda arXiv:1102.0729; I did not open
   Math. Z.) In such a cone, edge energy ≈ (2π/g)² and pair energy ≈ 4, so the Poincaré constant is ≈ g² ≈ (log n)²:
   the largest possible.
2. **Mendel–Naor**, "Expanders with respect to Hadamard spaces and random graphs", Duke Math. J. 164 (2015),
   arXiv:1306.5434. [K, abstract]: there is a Hadamard space X and a sequence of 3-regular graphs that are
   expanders with respect to X, although random regular graphs are almost surely not expanders with respect to X.
   So for one Hadamard space the answer depends on the graph family: "is an expander in the classical sense" is
   neither necessary nor sufficient information. This is the template for the cell {not contracting, ports}.
3. **Mendel–Naor**, "Nonlinear spectral calculus and super-expanders", Publ. IHÉS 119 (2014). [K] The zig-zag
   iteration with Cesàro averages: a class of spaces for which (i) Cesàro averaging of walks improves the Poincaré
   constant ("nonlinear spectral calculus", true in Hadamard spaces via barycentres) and (ii) one base graph has a
   small enough constant, admits bounded-degree expanders. HC Lemma 4.1 + Theorem 4.2 and EG §11.1.3 are this
   argument with explicit constants; EG cites [20, Cor. 1.9], [21, Thm 1.13(V), §8], [22, Thm 3.4].
4. **Izeki–Nayatani invariant.** [K] Izeki–Nayatani, "Combinatorial harmonic maps and discrete-group actions on
   Hadamard spaces", Geom. Dedicata 114 (2005). For a finitely supported probability measure ν on a complete
   CAT(0) space Y with barycentre b: δ(ν) = inf over maps φ: supp ν → Hilbert space with ‖φ(p)‖ = d(p,b) and
   ‖φ(p)−φ(q)‖ ≤ d(p,q) of ‖∫φ dν‖²/∫‖φ‖² dν; δ(Y) = sup_ν δ(ν) ∈ [0,1]. Theorem (as quoted in Toyoda,
   arXiv:1102.0729, Prop. 3.3): (1−δ(Y))·μ₁(G) ≤ λ₁(G,Y) ≤ μ₁(G), where μ₁ is the scalar gap. (One survey quotes
   an extra factor 1/2 on the left; the constant should be checked in the original before use.) Hence: if
   δ(Y) ≤ c < 1 for every Y in a class, **every** classical expander family is an expander family for the class.
5. **Values.** [K] δ = 0 for Hilbert spaces and for trees (Izeki–Nayatani 2005; the search confirms "δ < 1" for
   Hilbert spaces, Hadamard manifolds, trees, CAT(0) cube complexes and Bruhat–Tits buildings, and δ ≤ 1/2 for
   CAT(0) cube complexes (Fujiwara–Toyoda, arXiv:1012.4147); the exact value 0 for trees/Hilbert is from the
   original paper and standard). For the building of SL₃(ℚ₂): δ ≤ 0.4122, and the method gives a bound above 1/2
   for SL₃(ℚ_p), p ≥ 3 (Izeki–Nayatani, quoted in the survey arXiv:math/0612736). δ is stable under ℓ₂ products
   and limits (δ(X×Y) ≤ max; Izeki–Kondo–Nayatani).
6. **Toyoda.** [K] "CAT(0) spaces on which a certain type of singularity is bounded" (arXiv:1010.1963): δ(Y) < 1
   if the family of spaces of directions (tangent cones) of Y is Gromov–Hausdorff precompact. "Fixed point
   property for a CAT(0) space which admits a proper cocompact group action" (arXiv:1102.0729): a geodesically
   complete CAT(0) space with a proper cocompact isometric action has δ < 1, so every expander family is an
   expander family with respect to it. Both are statements about ONE space of bounded local complexity. Neither is
   uniform over buildings of growing rank.
7. **Izeki–Kondo–Nayatani**, "Fixed-point property of random groups" (Ann. Global Anal. Geom. 2009) and "N-step
   energy of maps and fixed-point property of random groups" (arXiv:1210.5829): random groups fix points in all
   CAT(0) spaces with δ ≤ C < 1; extended to a class including all Hadamard manifolds.
8. **Strong property (T).** [K] V. Lafforgue (Duke 2008; J. Topol. Anal. 2009): SL₃ over a non-archimedean local
   field has strong Banach property (T); the expanders from its lattices do not coarsely embed in uniformly convex
   Banach spaces. de la Salle; de Laat–de la Salle (arXiv:1401.3611, 1705.03296, 2303.01405): strong (T) and fixed
   points on uniformly convex Banach spaces for higher-rank groups and lattices. These give super-expanders for
   Banach targets. I found no statement giving expanders with respect to all Euclidean buildings of all ranks, or
   with respect to all CAT(0) spaces of some non-compact local type.
9. **All Hadamard spaces at once.** I did not find a citable theorem that no bounded-degree family is an expander
   family with respect to all Hadamard spaces simultaneously. For large-girth families it is item 1. In general it
   is [C] (HC Theorem 4.2 reduces it to: every bounded-degree graph has Poincaré constant ≥ c log n against some
   Hadamard space). It is not needed below.

### 3.3 Two derivations that locate the spectral class [D]

**(a) Buildings of growing rank have δ → 1, and classical expanders fail against them.** Let Y be any complete
CAT(0) space containing (Mat_μ(F₂), ρ_μ) isometrically, e.g. (after scaling by √2) the Bruhat–Tits building of
GL_{2μ}(F₂((t))) by c1 §2 [K-ours]. Let ν be uniform on Mat_μ(F₂), b its barycentre.

- Every 1-Lipschitz map φ of (Mat_μ(F₂), ρ_μ) into a Hilbert space has E‖φ(a)−φ(a′)‖² ≤ 2 for independent
  uniform a, a′. (Fourier on F₂^{μ²} as in c1 §4: the energy at frequency B is weighted by 1/2 for uniform
  differences and by p₁(rk B) > 1/4 for rank-one differences, and rank-one differences have ‖·‖² ≤ 1.) So
  Var φ ≤ 1.
- E d(a,b)² ≥ E ρ_μ(a,a′)²/4 ≥ (μ−1)/4 by the triangle inequality (the mean rank of a uniform matrix exceeds μ−1).
- Hence ‖Eφ‖² = E‖φ‖² − Var φ ≥ E d(a,b)² − 1 and δ(Y) ≥ δ(ν) ≥ 1 − 4/(μ−1).

So **the Bruhat–Tits buildings of GL_n(F₂((t))) have Izeki–Nayatani invariant → 1 as n → ∞** (each one has δ < 1 by
Toyoda). Equivalently: the Cayley graph Cay(Mat_μ(F₂), rank-one matrices) has scalar spectral gap ≥ 1/2 (every
nontrivial character sees more than 1/4 of the generators with sign −1) but nonlinear Poincaré constant
E ρ²/1 ≈ μ against the building. I have not found this in the literature; it is elementary and should be
checked for novelty before being claimed.

**(b) The borderline is hit exactly.** For G_μ = Cay(Mat_μ(F₂), rank-one): n = 2^{μ²}, d ≈ 2^{2μ},
β = μ ≈ 2·log n/log d. For the Grassmann graph J of m-planes in F₂^{2m} with σ_m: β = m ≈ log n/log d as well
(n ≈ 2^{m²}, d ≈ 2^{m}). In the tangent cone at a vertex (the Euclidean cone over the spherical building of
GL_N(F₂)): nested subspaces of dimensions k, k+1 near N/2 are at angle ≈ 2/√N, generic pairs of half-dimensional
subspaces are nearly opposite; again β ≈ N ≈ 2 log n/log d. HC Theorem 4.2 says that without ports every graph has
β ≥ c·log n/log(d+1). So **if these building metrics are prices, the dense graphs attached to them already have
the no-ports growth rate, with the right dependence on the degree.** This is a snowflake phenomenon: ρ_μ is the
square root of the graph metric of G_μ, so pair energy/edge energy = mean graph distance ≈ diameter ≈ log n/log d.
In a Hilbert space the square root of a graph metric can be isometric only for graphs that are poor expanders
(the cube); in a building it happens for a graph with spectral gap 1/2.

**(c) What this does not give.** Ports needs only ONE bounded-degree family. Item 2 (Mendel–Naor) shows that a
space defeating classical expanders can still admit expanders. So (a)–(b) do not prove "not contracting ⇒ no
ports". The missing statement is purely metric:

> **Question Q-build [open, metric geometry].** Is there a bounded-degree family of graphs that is a uniform
> expander family with respect to all Bruhat–Tits buildings of GL_n(F₂((t))), n → ∞ (or with respect to the
> metrics σ_m, all m)? If NO: contracting ⇔ ports, and ports ⇔ "some ρ_μ is not a price". If YES: the cell
> {not contracting, ports} cannot be excluded by these metrics alone.

A sanity check [D]: Anthropic's own graphs (U_h with the h−1 elementary generators, placed by g ↦ g·U₀ on the big
cell) have pair energy ≈ h/4 and edge energy ≤ 1 in σ, i.e. β = Θ(h) = Θ(√log n) at degree h−1. That matches the
form of AN F.6 (β ≤ C₀(h−1)), so these graphs do not separate the cases either.

### 3.4 The decisive question, restated

Which Hadamard spaces are spectral? After Parts 2–3:

- If some σ_m (equivalently some ρ_μ) is NOT spectral: ports (Prop. 11.2′ / Theorem A). No Izeki–Nayatani
  argument is needed; the zig-zag iteration does it.
- If all σ_m are spectral: δ(X_χ) = 1, the Izeki–Nayatani route is closed, and ports ⇔ a positive answer to a
  Q-build-type question for the full (unknown) class X_χ.

So H14 of our LOGBOOK ("if every spectral space has δ bounded below 1, ordinary expanders are ports") is true but
its hypothesis is equivalent to something at least as strong as contracting, and the sharper statement is
Theorem A. The brief's alternative "some spectral space contains cones over expanders coarsely ⇒ no ports" is
right as stated; what Weak ETH is known to force is weaker (the buildings), see Part 4.

---

## Part 4. Which spaces ARE spectral: the evidence on each side

### 4.1 What is known to be spectral

| Space | Source | Status |
|---|---|---|
| Cut pseudometrics (one cut) | flattening rank | explicit, every field |
| Star metrics d(u,v) = θ_u + θ_v, and partition-star metrics | quantum functionals over ℂ (CVZ); Strassen's support functionals on wires, every field (b2 §2) | explicit |
| Tree metrics | laminar families of cuts; AN thm_tree works with tree networks; MM §7 builds trees "in which two branches meet at the valuation of the difference of their parameters" under its strict-saving hypothesis | explicit for stars; general trees via geodesic extension (EG 3.1(2) adds a star centre) [D: every finite tree metric is obtained from a cut metric by repeated use of EG Theorem 3.1; not written out] |
| Hilbert spaces, all dimensions | EG Theorems 1.1, 1.2 | [K-OA]; proof by contradiction, no explicit points; Lean for finite dimension |
| Segments, geodesic completions, convex hulls, ultralimits, rescalings of the above | EG 3.4, 4.3, §2.3 | [K-OA]; AN Prop. C.3 for the CAT(0) completion |
| √rk on Mat_μ(F₂), Grassmann metrics σ_m (vertex sets of buildings over F₂((t))) | AN D.3 if contracting fails; forced in char. 0 by Weak ETH (Theorem B(iii)) | conditional |
| ℓ₂ products | — | NOT known (HC 6.1 gives only a Zorn subclass) |
| Anything containing an expander coarsely (cones, Kondo-type) | — | nothing; forced only indirectly, see 4.3 |

MM's "tripod" is not a new wire geometry: three tips at pairwise distance 2 is a star metric. What is non-flat
there is the price of the shared three-way label (rate 8/3 instead of the Euclidean mean width), i.e. the
extension of the price to diagonal tensors, not the metric.

### 4.2 Does closure alone force wild spaces? No.

[D] The class {Hilbert spaces, ℝ-trees, and their closed convex subsets} is closed under rescaling, closed convex
subspaces and pointed ultralimits (an ultralimit of Hilbert spaces is a Hilbert space; an ultralimit of trees is
an ℝ-tree). It contains every space in the first five rows of the table. It has δ = 0, so every expander family
is a port family for it. Hence the known closure properties plus the known examples are consistent with ports.
If products were allowed the class would grow to products of trees and flats (still δ = 0); buildings of rank
≥ 2 are not obtained this way (branching flats; M5 is not in tree × tree).

So any proof of "no ports" must produce a spectral point of a genuinely new kind. Conversely the same toy class
shows that the axioms used so far cannot prove no ports: c1 §4 already observed that Hilbert pull-backs form a
model of all the price axioms of AN §§A–D in which flat and contracting both hold.

### 4.3 What OpenAI's logic forces, and whether the papers construct it

Chain in characteristic 0 under Weak ETH: no ports (IM 7.1) ⇒ contracting fails (Theorem A) ⇒ all ρ_μ, σ_m are
prices (AN D.2/D.3; EG 11.3). So the forced wild spaces are **Euclidean buildings of unbounded rank over
F₂((t))** (more precisely the convex hulls of the rank metrics in a price space; by the flat-rectangle rigidity
used in AN D.2 Steps 4–7 these contain the solid cubes [0,1]^μ and branch like the building).

Beyond that, no ports forces more (HC Theorems 4.2, 5.1, 6.1, all [K-OA]):

- for EVERY bounded-degree graph on n vertices a placement with pair energy ≥ c log n × edge energy (4.2);
- an "information" inequality: if demand steps are β times longer (in mean square) than physical steps in every
  placement, then H(demand step) ≤ Cβ(1 + entropy rate of the physical walk) (5.1). Read backwards: in the
  extremal spaces, squared distance behaves like transmitted information, d² ≈ bits/const. The rank metric has
  exactly this form on its range of scales: one rank-one step = 2μ bits = squared length 1; a uniform matrix =
  μ² bits = squared length ≈ μ. A space witnessing no ports for bounded-degree graphs must behave like this down
  to steps of O(1) bits, i.e. over a range of scales of ratio log n rather than √log n;
- a product-closed subclass without ports, containing ℓ₂ (HC 6.1, §2.3).

Do the papers construct or hint at such a space? **No.** HC Part I, MM Lemma 4.1 and IM Lemma 8.2 only use the
existence of bad placements, obtained from the contrapositive of the zig-zag iteration; no spectral point is
exhibited, and the authors say the proof "requires no classification of the characteristics" (HC §1.3). The only
non-Euclidean, non-tree metrics that appear by name anywhere in the two labs' papers are AN's √rk (Remark D.3)
and, implicitly, the limit configuration in EG Lemma 11.3.

### 4.4 Could the class be "Euclidean buildings and their limits"?

[C] Candidate description under "not contracting": X_χ ⊇ {ℝ-trees, Hilbert spaces, buildings B_n of
GL_n(F_q((t))) for all n and (probably) all q, and limits}. Asymptotic cones of such buildings are ℝ-buildings;
unbounded rank gives infinite-dimensional objects. For this class:

- each B_n alone admits all classical expanders (Toyoda), with constant degrading as n grows (3.3(a));
- uniformly in n nothing is known (Q-build). Lafforgue's strong (T) concerns actions of rank-2 groups on Banach
  spaces, not Poincaré inequalities with building targets of growing rank; Izeki–Nayatani's estimates are for Ã₂;
  Oppenheim's angle criteria (used by AN in F.2–F.3 in the same spirit: "windows meet almost at a right angle")
  give fixed-point theorems for groups acting on such spaces, again for a fixed space.

If X_χ were exactly this class, ports would be equivalent to a positive answer to Q-build. I see no reason for
X_χ to be exactly this class; the entropy picture in 4.3 suggests that no ports needs spaces that branch at every
scale (like cones over expanders), which buildings over a fixed residue field do only at integer scales.

### 4.5 A cleaner way to see what is being asked: network coding for tensors [D]

Let G be a supply graph with capacities c_e and D a set of demand pairs with rates r_e. Write
S = ⊗_{e∈G} E_e(2^{c_e}) and T = ⊗_{e∈D} E_e(2^{r_e}) (products of wires). By Strassen's theorem [K: Strassen 1988;
EG Lemma 2.2 is the strict form], T^{⊗fn} is a restriction of S^{⊗(n+o(n))} iff f·log F(T) ≤ log F(S) for every
spectral point F, i.e.

    f*(G, D) = min over spectral wire metrics d of  Σ_{e∈G} c_e d(e) / Σ_{e∈D} r_e d(e).

This is the LP dual of multicommodity flow with "all metrics" replaced by "spectral metrics". Since cut metrics
are spectral, f* ≤ sparsest-cut bound; since the shortest-path metric of G is a feasible dual for flow,
f* ≥ max concurrent flow (routing by contracting wires along paths).

- **Tensor coding beats routing.** For the Okamura–Seymour instance (G = K_{2,3}, demands the three pairs inside
  the 3-side and the pair on the 2-side) the flow value is 3/4 and the cut bound is 1. Every optimal metric of the
  flow dual satisfies d(v_i,v_j) = d(v_i,u_k) + d(u_k,v_j) and d(u_1,u_2) = d(u_1,v_i) + d(v_i,u_2); putting this
  into the quadrilateral inequality (EG (4.5) / AN C.4(b)) for (v_1,u_1,v_2,u_2) forces a side to vanish, and
  running over the three quadrilaterals collapses everything. So no optimal dual metric is CAT(0), and by
  compactness **f*(K_{2,3}) > 3/4** over every field. Star metrics give f* ≤ 1. The exact value is a clean small
  open problem; it is the first instance of "which five-point CAT(0) metrics are spectral".
  This rests only on "prices are CAT(0)", which Anthropic proves (thm_cn) and has in Lean.
- The quadrilateral inequality itself is the statement that two crossing wires can be supplied from the four
  sides more cheaply than routing predicts (AN's crossing identity B.2). So the √ law of our engine and the
  failure of "routing is optimal" are the same fact.
- **Ports in this language.** Ports ⇔ for a bounded-degree expander family, the complete-graph demand can be
  obtained from a direct sum of edge supplies at constant ℓ₂ cost, i.e. tensor coding gains the full factor
  ≈ log n over routing (in the ℓ₂ normalisation: log² n → O(1)). No ports ⇔ on every bounded-degree graph the
  gain is at most log n (pair energy ≥ c log n × edge energy, against the trivial log² n).
- Context [K, search]: the classical multiple-unicast (Li–Li) conjecture, "coding = routing in undirected
  networks", was reported refuted in October 2026 (arXiv:2610.09367, 2610.10108, 2610.20079; unrefereed). Classical
  information-theoretic coding and tensor restriction are different resources, so neither result implies the
  other, but the old intuition that would have made "no ports" look like a tensor analogue of a believed
  conjecture is gone. Braverman–Garg–Schvartzman (ITCS 2017) proved a dichotomy for the classical gap (either no
  gap or a gap of (log n)^c), which is the same shape as HC Theorem 4.2.

### 4.6 Evidence summary

For ports (some characteristic):
- nothing excludes it unconditionally; the toy class of 4.2 has ports;
- every explicit spectral point is a tree/star point (δ = 0);
- in positive characteristic there is not even a conditional exclusion in the release.

For no ports:
- Weak ETH (characteristic 0), via a Lean-formalised implication;
- in a no-ports world all of OpenAI's exponent-1/2 results are tight and coherent (upper bounds n(log n)^{1/2+ε}
  proved unconditionally for multiplication, Fourier transforms, sorting-type problems); in a ports world the
  true log-exponents would be some unexplained σ < 1/2;
- OpenAI proved that the rigid alternative closest to ports (a largest flat) is false in every characteristic;
  the mechanism (rigidity ⇒ too-good routing ⇒ self-simulation paradox) plausibly extends to contracting (5.E2).

Against a quick decision either way: ports ⇒ a 2^{v^{1−δ}} 3-SAT algorithm; no ports ⇒ unconditional
Ω(n√log n) Boolean circuit lower bounds for multiplication. Each would be a landmark; neither lab claims either.

---

## Part 5. Attack routes, ranked, each with a first experiment (≤ 3 hours for an executor)

Ranking is by (value × chance) for us, not by importance of the target.

### Route 0 (first). Nail down Theorems A and B and the re-basing

- **Why first.** It is the only new, checkable, lab-independent statement we have: "Anthropic's contracting
  hypothesis over ℚ ⇒ 3-SAT in 2^{O(v^{1−δ})}", hence "Weak ETH ⇒ the contracting hypothesis is false in
  characteristic 0 ⇒ √rk metrics are prices over ℚ ⇒ Anthropic's permanent bound in characteristic 0 is the
  flat-case one, and in the contracting case it can be raised to 2^{m^ε}".
- **Experiment 0a (referee, 2 h).** Check §2.2 line by line: AN F.6 as stated in the paper and in AN's Lean
  (thm_poincare: is it stated for "every price on U_h", with C₀ independent of h?); the normalisation in my
  step 2; HC Theorem 4.2's proof (Lemma 4.1, the rounding of S, the cloud step) and the Lean constant; the
  inclusion {OA spectral points} ⊆ {AN spectral points}; EG Lemma 2.3 for the field transfer.
- **Experiment 0b (reader, 3 h).** AN §§I–J: write out the corollary of Theorem J.4 "contracting over ℚ ⇒ sums
  over runs of τ-step nondeterministic tape computations in 2^{O(τ^{1−12/H})}", then the 3-SAT corollary with
  sparsification. Decide: is it a corollary of Anthropic's paper alone? Odds it goes through: 65%.
- Odds Theorem A survives review: 85%.

### Route A. PORTS via a rigidity statement (the only live form of "bounded Izeki–Nayatani invariant")

- **Target.** Show some ρ_μ (or M5) is not a price: one tensor identity, i.e. a cover of an M5- or ρ₂-weighted
  wire network that is cheaper than its ρ-length. By Theorems A/B this gives a 2^{v^{1−δ}} 3-SAT algorithm.
- **Status.** x5 searched compositions of crossing identities and proved they cannot work in any space
  satisfying B.3; no cover found. Metric-only arguments are impossible (§2.6). Under Weak ETH the target is false
  over ℚ.
- **On the experiment proposed in the brief** (LP/SDP over metrics satisfying CAT(0) + B.3 on Mat₂(F₂) or on a
  small expander): its outcome is predetermined. ρ₂ is feasible (it is a building metric, and c1 found no B.3
  violation), so the LP returns the trivial constant D(2)² = 2·D(1)². On a small bounded-degree expander the LP
  over CAT(0)-embeddable metrics is the Poincaré constant against all Hadamard spaces, which is the Gromov–Kondo
  value. Not worth running. The one useful variant: **prove or refute [C] "B.3 holds in every CAT(0) space"**
  (c1). If B.3 fails somewhere in a building, B.3 becomes a genuinely new constraint and the LP becomes
  informative.
- **Experiment A1 (2 h).** Numerical search for a B.3 violation in the building of GL₄(F₂((t))) with hubs at
  arbitrary vertices and edge midpoints (c1 tested hubs in Mat_μ(F₂) only), and in the Euclidean cone over the
  incidence graph of the Fano plane (the tangent cone of an Ã₂ building).
- Odds of proving ports this way: < 1% (3% that contracting is true at all over ℚ).

### Route B. NO PORTS via an explicit wild price

- **Target.** A spectral point whose wire metric defeats bounded-degree expanders, e.g. the cone over a
  large-girth graph, or any metric with d² ≈ information at all scales (§4.3).
- **Which step is missing.** Every step. Flats, trees, rescaling, convex hulls and limits stay inside
  {Hilbert, ℝ-trees} (§4.2). Products are not available. Local-to-global gluing (a cone over a tree-like ball is
  locally a union of flat sectors, each of which is spectral) is not available: spectrality is a condition on all
  finite subsets and there is no Cartan–Hadamard theorem for it. The only existence technique is "not a price ⇒
  too-good identities ⇒ contradiction".
- **Sub-route B1 (constructive, the best idea here).** Valued prices. MM §5–6 constructs prices over a valued
  field K = Frac E[t^ℚ] (the "Gauss lift": p(cT) = p(T) − ν(c), nonincreasing under integral restrictions). Lattice
  classes in K^n are the vertices of the building, and c1's L_a are such lattices. Question: does a valued price
  induce an ordinary spectral point on a finite set of lattices (party = lattice, a tensor is transported by
  the base changes between lattices) whose wire metric is the building distance? If yes, ρ_μ is a price over
  every field, contracting is false unconditionally, and Anthropic's theorem loses its second case.
  **Experiment B1 (3 h):** read MM §§5–6 and EG §3; define the candidate "lattice price" for n = 2 (the tree of
  GL₂); check the axioms on wires and whether the tree metric comes out; then n = 4 and the five points of M5.
  Odds it works: 5%. Value if it works: high (an unconditional theorem about both labs' case splits).
- **Sub-route B2.** Q-build (§3.3): find, for every bounded-degree graph, a bad placement in buildings of growing
  rank, or prove there are expanders against all of them. **Experiment B2 (3 h):** numerics on small cases:
  place Cayley graphs of SL_N(F₂), N = 3, 4 (168 and 20160 elements; bounded generating sets) into the
  Grassmann metric by g ↦ g·U₀ and by random orbit maps, and optimise pair energy/edge energy; compare with the
  scalar gap. Literature check: expanders with respect to buildings of unbounded rank (Oppenheim; de la Salle;
  Kassabov's uniform expanders of SL_N(F_p)). Outcome is evidence only.
- Odds of proving no ports in any characteristic by us: < 2%. It implies unconditional superlinear Boolean
  circuit lower bounds with the sharp exponent; expect it to be as hard as it sounds.

### Route C. Positive characteristic

- [K-OA] The release excludes ports only in characteristic 0 and only under Weak ETH. Nothing is said for
  characteristic p. Field transfer (EG Lemma 7.1) goes one way: a metric realised over F_p for infinitely many p
  is realised over ℚ. So X_0 contains the "common part" of the X_p; ports in characteristic 0 does not follow from
  ports in some characteristic p, nor conversely.
- **Could characteristic 2 have ports with no contradiction?** Yes as far as anything proved goes. It would give:
  (i) HC_N needs 2^{N^ε} gates in characteristic 2 (HC 12.2); (ii) the count mod 2 of any volume-s bit network,
  in particular ⊕3-SAT after sparsification, in 2^{O(s^{1−η})} (HC 13.1 is stated "over any field of this
  characteristic"); (iii) MM Theorem 2.2 over F₂ with a small σ < 1/2 and no exponent-1/2 circuit bounds over
  F₂ from this source; (iv) via an isolation lemma, a randomised 3-SAT algorithm in 2^{v^{1−δ′}}, **provided**
  isolation can be done with XOR constraints of total volume v^{1+o(1)} and success probability 2^{−v^{1−δ}}.
  Valiant–Vazirani costs volume ≈ v² (useless here); the Calabro–Impagliazzo–Kabanets–Paturi isolation lemma for
  k-CNF trades success probability 2^{−εv} for width; whether it reaches the power-saving regime is the thing to
  check. **Experiment C1 (2 h):** work out (iv). If it holds: "ports in ANY characteristic refutes randomised
  Weak ETH", so Weak ETH (randomised form) gives no ports everywhere and our Theorems S and M hold over F₂ in the
  M1 form under one standard hypothesis. That is a real strengthening of our conditional theorems and costs only
  reading. Odds: 50%.
- Is characteristic p easier? I see no Frobenius argument. The buildings in §2 are over F₂((t)) because the index
  set is Mat_μ(F₂), for every coefficient field; the coefficient characteristic enters only through which tensor
  identities exist. One genuine difference: in characteristic 2 the permanent is the determinant and exterior
  and symmetric constructions coincide, so crossing-type identities may have extra relatives there.
  **Experiment C2:** rerun x5's small cover searches over F₂ and F₃ instead of ℚ (exact linear algebra).

### Route D. Run the implication backwards as an algorithm hunt

- **Can a weaker, provable expansion property give an intermediate algorithm?** Two obstacles, both structural.
  (1) An identity exists iff the metric inequality holds at ALL spectral points (Strassen duality). Expansion
  with respect to flats and trees only proves nothing about restrictions. (2) HC Theorem 4.2 is a dichotomy:
  the Poincaré constant of bounded-degree graphs over the spectral class is O(1) (ports) or ≥ c log n on every
  graph. There is no intermediate regime such as (log n)^{1/2} to exploit.
- What is unconditional: the six-party motif and crossing identities (CAT(0) only), which is what our engine and
  OpenAI's n(log n)^{1/2+ε} upper bounds use. This suggests a **gap theorem** rather than an algorithm:

  > [C] **Engine gap.** If a network-rewriting algorithm of the engine's type (exact expansion into terms with
  > fewer shared bits, fixed topology per term) contracts every volume-s bounded-degree network in
  > 2^{O(s/(log s)^c)} for some c > 1/2, then ports holds, hence 2^{O(s^{1−η})}.

  Heuristic: MM Lemma 4.1 says that without ports a fixed topology that realises r wires with q-way uncertain
  destinations has size Ω(r√log q); rewriting a network into terms that fall apart is such a realisation.
  **Experiment D1 (3 h):** formalise "engine type" so that MM Lemma 4.1 / IM Lemma 8.2 apply, and derive the
  bound "shared bits ≥ s/O(√log s) in some term" under no ports. If it works we get: *the exponent 1/2 in
  2^{n/√log n} is optimal for this class of algorithms unless 3-SAT is in 2^{n^{1−δ}}*. A conditional optimality
  theorem for both labs' ETH refutations, phrased with no reference to tensors. Odds of a clean statement: 25%.
- Also worth one hour: **does the engine extend to exact #3-SAT mod p and to network contraction at
  2^{s/√log s}?** If yes it is the unconditional shadow of HC 13.1 and should be stated.

### Route E. Wild ideas

- **E1. Make ports refute itself.** Under ports, every permutation demand π on the N vertices of a port graph
  satisfies Σ_i d(x_i,x_{π(i)})² ≤ 4γN·E_edges (triangle inequality through one vertex plus the Poincaré
  inequality), so by EG 12.1 every fixed permutation of N h-bit records is realised on ONE bounded-degree topology
  of size O(√γ·N·h), with vertex maps depending on π. MM §4.3 shows that under ports the data-dependent version
  (the tagged-permutation tensor) costs ≥ N·h^{1+σ′}. So under ports the rerouting maps must depend on π in a
  way that costs more than a factor h^{σ′} to compute from the tags. If one could show the maps can be chosen
  with local dependence on π (they come from Strassen duality, so nothing is known about them), ports would be
  refuted unconditionally in every characteristic, and all the exponent-1/2 lower bounds would follow. I checked
  one naive version (Valiant two-hop routing over a complete-graph demand with recursion); it fails at the base
  case exactly as classical switching does (cost N h·log N). **Experiment E1 (2 h):** read EG §§12–14 for what
  is known about the dependence of the motif maps on the demand; decide whether "locality" can even be stated.
- **E2. Refute contracting the way OpenAI refuted a largest flat.** EG Parts II–III: rigidity (cube exclusion) ⇒
  ports AND cheap routing gates (§9, via local Euclidean coordinates on a maximal flat) ⇒ a network simulates a
  larger one ⇒ contradiction. Under contracting we have the first half (Theorem A) and a different rigidity
  (some Grassmann metric is excluded). If the excluded Grassmann configuration can drive the local tests of EG §9
  the way the excluded cube does, contracting is false over every field, unconditionally. Then: Anthropic's
  second case disappears, all √rk metrics are prices, buildings of every rank are spectral, and ports reduces to
  Q-build. EG §9 uses the maximal flat heavily (Lemma 9.5 "local flattening"), so this is a research programme,
  not an afternoon. **Experiment E2 (3 h):** locate every use of cube exclusion in EG §§8–10 and say for each
  whether "σ_m is not spectral" could replace it.
- **E3. The Okamura–Seymour rate.** Compute lower bounds on f*(K_{2,3}) by finding explicit restrictions.
  **Experiment E3 (3 h):** alternating least squares for local maps taking the K_{2,3} supply with bond
  dimension 2 on each edge to the four demand wires of dimension 2 (rate 1; all flattening ranks allow it:
  I checked the cuts {v₁}, {u₁}, {v₁,u₁}); if infeasible, supply dimension 4 against demand dimension 3 (rate
  0.79 > 3/4), also in border form. Any exact solution with rate > 3/4 is an explicit tensor code beating
  routing on five parties, a publishable small fact; rate 1 would mean the cut bound is attained.
  Link to ports: **"tensor coding attains the cut bound on every instance" ⇔ every spectral metric is
  ℓ₁-embeddable ⇒ (ρ_μ is not ℓ₁-embeddable for large μ, by Cheeger on the rank-one Cayley graph) contracting ⇒
  ports ⇒ fast 3-SAT.** So under Weak ETH some instance has tensor rate strictly below its cut bound; small
  instances will not show it (M5 and ρ₂ are ℓ₁), which is why this is evidence, not a decision procedure.

---

## Part 6. Recommendation

**Odds [C], characteristic 0.**

| Statement | My probability |
|---|---|
| No ports (so Weak ETH-consistent world) | 93% |
| Contracting hypothesis false over ℚ (all √rk metrics are prices) | 95% |
| The middle cell: contracting false but ports true | 3% |
| Contracting true (hence ports, hence 2^{v^{1−δ}} 3-SAT) | 2% |
| Ports in some positive characteristic | 10% (no hypothesis excludes it yet; see C1) |
| Theorem A (contracting ⇒ ports) is correct as written | 85% |
| The re-basing on Anthropic's J.4 alone goes through | 65% |
| We prove ports or no ports outright in the next weeks | < 2% each |

**What to do.**

1. **First experiment: 0a + 0b together** (one referee, one reader, about 3 hours each). They turn today's main
   finding into a short note with a title like *"Anthropic's contracting case contradicts Weak ETH"*:
   Theorem A, Theorem B with the finite objects (M5, 4×4 and 3×3 binary matrices under √rank), the side-by-side
   table, and the corollaries for both labs' permanent bounds. It uses Anthropic's Lean-backed F.6 and D.2, one
   elementary zig-zag theorem, and (for the 3-SAT conclusion) either OpenAI's Lean-backed IM 7.1 or, if 0b
   succeeds, Anthropic's J.4 alone. It is the result here that the user's reliability ordering favours.
2. **Then C1** (isolation in the power-saving regime): if it works, our conditional lower bounds extend to
   characteristic 2 under one hypothesis, and "ports anywhere ⇒ randomised 3-SAT speed-up" joins the note.
3. **Then D1** (engine gap theorem): the statement "beating the exponent 1/2 by this kind of algorithm already
   gives 2^{n^{1−δ}}" would be the most quotable consequence for the ETH line.
4. **In parallel, cheap numerics: E3** (K_{2,3}), then A1 (B.3 in buildings), then B2.
5. **Long shots to assign only if a strong reader is free: B1** (valued prices ⇒ building metrics) and **E2**
   (refute contracting unconditionally). Either would be a theorem about both papers at once.

**What not to do.** Do not run LPs/SDPs over CAT(0) conditions to "test" M5 or ρ₃ (§2.6: predetermined). Do not
try to prove ports through the Izeki–Nayatani invariant (§3.3: equivalent to contracting or stronger). Do not
present "finite test" without the caveat that only one side has finite certificates.

**Dependencies to flag in anything we publish.** Theorem A's conclusion "ports" uses OpenAI's HC Theorem 4.2
(elementary; Lean exists; we have not built it). "Ports ⇒ 3-SAT" is OpenAI's (Lean exists). "Flat is a theorem"
is OpenAI's EG 1.2. Everything about Anthropic's side (F.6, D.2, D.3, J.4, thm_cn) is from the paper the user
trusts more. The network-coding reformulation and the K_{2,3} bound use only Strassen's theorem and thm_cn.
