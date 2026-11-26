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
   for all μ, the class of spectral spaces has Izeki–Nayatani invariant tending to 1 (I get δ ≥ 1 − 8/μ), and it
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

Proof of (i): ρ_μ not a price ⇒ ρ_{μ′} not a price for all μ′ ≥ μ ⇒ contracting fails to fail at μ′ ≥ 3, i.e.
by D.2/D.3 contracting holds ⇒ Theorem A. (ii): M5 ⊂ Mat₂(F₂) with the restricted metric (x5 [N]: checked exactly),
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
