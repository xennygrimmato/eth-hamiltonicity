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

