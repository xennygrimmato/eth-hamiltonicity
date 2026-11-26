# q2-notes: does OpenAI's balanced-cut argument (HC Part I) transfer to the clique wire tensor?

Working notes, 26 Nov 2026. Nothing here is committed, machine-checked or refereed by a second reader.

Tags: **[K]** quoted, with location; **[R]** proved here in full; **[D]** derived here, unreviewed (or resting on an
unrefereed input, named); **[N]** numerical (script named); **[C]** conjecture or open; **[X]** dead, with reason.

Sources (paths relative to the session scratchpad): HC = `survey/oa/preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-…/paper.txt`
("l. n" = line of that file); IM, EG = the integer-multiplication and Euclidean-geometry preprints of the same release;
AN-ETH = `pb/aneth/paper.txt`; AN-VP = `fm/paper.txt`. **Every statement taken from HC, IM, EG, AN-ETH, AN-VP is
machine-generated and unrefereed; each use below is marked.** Notation of `prior-barriers.md` §5.3 and `notes.md` §1:
T_K(λ) = ⊗_{u<v} ⟨2^λ⟩_{uv} is the wire tensor of the K-clique with λ bits per edge, viewed on K rows of side
2^{λ(K−1)}; f_{K,λ} = f_{T_K(λ)} is the clique-sum polynomial (AN-VP's f_{k,ℓ}; the value of AN-ETH's (K, λ)-clique as a
polynomial in the tables); S = λK(K−1)/2.

Scripts: `q2/check_lemmaN.py`, `q2/check_star_restriction.py`, `q2/check_star_restriction_dense.py`,
`q2/check_euclid_ends.py`.

---

## 0. Verdict

**Q2 as literally posed (the metric lemma of `prior-barriers.md` §5.3): NO, for a three-line reason that holds in
every metric space (Lemma N, §2). Pricing T_K itself with one site per row can never work.**

**The theorem Q2 was meant to deliver: YES, conditionally on HC Thm 3.1 as printed (Theorem T, §3.3).** The transfer
does not go through a price of T_K. It goes through a restriction: T_K(λ) restricts, by linear maps on the rows, to
h = K·⌊⌊λ/2⌋/log₂q₀⌋ grouped copies of HC's own tensor T_d (d = K), at the cost of a factor 2(K−1)/K in bits per row
(Lemma S, "time-shared stars"). HC's proof of its Thm 3.1 is stable under row-wise restriction, so:

> **Theorem T [D; conditional on HC Thm 3.1].** If the characteristic of F has no ports, then for every sufficiently
> large even K and every λ ≥ λ₀(K) = Θ(K (log K)^{3/2}), every arithmetic circuit over F for f_{K,λ} (also in HC's
> border, degree-component sense) has at least 2^{c_T·K²λ/√⌈log₂K⌉} gates, with an absolute c_T > 0.

In AN-ETH's terms (Def. 4): a pair (K, e) that is achievable by an algorithm which is an arithmetic circuit in the
table entries has e ≥ c_T/√log K. So **an oblivious algebraic clique-sum algorithm with exponent α > 1/2 (any number
of merges, nets, hyperedge pieces, non-product term sets, any recursion or none) forces ports, hence, in
characteristic 0, 3-SAT in 2^{O(v^{1−δ})} by IM Thm 7.1 [K], hence the failure of Weak ETH.** One circuit for one pair
(K, λ) in the regime is enough.

What this rests on and what it leaves out is in §6. Short version: (i) HC Thm 3.1 and IM Thm 7.1 are unrefereed, and
the d/√log d rate of HC is outside the scope of the lab's Lean (§1.6); (ii) the regime is long wires,
λ ≳ K (log K)^{3/2}, which is AN-ETH's regime but not every conceivable one; (iii) only arithmetic circuits are
covered; (iv) the implication is one-directional.

---

## 1. What HC Part I says (§§1–7 read line by line; §8 and §11 read for the statements used)

### 1.1 The model and Lemma 3.3

- [K, l. 49–58] "its degree-component border size L_F^{[D]}(f) is the least s such that f belongs to the Zariski
  closure, over F, of the degree-D components of outputs of circuits with at most s gates. Each gate performs one
  binary addition, subtraction or multiplication. Variables and scalar inputs are free, and intermediate polynomials
  may have arbitrary degree."
- [K, l. 499] "A bipartition of [d] is balanced if each side has at least d/3 rows."
- [K, Lemma 3.3, l. 511–515] "For d ≥ 4, the coefficients that use one variable in each of d rows of the output of a
  size-s circuit form a sum of at most 2^d tensors. Each summand has rank at most 2^{O(d)}(s + 1) on its own balanced
  cut, with at most one summand per cut. For degree-component border size s, the coefficient tensor lies in the
  closure of the set of these sums."
- Proof read (l. 516–532): keep the row-multidegree 1_I component at every gate (3^d overhead), expand into parse
  trees, follow the child with more rows, stop at the first gate with ≤ 2d/3 rows, group by stopping gate. This is the
  balanced-gate argument of depth reduction. [R-level: I checked it; it is standard.]
- **Answers to the brief.** Lemma 3.3 assumes nothing about the terms. Its only input is an arithmetic circuit
  (+, −, ×; arbitrary depth, reuse, non-multilinear intermediate results) of size s whose degree-d component is f.
  It is blind to merges, levels, hyperedges and to whether term sets are products. The cut of a term is **not** from
  a fixed family: it is whichever bipartition with both sides ≥ d/3 the circuit's gates produce, so a lower-bound
  argument must handle all ≤ 2^d balanced cuts at once. The terms are arbitrary tensors of rank ≤ 2^{O(d)}(s+1) on
  their cut.

### 1.2 The theorem

- [K, Thm 3.1, l. 475–483] "There are an absolute positive integer a and absolute constants c, C > 0 with the
  following property. For every sufficiently large even d, set m = ⌈log₂ d⌉ and w = ⌈a d m^{3/2}⌉. There is a tensor
  T_d with entries in {0, 1} on d rows of common side q₀, with w ≤ log q₀ ≤ Cw, such that over every field F whose
  characteristic has no ports, L_F^{[d]}(f_{T_d^{⊗h}}) ≥ exp(c h d w/√m) (h ≥ 1)."
  Here T^{⊗h} is the grouped power: [K, l. 471–473] "In T^{⊗h} each row index is a word of length h, so f_{T^{⊗h}}
  still has degree d and now has d q^h variables." q₀ = 2^{⌈C₀w⌉} [K, l. 2883].
- [K, Cor. 3.2] fixed large even d, n ≥ d·q₀(d): size n^{Ω(d/√log d)}.
- The explicit tensor (Thm 11.2, l. 2730–2885, read): a binary encoding of the coefficients of
  P(z) = ±∏_{e ≤ b} ∏_{i<j ∈ S_e} (z_j − z_i) (b = m³ copies of the maximal minors of an (n/2) × n Vandermonde matrix,
  n = dq slots, q = ⌈w/m²⌉ slots per row), with the row alphabet compressed to the letters of weight ≥ −Aw. Its only
  role: [K, l. 2738–2744] for unit sites x₁,…,x_d with barycenter at the tip of a Hadamard cone with homogeneous
  prices, "the tensor T admits a rowwise restriction to a tensor Û on the alphabet V satisfying
  dF(1) − Cd ≤ B_x(Û) ≤ dF(1)", with "cw ≤ F′(1) ≤ Cw", "The restriction may depend on the placement and its prices."
  So T_d is a universal container; the object that is priced is Û, a row-wise restriction chosen **after** the
  placement.

### 1.3 The proof of Thm 3.1 (l. 594–655), step by step

1. [K, l. 594–598] "Lemma 3.3 puts T^{⊗h} in the closure of sums over balanced cuts with rank at most 2^{O(d)}(s+1)
   per cut. Applying the local maps to obtain Û^{⊗h} preserves this conclusion. The maps are linear on coefficient
   arrays and can only decrease cut ranks. The same conclusion holds if one starts with a size-s border circuit for
   f_{Û^{⊗h}} over K. We bound s in either case."
   **This is the sentence the transfer uses: from here on the proof uses nothing about T^{⊗h} except that Û^{⊗h} is a
   row-wise linear image of a tensor with the Lemma 3.3 property.**
2. A rank-R term on cut ℓ is supplied from two suppliers y_b = τZ_{ℓ,b}: one wire of dimension R of length ≤ τ, and
   every row index sent from its supplier. Weighted price ≤ τ log(s+1) + O(τd) + h Σ_i F(r_i) (3.3).
3. With τ = η/(d√m): Σ_i F(r_i) ≤ dF(1) − c₁w/m, using (3.1) and (3.2).
4. Summing ≤ 2^d terms costs O(d√m) once (Lemma 2.2). The target has weighted price ≥ h(dF(1) − O(d)). Hence (3.4):
   τ log(s+1) + O(hd + d√m) ≥ c₁hw/m, and w = ⌈a d m^{3/2}⌉ absorbs the errors for every h ≥ 1.

So the quantitative heart is two numbers per copy: saving c₁w/m (from the placement), deficit O(d) (from the target).

### 1.4 What "no ports" supplies

- Definition. [K, l. 346–351] "A class of metric spaces admits ports if regular multigraphs of a single positive
  degree and unbounded orders satisfy a uniform Poincaré inequality for squared distances in all its spaces […] The
  condition for X_χ is precisely port admission by χ [EG, Definition 11.1]." X_χ = the Hadamard spaces admitting
  spectral prices over a field of characteristic χ (l. 338).
- [K, Thm 4.2] no ports ⇒ Poincaré constant ≥ c·log n/log(d+1) on every d-regular n-vertex graph.
- [K, Thm 5.1, l. 970–977] "Let P, D be Markov kernels on a finite set with common stationary law π. Suppose that
  β ≥ 1 and that E_D(f) ≤ βE_P(f) for every placement f in a class of Hadamard spaces without ports. For any labeling
  L, let a be its entropy rate for the stationary P-walk and draw (X, Y) from the stationary D-step. Then
  H(L(Y) | X) ≤ Cβ(1 + a)." Read contrapositively: placements exist in which mean squared demand distance exceeds
  mean squared physical distance by the ratio of the information rates. This is the only way "no ports" enters
  §§6–7.
- [K, Thm 6.1] a no-ports class closed under rescaling, closed convex subspaces and pointed ultralimits contains a
  no-ports subclass M that is also closed under finite ℓ₂ products. M is a Zorn-minimal subclass (l. 1493–1500); it
  contains lines and Hilbert space (l. 360–365). Nothing else about its members is known. In particular X_χ itself is
  not shown to be closed under ℓ₂ products.
- [K, Thm 7.1, l. 1562–1572] "For every list of L balanced layouts on [n] there is a Hadamard metric cone in M, with
  unit points x₁,…,x_n of barycenter zero and two points Z_{ℓ,0}, Z_{ℓ,1} per layout, such that d(Z_{ℓ,0}, Z_{ℓ,1}) ≤ 1,
  ‖Z_{ℓ,v}‖ ≤ C√(m + log L), Σ_i ⟨x_i, Z_{ℓ,b_ℓ(i)}⟩ ≥ cn/√m for every layout." (m = log₂n; a layout is balanced if
  each value is taken on ≥ n/4 rows.)
- How the sites arise (l. 1584–1870): for a distribution on layouts, points z_{ℓ,0}, z_{ℓ,1} at distance ≤ 1 with
  diameter ≤ C√(m + log L); u_i = bar_ℓ z_{ℓ,b_ℓ(i)} (Cartan barycenter over layouts of the point that row i selects);
  [K, Lemma 7.2] (E d(u_i, u_{i′})²)^{1/2} ≥ c/√m; then x_i = log_p(u_i)/σ in the tangent cone at p = bar_i u_i,
  a minimax over distributions realised by an ℓ₂ product, and a product over the n cyclic shifts to make all norms 1.

### 1.5 The role of the lamp construction

Two uses. (a) In the proof of Thm 5.1 (l. 1010–1121) a "reservoir" of r copies of the state writes increments into m
"lamps"; refreshing all lamps is charged to O(mrβ) physical steps, Cor. 4.3 forces the net translation to carry
≈ mrh bits, and coding the physical trajectory bounds that by the entropy rate. This converts the Poincaré
obstruction for bounded-degree graphs into a statement about arbitrary pairs of walks. (b) In §7.2 the "lamp graph"
has states (lamp array g ∈ A^M, chart θ of layouts, report bits h) and reversible moves with costs (bounds on squared
lengths): flip one report bit, log(1/δ); add an arbitrary word to a lamp, S; add a word from the list determined by
typical reports, δS. Lemma 7.3 places it with all squared edge lengths ≤ cost and mean squared demand ≥ c₀MS. The
detour "install the increment's own reports batch by batch, make the now cheap increment, restore" (Fig. 4) must be as
long as the unprepared increment, c₁√S. Each batch replacement is bounded by J·√(r_a log(1/δ)) with J the best
barycentric separation, the P = O(m) batches add linearly, Σ_a √r_a ≤ Cm√r and S = rm, hence J ≥ c/√m.

So 1/√m = 1/√log₂n is "one bit out of the m bits of a row label, in a geometry where every balanced Boolean function
of the label is as good as a coordinate bit". For the m coordinate bits alone the Euclidean cube {±1}^m/√m gives the
same saving n/(2√m) [R, one line]; for a general list of L layouts a Euclidean placement gets only O(√n) (HC l. 166).

### 1.6 What is and is not machine-checked on their side

[K, `survey/oa/lean/docs/379.md`] "The paper's stronger exp(c(log N)²/(log log N)²) lower bound for circuits
approximating only the degree-N coefficients of these polynomials remains unformalized." The Lean folder contains a
balanced-cut circuit lemma and a unit-cube (Euclidean) saving (`BalancedWireLayout.lean`,
`BalancedLayoutThreshold.lean`, `BalancedPowerObstruction.lean`; headers read, nothing built). I found no
formalisation of Thm 7.1 or of the d/√log d rate. So **HC Thm 3.1 is a printed, unformalised, unrefereed claim.**

### 1.7 What the lamp sites' pairwise distances look like

The paper controls unit norms, barycenter 0, the savings and ‖Z‖. For the pairwise distances of the rows it gives no
statement. What follows from its own data:

- [R] Unit points with barycenter at the tip of a Hadamard cone satisfy Σ_i ⟨v, x_i⟩ ≤ 0 for every v (l. 1833–1836),
  so Σ_{i≠j} ⟨x_i, x_j⟩ ≤ −n and the mean of d(x_i, x_j)² over ordered pairs i ≠ j is ≥ 2n/(n−1). With d ≤ 2 the mean
  distance is > 1. So the rows are "at least Euclidean" (RMS ≥ √2) and at most pod-like (2). Nothing more.
- The sites are functions of the layout-bit vector (b_ℓ(i))_ℓ only. Two rows with the same bits get the same site.
- The spaces are produced by ultralimits, a Zorn-minimal class and a minimax; they are not described. Whether they
  are Euclidean-like, tree-like or expander-like between rows cannot be read off. For Q2 it does not matter (Lemma N).

---

## 2. Check of `prior-barriers.md` §5.3

### 2.1 The two-line inequality: correct [R]

Setting: K sites at distance 1 from o, a cut into halves A, B, suppliers y₀, y₁, r_i = d(x_i, y_{b(i)}),
Σ r_i = K − σ. Same-side pairs: d(x_u, x_v) ≤ r_u + r_v, and Σ over same-side pairs of (r_u + r_v) = (K/2 − 1) Σ r_i.
Cross pairs: d ≤ 2, and there are K²/4 of them. So Σ_{u<v} d ≤ (K/2 − 1)(K − σ) + K²/2 = K(K−1) − (K/2 − 1)σ, and

    price(T_K) − cost(term) ≤ λ[K(K−1) − (K/2−1)σ] − λ(K−1)(K−σ) − d(y₀,y₁) log R = λ(K/2)σ − d(y₀,y₁) log R.

This is what §5.3 states. It is right. It is also far from sharp, because it bounds the cross pairs by 2.

### 2.2 The sharp statement

**Lemma N [R] (no hypothesis; any pseudometric space).** Let x₁,…,x_K be points of a pseudometric space, K even.
There is a partition [K] = A ⊔ B with |A| = |B| = K/2 such that for all points y₀, y₁

    (K − 1)·[ Σ_{i∈A} d(x_i, y₀) + Σ_{i∈B} d(x_i, y₁) ] ≥ Σ_{u<v} d(x_u, x_v).

*Proof.* For any such partition and any y₀, y₁, the triangle inequality on same-side pairs gives
Σ_{same} d(x_u,x_v) ≤ (K/2 − 1)[Σ_A d(x_i,y₀) + Σ_B d(x_i,y₁)]. For a uniformly random partition into halves a pair is
on the same side with probability (K/2 − 1)/(K − 1), so some partition has
Σ_{same} d ≥ ((K/2−1)/(K−1)) Σ_{u<v} d. Combine. ∎

Equality: a K-pod with unit legs and both suppliers at the centre (56 = 56 at K = 8).
[N] `q2/check_lemmaN.py`: 180 random finite metric spaces (graph, tree, ℓ₁, ℓ₂, ℓ_∞), K = 4, 6, 8, suppliers ranging
over all points: the minimum over trials of max_cut min_suppliers [(K−1)·star − Σ_pairs] is 0.0, never negative.

**Corollary N1 [R].** Place the K rows of T_K(λ) at one site each, in any spectral space. For the cut of Lemma N the
HC bound for a term of rank R ≥ 1, namely λ(K−1)Σ r_i + d(y₀,y₁) log R, is ≥ λ Σ_{u<v} d(x_u,x_v) = H(T_K; x) for every
choice of suppliers. The comparison yields nothing, not even R > 1. Ports play no role.

**Corollary N2 [R] (not an artefact of the star bound).** If (K/2 − 1) divides λ(K−1), put λ′ = λ(K−1)/(K/2−1) and
P_ℓ = T_A(λ′) ⊗ T_B(λ′) (two half-cliques with doubled wires). P_ℓ has the format of T_K(λ), rank one on the cut
(A, B), and price λ′ Σ_{same} d ≥ λ Σ_{u<v} d = H(T_K; x) for the cut of Lemma N. So in every spectral point some
rank-one term on a balanced cut is at least as expensive as T_K. No upper bound for low-rank terms, however clever,
can separate T_K from them with rows as sites. (Prices of independent wires add, HC l. 236–237.)

**Corollary N3 [R].** The missing lemma "Q2" of §5.3 asks for Σ_{u<v}(2 − d(x_u,x_v)) ≤ (1−δ)(K−1)·min_ℓ σ_ℓ with
δ > 0. With unit sites, Lemma N reads K(K−1) − D ≤ (K−1)(K − σ_ℓ) for its cut, i.e. D ≥ (K−1)σ_ℓ ≥ (K−1) min_ℓ σ_ℓ,
where D = Σ(2 − d). So the requested inequality fails in every metric space unless min_ℓ σ_ℓ ≤ 0. **Q2 as posed: no.**

### 2.3 The angle count: arithmetic right, verdict wrong

§5.3's count: all pairs at angle ≥ π − ε′ with ε′² ≲ 8ηc/(K log K); then the saving is at most ‖Z‖(1 + Kε′/2), "the
same order as required", "first-order counting neither proves nor excludes the placement".

- The orders are computed correctly [R]: with ‖Z‖ ≤ C√(K + log K), ‖Z‖·Kε′/2 ≍ K/√log K.
- Done with constants it is not borderline [D for this second-order computation; the rigorous statement is
  Lemma N]. In a cone, r_i = 1 − τ⟨x_i,Z⟩ + (τ²/2)(‖Z‖² − ⟨x_i,Z⟩²) + O(τ³). Two same-side sites at angle ≥ π − ε′
  have ⟨x_i,Z⟩ + ⟨x_j,Z⟩ ≤ ε′‖Z‖, and nearly all sites are nearly orthogonal to Z, so the saving of a balanced cut is
  σ(τ) ≲ (K/2)(tε′ − t²), t = τ‖Z‖, with maximum (K/2)·ε′²/4. Multiplied by (K − 1) this is K(K−1)ε′²/8. The
  deficit of T_K at angles π − ε′ is D = Σ_{u<v}(2 − 2cos(ε′/2)) ≈ K(K−1)ε′²/8. **Best saving = deficit**: the
  quadratic term that §5.3 left to "constants" cancels the gain exactly. That is the equality case of Lemma N.
- Correction to the last bullet of §5.3's list: HC Thm 7.1 does give a lower bound on the pairwise distances, namely
  RMS ≥ √2 (§1.7). It is useless for the same reason.
- The closing [C] of §5.3 ("a space that is a pod to first order and has no-ports directions at second order is not
  obviously contradictory") is settled: it is contradictory, by Lemma N.

### 2.4 The "second, independent version" at the end of §5.3

§5.3 asks whether HC's T_d is a restriction of a complete-graph wire tensor on O(d) nodes with O(w) bits per node,
and says "The trivial representation uses (d−1)·w bits per node, which is useless." That count is for one copy hosted
by one star. For grouped powers the d star centres can be used in turn and the count is 2(d−1)/d times the bits of
the hosted power (Lemma S below). This is the route that works.

---

## 3. Does the argument transfer to T_K?

Three different things can be meant. The answers differ.

### 3.1 Pricing T_K with one site per row: dead [X, by Lemma N]

This is what §5.3 set up. It fails in every spectral space, with or without ports, for the reason of §2.2. A pod
factor does not help: in a product (pod leaf, lamp point) the pod part makes Lemma N an equality and the lamp part
makes it strict. The product-hull theorem (notes.md §4) is not needed to see this and cannot repair it.

On the hypothesis mismatch raised in the brief: "no ports ⇒ contracting fails" is Theorem A in contrapositive, so
under no ports pods and finite ℓ₂ products of pods and lines are prices (notes.md Thm 4.3) and lie in X_χ. That is
**not** enough to form "pod × lamp": HC's lamp cones live in the Zorn-minimal product-closed subclass M of X_χ, pods
are not known to belong to M, and X_χ is not known to be closed under ℓ₂ products (that is why HC needs Thm 6.1).
[D] Moot, by Lemma N.

### 3.2 Pricing T_K with one site per wire end: capped by HC's own barycentres; Euclidean value K^{3/2}; open in general

A cut of the rows induces a cut of the K(K−1) ends e = (u, v) ("the end at u of the wire to v"), with b(e) = b(u),
and the rank of a term is unchanged. This is what AN-VP does in the flat case (Props E.5, E.10: [K, l. 1940–1944,
2096–2098] "We put the end (a, b) at ½u_{ab}", u_{ab} = (e_a − e_b)/√2; "For a < b we put the end (a, b) at ½e_a and
the end (b, a) at −½e_a"). The bound obtained is log R ≥ λ·V_ℓ − (sharing), with

    V_ℓ = sup_{y₀≠y₁} [ Σ_{u<v} d(x_{(u,v)}, x_{(v,u)}) − Σ_e d(x_e, y_{b(e)}) ] / d(y₀, y₁).

- **E1 [R].** V_ℓ ≤ |A||B| (triangle inequality on each wire). Same-side wires contribute ≤ 0, cross wires at most
  d(y₀, y₁). A wire contributes fully iff its geodesic passes through y₀ and then y₁.
- **E2 [R] (Euclidean cap; AN-VP E.10 is optimal for its method up to the constant).** For every placement of ends
  and suppliers in a Hilbert space, min over exactly balanced cuts of V_ℓ ≤ (K/2)√(K−1).
  *Proof.* Let ν_{uv} be the unit vector from x_{(u,v)} to x_{(v,u)}, û_{uv} = ν_{uv} = −û_{vu}. As in notes.md
  Prop. 2.2, |x_e − x_ē| − |x_e − y| − |x_ē − y′| ≤ ⟨ν, y′ − y⟩. So the numerator is ≤ ⟨w_ℓ, y₁ − y₀⟩ with
  w_ℓ = Σ_{u∈A, v∈B} û_{uv} = ½ Σ_u s_u X_u, X_u = Σ_{v≠u} û_{uv}, s = ±1. For a uniform exactly balanced s,
  E[s_u s_{u′}] = −1/(K−1), and Σ_u X_u = 0, so E|w_ℓ|² = (K/(4(K−1))) Σ_u |X_u|² ≤ K²(K−1)/4. ∎
  The placement x_{(u,v)} = (e_u − e_v)/√2 has |w_ℓ| = K^{3/2}/(2√2) on every exactly balanced cut.
  [N] `q2/check_euclid_ends.py` (exhaustive over cuts, K = 6, 8; formula for E|w|² confirmed to 6 digits).
  This answers, for Euclidean placements, AN-VP's remark [K, l. 3462–3466] "We do not know whether the bound in the
  flat case can be improved": not with ends in a Euclidean space; any improvement needs other prices.
- **E3 [R] (the cap in every Hadamard space is HC's barycentric separation).** Let q be a probability vector on a
  family of cuts, y_{ℓ,0}, y_{ℓ,1} any suppliers, N_ℓ = Σ_{u<v} d(x_{(u,v)}, x_{(v,u)}) − Σ_e d(x_e, y_{ℓ,b_ℓ(e)}) the numerator
  of V_ℓ at these suppliers, and β_u = bar(Σ_ℓ q_ℓ δ_{y_{ℓ,b_ℓ(u)}}) the Cartan barycentre of the suppliers that row u
  uses. Then for every placement of the ends in a Hadamard space

      Σ_ℓ q_ℓ N_ℓ ≤ Σ_{u<v} d(β_u, β_v).

  In particular, if d(y_{ℓ,0}, y_{ℓ,1}) = δ for all ℓ, then min_ℓ N_ℓ/δ ≤ Σ_{u<v} d(β_u, β_v)/δ.
  *Proof.* Jensen for barycentres (HC l. 1213–1215, "the distance between two barycenters is at most the mean
  distance under any coupling of the two laws", applied to δ_x and the law of the suppliers):
  Σ_ℓ q_ℓ d(x, y_{ℓ,b_ℓ(u)}) ≥ d(x, β_u). So for a wire with ends x, x̄ at rows u, v:
  Σ_ℓ q_ℓ[d(x,x̄) − d(x, y_{ℓ,b_ℓ(u)}) − d(x̄, y_{ℓ,b_ℓ(v)})] ≤ d(x,x̄) − d(x,β_u) − d(x̄,β_v) ≤ d(β_u,β_v). ∎
  The β_u are exactly the points u_i of HC Lemma 7.2. So a wire-end certificate of order K²/√log K exists only if
  HC's barycentres are separated by ≳ δ/√log K on average (which HC proves under no ports), and equality needs two
  more things: each wire's ends collinear with β_u, β_v, and the Jensen step tight, i.e. the distance (Busemann)
  function of each end affine on the suppliers of its row. In a Euclidean space Jensen is tight and the separation is
  small; in a tree the separation can be large and Jensen loses everything.
- **E4 [D].** One tree: if every same-side wire passes through its supplier for all character cuts of F₂^m, any three
  suppliers of independent cuts are on a line (m ≥ 4), the supplier hull is a path up to end effects, and the value is ½|σ̂(a)| for a score
  vector σ with |σ_v| ≤ K−1, so min_a ≤ K^{3/2}/2 by Parseval: no better than Euclidean. Tree products obey the
  one-tree reduction of notes.md Thm 5.1. I did not bound the one-tree ratio with penalties allowed.
- **E5 [D].** Pod × lamp for the ends: put the pod factor in to make partner ends antipodal, weight s on the lamp
  factor. To second order the value is s·(A₂ − n‖Z‖√κ̄)/d(Z₀,Z₁), A₂ the lamp saving, κ̄ the mean of
  cos²(½∠(x_e, x_ē)) in the lamp factor. So the pod factor changes nothing: the criterion "mean cosine between an end
  and its supplier > RMS cosine of half the partner angle" is a property of the lamp factor. With HC's numbers the
  partners must be antipodal in the lamp cone itself to within ε² ≲ 1/(K log K). Gluing an antipodal ray at the tip
  (a wedge) makes ⟨antipode, Z⟩ = −‖Z‖ and loses ‖Z‖ ≈ √K per end against a gain of 1/√log K. [X]
- **E6 [K + D].** In HC's construction the site of an end would depend on its layout bits only, i.e. on its row, and
  that is §3.1. A wire-end certificate needs sites that also depend on the partner (Euclidean: ξ_u − ξ_v), for which
  a Hadamard cone has no operation.
- **Open statement X′ [C].** In a no-ports class, are there K(K−1) unit points x_{(u,v)} in a cone, with x_{(u,v)} and
  x_{(v,u)} antipodal, and suppliers for every balanced row cut, with Σ_e ⟨x_e, Z_{b(e)}⟩ ≥ cK²/√log K · d(Z₀,Z₁)?
  By E3 this is "HC's barycentric separation with Jensen-tight transversals". I have no proof and no refutation.
  **It is not needed for the conclusion** (§3.3). It would matter only for a direct proof, or for the short-wire
  regime of §6.2.

### 3.3 Restriction to HC's own tensor: works

**Lemma S [R] (time-shared stars).** Let a ≥ 1, K ≥ 2, and for v ∈ [K] let Star_v(a) = ⊗_{u≠v} ⟨2^a⟩_{vu}. Then
(i) T_K(2a) = ⊗_v Star_v(a) (grouped by rows): each edge {u, v} gives a bits to the star of u and a bits to the star
of v. (ii) For every tensor A on K rows whose rows u ≠ v have side ≤ 2^a (row v arbitrary), A is a row-wise
restriction of Star_v(a): with M_v: |(j_u)_{u≠v}⟩ ↦ Σ_i A_{i,(j_u)} |i⟩ at row v and the identity (or a coordinate
projection) elsewhere, (M_v ⊗ id)(Star_v(a)) = Σ_j (Σ_i A_{i,j}|i⟩) ⊗_u |j_u⟩ = A. (iii) Hence, for tensors A^{(1)},…,A^{(K)}
as in (ii) (A^{(v)} with star centre v), T_K(2a) restricts row-wise to A^{(1)} ⊗ … ⊗ A^{(K)}; the local map at row u is
M_u on the own-star factor tensored with coordinate projections on the K−1 leaf factors. (iv) In particular, for any
K-row tensor T of common side q and any h₀ with q^{h₀} ≤ 2^a: **T_K(λ) ≥ T^{⊗K h₀} for all λ ≥ 2a.**

Bits per row: T_K(2a) has 2a(K−1), the hosted power K·h₀·log₂q ≤ Ka. Overhead 2(K−1)/K < 2.
[N] `q2/check_star_restriction_dense.py` (K = 3, a = 1: explicit 16×16×16 array, explicit M_u, contraction equals
A₀ ⊗ A₁ ⊗ A₂ exactly; f_U(X) = f_T(MᵗX) at a random point); `q2/check_star_restriction.py` (entrywise identity for
K = 3, 4).

**Lemma L [R] (restriction and circuits).** If U = (⊗_u M_u) T, then f_U(X) = f_T(Y) with Y_{u,i} = Σ_j (M_u)_{j,i} X_{u,j}.
(a) L(f_U) ≤ L(f_T) + (gates computing the Y), also for degree-component border size, because the substitution is
homogeneous linear, commutes with taking the degree-d component, and is continuous on coefficients. (b) Without any
additive loss: the conclusion of Lemma 3.3 ("in the closure of sums over balanced cuts of terms of rank ≤ R") passes
from T to U, because ⊗M_u is linear and does not increase the rank on any row cut. This is HC's own sentence quoted
in §1.3 step 1.

**Theorem T [D; conditional on HC Thm 3.1 and, for form (b), on its proof as printed].** Let the characteristic of F
have no ports. Let d ≥ d₀ be even (HC's threshold), K = d, m = ⌈log₂K⌉, w = ⌈a_HC K m^{3/2}⌉, b₀ = ⌈log₂ q₀(K)⌉ = ⌈C₀w⌉,
λ₀(K) = 2b₀. For λ ≥ λ₀(K) put h₀ = ⌊⌊λ/2⌋/b₀⌋ ≥ 1 and h = K h₀. Then

    L_F^{[K]}(f_{K,λ}) ≥ exp(c·h·K·w/√m) − K·2^{λ(K−½)}     (form (a)),
    log(L_F^{[K]}(f_{K,λ}) + 1) ≥ c₂·h·K·w/√m                (form (b)),

and in both forms, for K large, log₂ L(f_{K,λ}) ≥ c_T K²λ/√⌈log₂K⌉ ≥ 2c_T·S/√⌈log₂K⌉, with
c_T = c/(12 C₀ ln 2)·(1 − o(1)) (c₂ in place of c for form (b)).

*Proof.* Lemma S(iv) with T = T_d, q = q₀, a = h₀b₀ ≤ ⌊λ/2⌋: T_K(λ) ≥ T_d^{⊗h} row-wise (first project T_K(λ) to
T_K(2a) by zeroing letters; this is a substitution of zeros). Form (a): Lemma L(a) and HC Thm 3.1. The Y of row v are
sums of at most q₀^{h₀} variables with coefficients in {0, 1}, and there are at most q₀^{2h₀(K−1)} nonzero ones per
row, so the extra gates number at most K·q₀^{h₀(2K−1)} ≤ K·2^{λ(K−½)}. Form (b): Lemma L(b), then the proof of HC
Thm 3.1 from its second sentence on, verbatim, with T_d^{⊗h} in place of "T^{⊗h}". Arithmetic: ⌊λ/2⌋ ≥ λ/3,
⌊x/b₀⌋ ≥ x/(2b₀) for x ≥ b₀, w/b₀ ≥ 1/(2C₀); so h K w/√m ≥ K²λ/(12 C₀√m). The subtracted term in (a) is negligible
once c_T K/√m > 1. ∎

Remarks.
1. **The regime.** λ ≥ λ₀(K) = Θ(K (log K)^{3/2}). It cannot be lowered much by this method: HC's target needs
   savings c₁w/m per copy to beat a deficit of O(1) per row, so w ≳ K log K, and one copy is not a product of
   smaller tensors, so a star must carry a whole row of it on each edge. See §6.2 for short wires.
2. **Odd K** follows from even K − 1 by projection (set the table of one node to the indicator of the zero strings),
   at the cost of HC's degree-isolation factor O(K²) in the border model. [D]
3. **Uniformity.** The bound holds for every h ≥ 1 with explicit dependence on h; there is no "liminf in λ without a
   rate" as in notes.md §6. The gap the referee found in Theorem S does not arise here.
4. **A variant with hubs [D].** Substituting constants for the tables of K − d′ rows turns each of them into a free
   hub: T_K(λ) with those rows contracted against arbitrary tensors is T_{d′}(λ) ⊗ (K − d′ arbitrary d′-row tensors
   with λ bits per row). So for d′ even ≥ d₀, λ ≥ b₀(d′): log L(f_{K,λ}) ≥ c(K − d′)⌊λ/b₀(d′)⌋ d′ w′/√m′ − O(log K).
   With d′ = K/2 this is Theorem T with threshold b₀(K/2) and constant 1/16 in place of 1/12. With d′ ≈ λ/(log λ)^{3/2}
   it gives, for short wires, log₂L ≳ c Kλ²/(log λ)², i.e. e ≳ c λ/(K (log λ)²).

**Corollary T1 [D] (AN-ETH's normalisation).** [K, AN-ETH Def. 4, l. 819–823] "(K, e) is achievable if there are an
algorithm and a constant C, both depending only on K and e, such that for all integers λ, B ≥ 1 and all tables with
|W_w| < 2^B the algorithm, given λ, B and query access, outputs the value of the (K, λ)-clique within
C·2^{eK²λ}(B + λ)^C operations." If the algorithm is a straight-line program in the table entries that computes
f_{K,λ} as a polynomial over a field of characteristic χ without ports, then e ≥ c_T/√⌈log₂K⌉ for all large K.
(Let λ → ∞ at fixed K.)

**Corollary T2 [D] (the chain; uses HC Thm 3.1, IM Thm 7.1 and through it HC Thm 13.1).** Suppose that for one
sufficiently large even K and one λ ≥ λ₀(K) there is an arithmetic circuit over a field of characteristic 0 for
f_{K,λ} with fewer than 2^{c_T K²λ/√⌈log₂K⌉} gates. Then characteristic 0 admits ports, and by [K, IM Thm 7.1, l. 1686–1689]
"for some δ > 0 a deterministic algorithm decides 3-SAT on v variables in 2^{O(v^{1−δ})} bit operations times a
polynomial in the input length", so Weak ETH fails. In particular every oblivious algebraic clique-sum algorithm over
ℤ or ℚ with e(K) ≤ (log K)^{−α}, α > 1/2, for infinitely many K, refutes Weak ETH. Under Weak ETH the exponent 1/2 of
AN-ETH is optimal in this class. In characteristic p the same with "randomised" (ports/c1d1 C1-OA) and rWETH.

**Corollary T3 [D] (HC Cor. 3.2 is tight, given AN-ETH).** For d in AN-ETH's sequence K_ℓ and any d-row tensor T of
side q, Lemma S and AN-ETH Thm A(b) with Thm B [K, l. 1596–1597, "outputs the value of the (K_ℓ, λ)-clique within
2^{e_ℓ K_ℓ² λ}(K_ℓ(λ + B))^{C₀K_ℓ²} operations", e_ℓ ≤ 0.85((3x₀+6)/log K_ℓ)^{1/2}] give circuits of size n^{O(d/√log d)}
for the grouped powers T^{⊗dh₀} (n the number of variables, h₀ large; over ℚ, or any field in which the integer d of
AN-ETH Def. 7(a) and 2 are invertible). So grouped powers of every tensor are this easy, and HC's n^{Ω(d/√log d)} cannot be improved in the exponent, even under no ports. The "same shape" observed in
`prior-barriers.md` §5.3 is the same quantity seen from the two sides.

**Corollary T4 [D] (the rate 1/√log d of the lamp certificate is forced; uses AN-ETH Thm A, B and HC Thms 8.1, 11.2).**
Suppose some Hadamard cone with homogeneous spectral prices over a field of characteristic 0 carried d unit sites of
barycenter 0 and, for every balanced cut, suppliers at distance ≤ 1 with ‖Z‖ = O(√d) and saving ≥ g·d. HC's comparison
(§1.3 with g in place of c₀/√m, τ ≈ ηg/d) would give log L(f_{T_d^{⊗h}}) ≳ c h d w g, and Corollary T3 gives
≤ C h d w/√log d for h a multiple of d, d = K_ℓ. So g ≤ C′/√log d: for the full list of balanced cuts the loss in HC's
§7.3 (batches adding linearly) is not an artefact. This is a statement about metric spaces obtained from an algorithm.

**A consistency check that could have failed [D].** Run the same route in a Euclidean placement (flats exist over
every field by EG Thm 1.2 [K]; simplex sites): the saving for a balanced cut is ≈ √d/2 per unit separation, the
quadratic error is O(wτ²d), τ ≈ 1/√d, and HC's comparison gives log s ≳ c h w √d for T_d^{⊗h}. Through Lemma S this is
log L(f_{K,λ}) ≳ c′ λ K^{3/2}: the order of AN-VP Prop. E.10 (λk^{3/2}/16), which is proved there by an independent
argument with wire ends as sites, and which E2 shows is the Euclidean optimum. So "rows as sites + near-star
restriction" and "ends as sites + wires" agree in the one case where both can be computed.

---

## 4. Comparison with what we know, in the engine's normalisation

Engine normalisation (notes.md §1.1): a level with p merges and node growth K′ = K^β has value ρ, and
e_{K′} = ρ·e_K, so e_K = (log K)^{−α′}, α′ = log_β(1/ρ*).

| statement | hypothesis | class | what it bounds | strength at one level, β = 2 |
|---|---|---|---|---|
| flat floor ρ ≥ 1/√p | flat (EG 1.2: unconditional) | fixed balanced configurations | level value | 1/√2 for p = 2; 0.577 for p = 3 |
| pod floor (notes.md §5) | contracting fails | 3-nets of F₂^M, F₄^M; per level | level value | 0.6124 |
| cap of Cor. 3.4 | none | anything proved by one price on a p-net level | what prices can show | ≤ 1/√2 |
| AN-VP E.10 | flat | all circuits for f_{K,λ} | e(K) ≥ 1/(8√K) | (global) |
| **Theorem T** | **no ports + HC 3.1** | **all circuits for f_{K,λ}, λ ≥ λ₀(K)** | **e(K) ≥ c/√log K** | **geometric mean of the level values ≥ 1/√2** |

**What Theorem T says per level.** For a tower with β = 2 and level values ρ_j, e(K_J) = e(K₀)·∏_{j≤J} ρ_j and
log K_J ≈ 2^J log K₀, so e(K_J) ≥ c/√log K_J for all J forces liminf (∏_{j≤J} ρ_j)^{1/J} ≥ 1/√2. In general
α′ ≤ 1/2 whatever β and p. So under no ports no tower of 3-nets (or of anything else) realised by arithmetic
circuits beats exponent 1/2; three merges buy at most a constant.

**It does not evade the per-level cap; it meets it, and it could not exceed it.** 1/√2 per level is exactly the cap
of Cor. 3.4 and exactly what the two-merge engine attains. AN-ETH's algorithm is an upper bound for every lower-bound
method, so no argument can give more than c/√log K globally.

**What HC uses that the per-level price method does not have.**
1. *A different target.* The per-level method prices the wire tensor of the level. With rows as sites that is dead
   (Lemma N); with ends as sites it is capped by E2/E3 and by Cor. 3.4. HC prices a row-wise restriction Û that is
   within O(1) per row of the star bound at the given placement (Thm 8.1/11.2, exterior tensors). Restricting lowers
   the price of the target a little and the price of the adversary's terms a lot: in T_K's own format the adversary
   has twice the row dimension the wires use (Cor. N2), in Û's format it has none to spare.
2. *A global decomposition.* Lemma 3.3 is applied to the whole circuit: one balanced bipartition per term of the
   fully unrolled computation, 2^K "merges" with two groups each, no levels. Nothing has to be composed over levels,
   which is where Theorem S has its uniformity gap.
3. *The no-ports geometry.* In a Euclidean placement the same route gives 1/√K (AN-VP E.10; E2). The whole gain from
   1/√K to 1/√log K is Thm 7.1: savings for all 2^K cuts as large as a Hamming cube gives for log K coordinate cuts.
   "Contracting fails" does not supply this (pods and their products are, for this problem, Euclidean up to
   constants as far as I can see, E4 [D]); "no ports" does, through Thm 5.1.

**Why this is not a contradiction with the cap.** The cap says: no single price on a net level certifies more than
1/√2. Theorem T certifies, for a different tensor and globally, a bound that equals 1/√2 per level in the mean. It
makes no per-level price statement. In particular it does not answer Q1 (is there a price with value E/√2 on
3-nets?). It makes Q1 unnecessary for the barrier: the attainment statement "no tower beats 1/2" holds under no
ports without any per-level certificate. Floor (what prices certify per level, between 0.6124 and 0.7071 for 3-nets
when contracting fails) and attainment (what circuits can do) are different things; notes.md §7 item 2 left open
whether they can differ, and this does not decide it either, since a single level with ρ < 1/√2 at one fixed order g,
followed by the two-merge engine, changes only the constant and is not excluded.

**Case table in characteristic 0 (all entries conditional on the cited unrefereed theorems).**

| | consequence for algebraic clique engines | consequence for 3-SAT |
|---|---|---|
| contracting (⇒ ports, Thm A) | not constrained by Theorem T | 2^{O(n^{1−δ})} (Thm R; IM 7.1) |
| not contracting, ports | not constrained by Theorem T | 2^{O(v^{1−δ})} (IM 7.1) |
| no ports (forced by Weak ETH) | e(K) ≥ c/√log K: exponent ≤ 1/2 | nothing new |

So in every case: an algebraic clique engine with α > 1/2 in characteristic 0 implies power-saving 3-SAT.

---

## 5. The engine side: what class is covered

- **What Lemma 3.3 needs: an arithmetic circuit for f_{K,λ}.** Not "terms low-rank on their own cuts"; that is its
  output. Engine terms being products of pieces over small configurations, costs being networks on groups, the
  recursion over levels: all of that is irrelevant once the algorithm is a sequence of ring operations on table
  entries that does not depend on their values.
- **AN-ETH's engine is of this kind [D, from reading the proof of Prop. 3, l. 991–1047, and Lemma 8].** It uses the
  identity 2^{t|R|}Z = Σ_ι Z_ι, chooses rows or columns per ι by comparing U_row and U_col (numbers that depend on ι,
  not on the tables), finds a grouping by a search over K^g groupings that depends on the c_{a,b} only, forms group
  tables as sums of products of table values, and recurses. Divisions are by fixed integers. So "(K, e) achievable
  by this algorithm" gives a circuit over ℚ, and over F_p for p not dividing the constants, of size at most the
  operation count.
- **The tensor is really T_K.** [K, AN-ETH Def. 3, l. 800–812] "the value is the sum, over all choices of one string
  in {0, 1}^λ per edge, of ∏_w W_w evaluated at the strings on the edges at w", with arbitrary tables W_w. As a
  polynomial in the table entries this is f_{T_K(λ)}. Non-uniform wire widths λ_{uv} restrict to the uniform clique
  with min λ_{uv}.
- **AN-ETH works in the regime.** [K, l. 1676–1680] in Thm A(c): "let K = K_ℓ […] for the largest ℓ with K_ℓ ≤ m^{1/9}",
  L = ⌈(U + 2ζgP)/K²⌉ ≈ 2km/K² ≥ m^{7/9} ≫ K (log K)^{3/2}. And Def. 4 demands all λ at fixed K.

**The class covered by Theorem T and Corollary T2:** every family of arithmetic circuits (straight-line programs
with +, −, ×, and, over infinite fields, ÷ after the standard elimination of divisions at polynomial cost in the
degree K [standard, not checked here]) that computes, or approximates in HC's border sense, the polynomial f_{K,λ}
for some pairs (K, λ) with K → ∞ and λ ≥ λ₀(K), over a field of a characteristic without ports. This contains:
tower engines with any number of merges per level, nets, hyperedge configurations, correlated (non-product) term
sets, growing lists of configurations, cut hierarchies that are not merges, and anything not organised in levels.

**Not covered.**
1. Algorithms that are not arithmetic circuits in the tables: branching on table values, hashing, lookups keyed by
   values, bit tricks on integers; instance-adaptive algorithms.
2. Algorithms that are correct only for structured tables (they compute a projection of f_{K,λ}, for which no lower
   bound is claimed).
3. The short-wire regime λ ≪ K (§6.2).
4. An algorithm that agrees with f only on a bounded grid of table values without being a polynomial identity. (A
   definitional point: the operation sequence must compute the polynomial. AN-ETH's does.)
5. 3-SAT algorithms that do not pass through clique sums at all, e.g. OA-ETH's interpolation; whether its tensor
   form yields circuits for f_{K,λ} I did not examine. [C]

---

## 6. Risks, limits, and what to do

### 6.1 What the conclusion rests on

| input | status | used for |
|---|---|---|
| Lemma S, Lemma L, Lemma N, E1–E3 | [R] here, short; S and N also [N] | everything in §§2–3 |
| HC Lemma 3.3 | [K]; proof checked here; a version is in their Lean scope | Theorem T |
| **HC Thm 3.1 (Thms 5.1, 6.1, 7.1, 8.1, 11.2)** | **[K], unrefereed, not formalised; I read §§4–7 and 11 but did not verify them** | Theorem T |
| IM Thm 7.1, HC Thm 13.1 | [K], unrefereed (our README: "Theorem A's 3-SAT conclusion depends on OpenAI's unreviewed chain") | Corollary T2 only |
| AN-ETH Thm A, B | [K], unrefereed | Corollary T3 and "the bound is attained" only |

If HC Thm 3.1 fails, Theorem T fails with it, and nothing in §3.3 survives except Lemma S and Corollary T3's upper
bound. Lemma N and the negative answer to the literal Q2 are unconditional.

### 6.2 The regime: short wires are not covered

Theorem T needs λ ≥ λ₀(K) ≈ 2C₀a_HC·K (log K)^{3/2}. For smaller λ the hub variant gives only
e ≳ c·λ/(K (log λ)²), a power loss. An algebraic algorithm that reaches 3-SAT through cliques with K ≈ n^{0.45} nodes
and wires of n^{0.1} bits would not be touched. I could not reduce short wires to long wires: grouping g nodes into a
supernode is not a substitution in f (the supernode table would have to be an arbitrary function of all strings
leaving the group, and a group of nodes with their own tables only produces tensor-network states with internal
bond (g−1)λ). AN-ETH's reduction and Def. 4 are in the long-wire regime, so every engine "in the sense of AN-ETH
Def. 4" is covered. A statement for all λ would need a near-star row-wise restriction of T_K(λ) with λ = polylog K,
or the wire-end certificate X′ of §3.2. [C]

### 6.3 One-directional

Ports are not shown to give an algebraic clique engine with small e(K): HC Thm 13.1 needs maximum degree ≤ s^{1/20}
and the nodes of a clique have degree λ(K−1). So the statement is "improvement ⇒ ports ⇒ Weak ETH fails", not an
equivalence. Under ports AN-VP E.10 (flat) still gives e(K) ≥ 1/(8√K).

### 6.4 What I would do

1. **Referee §3.3 (30 minutes).** Lemma S and Lemma L are elementary. The only judgement call is that HC's proof of
   Thm 3.1 uses T^{⊗h} only through the Lemma 3.3 property of Û^{⊗h} (form (b)); form (a) avoids even that and uses
   the statement of Thm 3.1 alone.
2. **The risk is HC Thm 3.1.** Cheapest tests of it, in order: (i) the Euclidean specialisation against AN-VP E.10
   (done above, consistent); (ii) Corollary T3 gives an unconditional-given-AN-ETH upper bound n^{O(d/√log d)} for
   grouped powers of **every** tensor, so any claimed lower bound for an explicit grouped power above that rate
   (in either lab's release or elsewhere) would contradict AN-ETH: scan for one; (iii) a line-by-line check of §7.3
   (the passage from Lemma 7.3 to J ≥ c/√m) and of Thm 8.1, which carry the two numbers of §1.3.
3. **Consequences for the project.** The attainment search in the window (1/2, 0.7075] for algebraic clique engines
   over ℤ or ℚ is, given HC 3.1 and IM 7.1, a search for a refutation of Weak ETH. Q1 is no longer needed for the
   barrier. What remains open on our side: the short-wire regime; non-algebraic algorithms; and whether the
   no-ports hypothesis can be replaced by "contracting fails" (it cannot by this route: the lamp certificate is the
   only source of the gain, and it needs Thm 5.1).

---

## 7. Dead ends and corrections

- [X] Pricing T_K with rows as sites, in any space, with any product or hull (Lemma N).
- [X] Wedge of cones at the tip to create antipodes for wire ends (E5): every supplier lives in one branch and loses
  ‖Z‖ on all ends outside it.
- [X] "Pod × lamp" as a way to get antipodal partners: the pod factor drops out of the second-order criterion (E5).
- Correction to `prior-barriers.md` §5.3: the inequality is right; the angle count's verdict is wrong (§2.3); the
  missing lemma as stated is false (Cor. N3); the dismissed last paragraph is the route that works (§2.4, Lemma S).
- Correction to `prior-barriers.md` §0 item 3 and §5.2: "The 'ports' lower bounds of OpenAI do not transfer" is true
  for FT, IM 8.1 and MM 4.1, and false for HC Thm 3.1, which transfers by restriction.
- Not done: I did not read HC §§9–10 (the proof of Thm 8.1) or §§12–19; I did not build or read in depth either lab's
  Lean; I did not examine OA-ETH's algorithm as a circuit for f_{K,λ}.
