# The middle cell {not contracting, ports}: reformulation, a spectral threshold, and expanders that are not ports

Theory notes, 26 Nov 2026. Tags: [R] proved here (complete proof in these notes from cited statements);
[D] derived, unreviewed or resting on an uncertified step; [C] conjecture; [X] dead, with the reason;
[K] quoted, with pointer ([K*] = recalled from memory, not re-opened today); [N] computed.
"AN" = Anthropic's "VP ≠ VNP over every field" (`scratchpad/fm/paper.txt`); "OA" = OpenAI's unrefereed
24 Nov 2026 release (EG, HC as in `../ideas-ports.md`). Nothing here has been refereed.

Notation. All graphs are finite regular multigraphs (loops allowed), A = normalised adjacency matrix,
1 = λ₁ ≥ λ₂ ≥ … ≥ λ_n its eigenvalues, λ* = max(|λ₂|,|λ_n|). For a function w on pairs of vertices,
E_pairs w = n⁻² Σ_{u,v} w(u,v) (ordered pairs, u = v included; this is AN F.6's E_{g,a} and EG's V) and
E_edges w = n⁻¹ Σ_{u,v} A_uv w(u,v) (EG's E_G). The Poincaré constant of G against a class 𝒞 of functions on
V×V is β_𝒞(G) = sup_{w∈𝒞} E_pairs w / E_edges w; ports for a class of metrics means: one bounded-degree
family, of unbounded order, with β bounded for 𝒞 = {d² : d in the class}.
rk = rank over F₂. ρ_μ(a,b) = √rk(a−b) on Mat_μ(F₂). For f: V → Mat_μ(F₂) write D_f(u,v) = rk(f(u)−f(v)).
D_f is a metric on V (rank is subadditive); the price in question is √D_f.

---

## 0. Verdict

**The middle cell is not emptied, and the route "¬contracting ⇒ ρ_μ are prices ⇒ no graph family survives"
meets a precise obstruction: a spectral threshold at λ₂ = 2^{−r}.** What is established:

| # | Statement | Tag |
|---|---|---|
| 1 | **Direct implication (no D.2 needed).** If G has Poincaré constant γ against all AN prices over k and some f: V(G) → Mat_μ(F₂) has E_pairs D_f > γ·E_edges D_f, then Contracting(k) holds at this μ with s² = μ − (E_pairs D_f − γ E_edges D_f). Same statement inside the OA class. | [R] §2 |
| 2 | **Reformulation.** Let (GE) be: "some bounded-degree family of unbounded order has E_pairs D_f ≤ γ E_edges D_f for all f into all Mat_μ(F₂)". Then [¬contracting ∧ AN-ports] ⇒ (GE); so ¬(GE) ⇒ (AN-ports ⇔ contracting), and likewise (OA-ports ⇔ OA-contracting). (GE) is a statement about a convex cone of metrics, the **rank cone**, CUT_n ⊊ 𝒦_n^{rk} ⊊ MET_n (n large), with five equivalent descriptions (matrices, subspaces, lattices, linear colourings, commutator ranks for Cayley graphs). | [R] §1–§3 |
| 3 | **Kernel lemma and threshold.** 2^{−k·rk(a−b)} is positive semidefinite on Mat_μ(F₂) for every integer k ≥ 1. Hence E_edges 2^{−D_f} ≤ λ₂ + (1−λ₂) E_pairs 2^{−D_f} for every graph and every f. Consequences: (a) if all edges have D_f ≤ r and λ*(G) ≤ 2^{−r−1}, then E_pairs D_f ≤ 6r+4; (b) if E_edges D_f ≤ (1−λ₂)/4 then E_pairs D_f ≤ (4/3)(1−λ₂)⁻¹ E_edges D_f; (c) for mean edge rank e < log₂(1/λ₂) the ratio is bounded by a function of (λ₂, e). So a spreading placement of bounded gradient r **needs r ≥ log₂(1/λ₂)**. | [R] §4 |
| 4 | **Sharpness.** Cay(Mat_μ(F₂), rank ≤ r) has λ₂ ≈ 2^{−r} and the identity is r-Lipschitz with pair rank ≈ μ. So the threshold cannot be improved by any argument that only uses the kernel. More: for every graph, percolation kernels show that "quantised positive definiteness" can never bound placements with r ≳ 2 log₂ d. | [R]/[D] §4.4, §6.3 |
| 5 | **Explicit expanders that are not ports if contracting fails.** The 12-regular Cayley graphs of SL₃(F₂[x]/(p)), p irreducible of degree k, generators e_ij(1), e_ij(x) (property (T) quotients; n ≈ 2^{8k}) admit f with all edge ranks ≤ 1 (after the normalisation of §3) and E_pairs ≥ 3⌊k/2⌋ − 1 ≥ (3/16)log₂ n − 3: the largest possible order. So under ¬Contracting(k), **for any field k**, their AN-Poincaré constant is Θ(log n). The mechanism is the Lubotzky–Zelmanov failure of dimension expansion over finite fields. By-product: these graphs have λ₂ ≥ 3/4 − o(1). | [R] §5; numerics [N] |
| 6 | **Which way (GE) goes is open.** Evidence that (GE) is TRUE (random regular graphs, or cross-characteristic Cayley graphs, are "Grassmann expanders"): item 3, a dimension count, a small-set refinement, small searches. Evidence against: item 5, item 4, and the absence of any tool above the threshold. I put (GE) true at about 60%. If (GE) is true, the metrics ρ_μ (all that ¬contracting gives, see §2.3) cannot empty the middle cell. | [C] §6 |
| 7 | **Class bookkeeping.** Per class X ∈ {AN, OA}: X-contracting ⇒ X-ports, and ¬(GE) ⇒ (X-ports ⇒ X-contracting). The literal cell {¬AN-contracting, OA-ports} also contains the "class gap" {every ρ_μ is an AN price, some ρ_μ is not Strassen-spectral}, which no graph argument touches. | [R]/[D] §2.4 |

Consequences for the case table are in §8, computation specs in §9, dead ends in §7.

---

## 1. The rank cone and five descriptions of one question

### 1.1 Definitions

For n ≥ 1 let 𝒦_n^{rk} ⊂ ℝ^{n(n−1)/2} be the closure of { c·D_f : c ≥ 0, f: [n] → Mat_μ(F₂), μ ≥ 1 }.

**Lemma 1.1 [R].** 𝒦_n^{rk} is a closed convex cone, CUT_n ⊆ 𝒦_n^{rk} ⊆ MET_n, and for every graph G on n
vertices β_ρ(G) := sup_{f,μ} E_pairs D_f/E_edges D_f = max over δ ∈ 𝒦_n^{rk}∖0 of E_pairs δ/E_edges δ.
Proof. Block-diagonal sums: D_{f⊕g} = D_f + D_g, and c·D_f for rational c is D of a multiple direct sum up to
a common scale. So the set of rational multiples of rank metrics is closed under addition; its closure is a
convex cone. Diagonal 0/1 matrices give all cut metrics (f(v) = [v ∈ S]·E₁₁). Rank is subadditive, so every
D_f is a metric. The ratio is homogeneous of degree 0 and quasi-linear, so the sup over the cone is the sup
over rank metrics. ∎

So the mean-versus-sup distinction for edges disappears at the level of the cone, and (GE) reads:

> **(GE)** There are d, γ and d-regular graphs G_i, |V(G_i)| → ∞, with E_pairs δ ≤ γ·E_edges δ for all
> δ ∈ 𝒦^{rk}_{|V(G_i)|}.

For CUT in place of 𝒦^{rk} this holds for expanders (Cheeger); for MET it fails for every bounded-degree
family (δ = graph metric). (GE) asks on which side the rank cone falls.

### 1.2 Subspaces and lattices [R]

- **Grassmann form.** For m-dimensional subspaces U, V of F₂^{2m} put σ_m(U,V)² = dim(U+V) − m. Every finite
  subset of (Gr(m,2m), σ_m) is, up to one scale factor, a pull-back of some ρ_μ.
  Proof. Let U₁,…,U_n be given, q = 2^s > n. Over F_q the spaces U_i⊗F_q have a common complement C (choose
  basis vectors of C one at a time outside the union of the n proper subspaces U_i⊗F_q + C_partial: n·q^{2m−1}
  < q^{2m}). With A = U₁⊗F_q, every U_i⊗F_q is the graph of a linear map a_i: A → C, and
  dim_{F₂}(U_i+U_j) − m = dim_{F_q}(U_i⊗F_q + U_j⊗F_q) − m = rk_{F_q}(a_i − a_j). Finally
  Mat_m(F_q) ⊂ Mat_{ms}(F₂) with rk_{F₂} = s·rk_{F_q}. So σ_m² restricted to {U_i} is s⁻¹·D_f with
  f(i) = a_i ∈ Mat_{ms}(F₂). ∎ (On the big cell this is the remark of `../ideas-ports.md` §2.1; the point
  here is the whole Grassmannian.)
- **Lattice-of-subspaces form.** On all subspaces of F₂^N put τ(U,V)² = dim(U+V) − dim(U∩V) (the graph
  distance in the Hasse diagram). Then τ = σ_N ∘ (U ↦ U ⊕ U⁰), U⁰ ⊂ (F₂^N)* the annihilator:
  dim((U⊕U⁰)+(V⊕V⁰)) − N = dim(U+V) + (N − dim(U∩V)) − N.
- Consequently 𝒦^{rk} is also the closed cone generated by the metrics τ(W_u,W_v)² of subspace-valued maps
  v ↦ W_v, and by the metrics dim_{F₂}((L_u+L_v)/(L_u∩L_v)) of maps into commensurable lattices of F₂((t))^N
  (finitely many lattices lie between a common t^eL and L; reduce mod t^eL). The last is the ℓ₁ Weyl distance
  d₁ on vertices of the building of GL_N(F₂((t))); on the points L_a of c1 it is 2·rk.
- **(GE), Grassmann form:** ∃ bounded-degree family and γ with
  E_pairs [dim(W_u+W_v) − dim(W_u∩W_v)] ≤ γ·E_edges [same] for all maps v ↦ W_v ≤ F₂^N, all N.

### 1.3 Linear colourings, entropy, percolation [R]

For f: V → Mat_μ(F₂) and x ∈ F₂^μ let c_x(v) = f(v)x ∈ F₂^μ ("colouring of V") and g_x(v) = f(v)ᵀx. Then

    2^{−D_f(u,v)} = Pr_x[c_x(u) = c_x(v)] = Pr_x[g_x(u) = g_x(v)],     D_f(u,v) = H(c_X(u) − c_X(v))

(X uniform, H = entropy in bits). So a placement is a family of 2^μ colourings, **linear in x**, and D is the
−log₂ of the probability of being monochromatic. Two consequences:

- N_uv := ker(f(u)−f(v)) satisfies N_uv ⊇ N_uw ∩ N_wv: a placement is a "subspace-valued ultrametric", and
  D = codim. Boolean lattices in place of subspace lattices give exactly the cut cone.
- (percolation bound) Let G_x be the subgraph of the edges e = uv with (f(u)−f(v))ᵀx = 0. Edge e lies in G_x
  for a fraction 2^{−D_f(e)} of the x, g_x is constant on the components of G_x, hence
  **2^{−D_f(u,v)} ≥ Pr_x[u, v in one component of G_x]**. A placement of gradient ≤ r is a (dependent) bond
  percolation with edge marginals ≥ 2^{−r} whose connection probabilities bound 2^{−D} from below.

### 1.4 Coboundary form [R]

f ↔ the 1-coboundary C_e = f(u)−f(v) ∈ Mat_μ(F₂): a labelling of the edges by matrices of rank ≤ r whose sum
around every cycle is 0; equivalently a graph homomorphism of G into the (reflexive) Cayley graph
Cay(Mat_μ(F₂), {rank ≤ r}); equivalently a linear map from the cycle-free part F₂[V]₀ to Mat_μ sending every
edge vector e_u+e_v into the variety of rank ≤ r. Dimension count (heuristic, §6.1): nμ² unknown bits against
(dn/2)(μ−r)² bits of constraints.

### 1.5 Cayley graphs: commutator ranks [R]

Let G = Cay(Γ,S) (edges g ~ sg). For f: Γ → Mat_μ put F(g) = ⊕_{h∈Γ} f(gh) ∈ Mat_{μ|Γ|}. Then
D_F(g,g′) = Σ_h D_f(gh,g′h) is right-invariant, E_pairs and E_edges are multiplied by |Γ|, and
F(gk) = P_k⁻¹ F(g) P_k for a block permutation representation P of Γ. So with M = F(1): F(k) = P_k⁻¹MP_k,
D_F(sg,g) = rk[P_s,M] and D_F(g,g′) = rk[P_{g g′⁻¹},M]. Conversely, for any F₂Γ-module P and M ∈ End_{F₂}(P)
the placement g ↦ P_g⁻¹MP_g has exactly these edge and pair ranks. Hence

    β_ρ(Cay(Γ,S)) = sup over F₂Γ-modules P and M ∈ End_{F₂}(P) of  E_{g∈Γ} rk[P_g, M] / E_{s∈S} rk[P_s, M].

(GE) for a family of Cayley graphs is a **rank-metric Kazhdan property over F₂**: every operator that commutes
with the generators up to rank e is, on average over the group, within rank γe of commuting. (This is the same
symmetrisation as AN's "length functions from maps into price spaces", F.1.) L(g) = rk[P_g,M] is a length
function with 2^{−kL} positive definite on Γ for all integers k ≥ 1 (§4). The orbit maps g ↦ gW of §5 are the
subspace-valued version of the same thing (M = a projection onto W, up to a factor 2 in the ranks).

---

## 2. From a bad placement to the contracting inequality

### 2.1 Theorem M0 [R]

Let k be a field, μ ≥ 2, G a regular graph on V, and γ ≥ 0 such that E_pairs w² ≤ γ E_edges w² for every AN
price w on V over k. Let f: V → Mat_μ(F₂), e = E_edges D_f, P = E_pairs D_f. Then every AN price on
Mat_μ(F₂) over k satisfies

    D(μ)² ≤ (μ − (P − γe))·D(1)².

In particular, if P > γe, Contracting(k) holds (AN Def. D.1) with this μ and s² = max(1, μ − (P − γe)) < μ.

Proof. Let w be a price on Mat_μ(F₂). The group 𝔄 of the maps a ↦ αaα′ + b (α, α′ ∈ GL_μ(F₂), b ∈ Mat_μ) acts
transitively on the ordered pairs (a,a′) with rk(a−a′) = j, for each j. For σ ∈ 𝔄 the pull-back of w along
σ∘f is a price on V (AN A.4: pull-backs of prices are prices), so
E_pairs w(σf(u),σf(v))² ≤ γ E_edges w(σf(u),σf(v))². Average over σ ∈ 𝔄: a pair with D_f(u,v) = j contributes
D(j)² (the mean of w² over all pairs of difference rank j; AN D.1). With π_j, ε_j the distributions of D_f
on pairs and on edges:

    Σ_j π_j D(j)² ≤ γ Σ_j ε_j D(j)² ≤ γ Σ_j ε_j·j·D(1)² = γe·D(1)²

by D(j)² ≤ j·D(1)² (AN D.2 Step 1). The same Step 1 gives D(μ)² ≤ D(j)² + D(μ−j)² ≤ D(j)² + (μ−j)D(1)², also
for j = 0. So Σ_j π_j (D(μ)² − (μ−j)D(1)²) ≤ γe·D(1)², i.e. D(μ)² ≤ (γe + μ − P)·D(1)². ∎

Only AN A.4 (pull-backs), C.3/C.4(b) (through D.2 Step 1) are used. Neither Theorem D.2 nor
`thm_alt_rank_price` is needed, and the statement is quantitative.

**Corollary M0′ [R].** If AN-ports holds over k (some bounded-degree family, constant γ, against all AN
prices) and (GE) fails, then Contracting(k) holds. Conversely [R, via `thm_alt_rank_price`]: if
Contracting(k) fails, every graph has β_ρ(G) ≤ β_AN(G); in particular AN port graphs witness (GE).

### 2.2 Monotonicity in μ [R]

If D(μ)² ≤ (μ−η)D(1)² for all prices on Mat_μ, then D(μ′)² ≤ (μ′−η)D(1)² for all prices on Mat_{μ′}, μ′ ≥ μ.
Proof. For a price on Mat_{μ′}, D_{μ′}(μ)² is the mean over the embeddings a ↦ αaα′ + b of Mat_μ (α, α′ of
full rank μ) of D(μ)² of the pulled-back price, and likewise D_{μ′}(1)². So D_{μ′}(μ)² ≤ (μ−η)D_{μ′}(1)² and
D_{μ′}(μ′)² ≤ D_{μ′}(μ)² + D_{μ′}(μ′−μ)² ≤ (μ−η+μ′−μ)D_{μ′}(1)². ∎
(So "contracting at some μ" = "at all large μ", with the same additive gain η.)

### 2.3 What ¬contracting gives, exactly

[K-AN, `thm_alt_rank_price` + trivial converse] For each μ ≥ 3: Contracting fails at μ ⇔ ρ_μ is a price.
By 2.2: Contracting(k) fails ⇔ every ρ_μ is an AN price over k ⇔ 𝒫_ρ ⊂ {AN prices}, where 𝒫_ρ := {√δ :
δ ∈ 𝒦^{rk}} (pull-backs, scalings, limits; AN A.4). **This is the complete content of ¬contracting.** On top of
𝒫_ρ, AN C.3 puts every price into a price space (complete CAT(0), all of whose finite subsets are prices), so
hull points are forced where rigidity forces them (Lemma H: diamonds in tripod × ℝ; flat cubes; m-pods ×
segment). Trees × flats have Izeki–Nayatani invariant 0, so these particular hull pieces are harmless for
every expander; the non-commutative part of the danger is already in 𝒦^{rk}.

### 2.4 The two classes

OA spectral metrics ⊂ AN prices (`../review-theoremAB.md` §1). Define, for X ∈ {AN, OA}:
C_X ("X-contracting"): ∃ μ ≥ 2, s² < μ with D(μ) ≤ s·D(1) for all X-metrics on Mat_μ(F₂);
P_X ("X-ports"): a bounded-degree family with a uniform Poincaré constant against all X-metrics.
Then:

- C_AN ⇒ C_OA and P_AN ⇒ P_OA (fewer test metrics). [R]
- C_AN ⇒ P_AN. [D] Theorem A: AN F.6 is a statement about all AN prices; HC 4.2's proof runs in any class of
  Hadamard spaces, here AN's price spaces (complete CAT(0), AN §C.4). The referee checked the OA-class
  conclusion; the AN-class conclusion uses the same two steps.
- C_OA ⇒ P_OA. [D, OA] EG §11.1.2–11.1.3 use Lemma 11.3 only through its conclusion B_m ≤ (m−η)B₁ on
  Gr(m,2m), m a power of two. C_OA at μ gives it: by 2.2 take μ = m a power of two; a random GL_{2m}(F₂)
  translate of the big cell is a copy of Mat_m in which complementary (adjacent) pairs are uniform among all
  complementary (adjacent) pairs, so B_m = E_cells D^{cell}(m)² ≤ s² E_cells D^{cell}(1)² = s²B₁. (This is
  Prop. 11.2′ of `../ideas-ports.md` with the hypothesis stated as C_OA; the amplification steps are OA's,
  read by me, not refereed.)
- ¬(GE) ∧ P_X ⇒ C_X for both X. [R] Theorem M0; for X = OA the proof is identical (pull-backs of spectral
  wire metrics along maps of finite sets are spectral: EG §2.2, duplication and restriction; D.2 Step 1 is
  the quadrilateral inequality EG (4.5)).

So **if (GE) fails, P_AN ⇔ C_AN and P_OA ⇔ C_OA**, and the four statements collapse to C_AN ⇒ C_OA. The literal
middle cell {¬C_AN, P_OA} then equals {¬C_AN, C_OA} = "every ρ_μ is an AN price, but some ρ_μ is not a point
of Strassen's spectrum". Whether that gap can occur is a question about the two notions of spectral point
(AN: cover-subadditive; OA: additive), not about graphs. Known [R, `../hull/notes.md` §2]: the two classes
have the same closed convex hull in d-coordinates (Strassen duality), but Poincaré inequalities are linear
in d², so this does not close the gap.

If (GE) holds, nothing follows from ρ_μ: see §6 and §8.

---

## 3. Why genuinely non-commutative placements are needed, and what room there is

- [R] Diagonal placements give exactly CUT_n; every expander has β_CUT ≤ (1−λ₂)⁻¹ (co-area; §4.2 step 4).
- [R given K*] 𝒦_5^{rk} = MET_5: the 25 extreme rays of MET_5 are the 15 cuts and the 10 graph metrics of
  K_{2,3} ([K*] Deza–Laurent), and the latter is D on N5 ⊂ Mat₂(F₂) (`../hull/notes.md` §1.1). So on five
  points the rank cone is everything (consistent with Toyoda's five-point criterion used in the hull notes).
- [R] The graph metric of K_{3,3} is in 𝒦_6^{rk}: {0, I, ω} ∪ {e₁₁, e₂₁+e₂₂, e₁₂+e₂₂} ⊂ Mat₂(F₂) with
  ω = [[0,1],[1,1]] (0, I, ω, ω² = F₄). The graph metric of K_{q+1,q+1} is in the cone for q = 2^s: the two
  reguli of a hyperbolic quadric in PG(3,q) (lines of one family pairwise skew, each meets each line of the
  other) in the Grassmann graph of 2-planes of F_q⁴.
- [R] 𝒦_n^{rk} ≠ MET_n for large n: √δ embeds isometrically into a complete CAT(0) space for every δ in the
  cone (c1 §2 for ρ_μ; ℓ₂-sums, scalings and ultralimits preserve this). [K*] Eskenazis–Mendel–Naor,
  "Nonpositive curvature is not coarsely universal" (Invent. Math. 2019): Hadamard spaces have metric cotype
  2 with sharp scaling, so the grids ([m]ⁿ, ℓ_∞) do not embed coarsely-uniformly; a ½-snowflake is a coarse
  equivalence. Hence large ℓ_∞-grids are not in the rank cone. (This does not concern expanders: CAT(0) spaces
  can contain expanders, [K] Gromov, Kondo, Mendel–Naor.)
- [N] Small searches (annealing, `place.py`; values are lower bounds on β_ρ, pairs normalised as above):
  K_{3,3}: 7/6 against the cut value 1; Petersen 1.5 = cut; Heawood 1.75 against 1.714; Pappus 2.056 against
  2.0 (μ ≤ 3). The non-commutative gain on small cubic graphs is a few per cent.

---

## 4. The kernel lemma and the spectral threshold

### 4.1 Lemma K [R]

For every μ and every integer k ≥ 1 the kernel K_k(a,b) = 2^{−k·rk(a−b)} on Mat_μ(F₂) is positive
semidefinite. More generally, for random variables (Y_v) on one probability space, K(u,v) = Pr[Y_u = Y_v] is
positive semidefinite, and so is K(u,v) = Pr[u ↔ v] for any random graph on V.
Proof. 2^{−rk(a−b)} = |ker(a−b)|/2^μ = E_x 1[ax = bx] = E_x Σ_y 1[ax=y]·1[bx=y], an average of Gram
matrices. Powers: Schur products. The general statements have the same proof. ∎
(Equivalently |Γ_a ∩ Γ_b|/2^μ; on the lattice side, the correlation of the indicators 1_L, 1_{L′} in
L²(F₂((t))^N).) Only integer k occur: if 2^{−t·rk} were positive semidefinite for all t > 0, √rk would be
Hilbertian by Schoenberg, and it is not (M5, N5).

**Proposition S [R].** For every regular graph, every f: V → Mat_μ(F₂) and every integer k ≥ 1, with
λ = max(λ₂,0):

    E_edges 2^{−kD_f} ≤ λ + (1−λ)·E_pairs 2^{−kD_f}.

Proof. tr(AK) = Σ_i λ_i φ_iᵀKφ_i ≤ φ₁ᵀKφ₁ + λ Σ_{i≥2} φ_iᵀKφ_i = (1−λ)φ₁ᵀKφ₁ + λ·tr K, with φ₁ = n^{−1/2}·1 and
K_vv = 1. ∎

### 4.2 Consequences [R]

**(a) Bounded gradient.** Let D_f ≤ r on all edges (r ≥ 1) and λ* ≤ 2^{−r−1}. Then E_pairs D_f ≤ 6r + 4.
Proof. (1) p := E_pairs 2^{−D} ≥ 2^{−r} − λ₂ ≥ 2^{−r−1}. (2) Some u₀ has E_v 2^{−D(u₀,v)} ≥ p; with
S = {v : D(u₀,v) ≤ r+2}: p ≤ |S|/n + 2^{−r−3}, so |S| ≥ 3·2^{−r−3}n. (3) T := V∖(S ∪ N(S)) has no edge to S;
the expander mixing lemma gives |S||T| ≤ λ*²n², so |T|/n ≤ 2^{−2r−2}/(3·2^{−r−3}) ≤ 1/3. So
S′ := S ∪ N(S) has |S′| ≥ 2n/3 and lies within D ≤ 2r+2 of u₀. (4) g(v) := min_{w∈S′} D(v,w) is real valued
with |g(u)−g(v)| ≤ D(u,v). For real functions E_pairs|g(u)−g(v)| ≤ (1−λ₂)⁻¹E_edges|g(u)−g(v)| (co-area and
1_Sᵀ(I−A)1_S ≥ (1−λ₂)|S||Sᶜ|/n), so 2·(2/3)·E_v g ≤ r/(1−λ₂) ≤ 4r/3 and E_v g ≤ r.
(5) D(u,v) ≤ g(u)+g(v)+2(2r+2). ∎

**(b) Small mean energy.** If e := E_edges D_f ≤ (1−λ₂)/4, then E_pairs D_f ≤ (4/3)(1−λ₂)⁻¹·e.
Proof. 1 − 2^{−D} ≤ D/2 for integers D ≥ 0, and 1 − 2^{−D} ≥ ½·1[D ≥ 1]. Proposition S gives
Pr_pairs[f(u) ≠ f(v)] ≤ e/(1−λ₂) ≤ 1/4, so one fibre S of f has |S| ≥ 3n/4. With g = D(·, f(S)):
2·(3/4)·E g ≤ e/(1−λ₂) and D(u,v) ≤ g(u)+g(v). ∎

**(c) Any mean energy below the threshold.** If e < log₂(1/λ₂), then by Jensen E_edges 2^{−D} ≥ 2^{−e},
p ≥ c := (2^{−e}−λ₂)/(1−λ₂) > 0, a set of density ≥ c/2 lies within D ≤ ⌈log₂(1/c)⌉ of a point, and step (4)
gives E_pairs D_f ≤ 2e/(c(1−λ₂)) + 2⌈log₂(1/c)⌉. The constant degrades like 2^e inside the window; (a) shows
that for bounded gradient it does not.

**(d) Reading.** A d-regular graph with λ₂ = λ satisfies the full Poincaré inequality against the rank cone
for all placements of mean edge rank below log₂(1/λ) − ε. Since λ ≥ 2√(d−1)/d − o(1), the window is at most
e < ½log₂ d − 1 + o(1): **every violation of ports by a ρ-placement on a good expander has edge ranks of
order log d at least.** For Ramanujan graphs of degree p+1 ≥ 18 (LPS graphs from PGL₂(F_q)) there is no
1-Lipschitz spreading placement at all. For cubic graphs the window is empty.

**(e) Converse use.** Any placement gives an upper bound on the spectral gap:
λ₂ ≥ (E_edges 2^{−D_f} − E_pairs 2^{−D_f})/(1 − E_pairs 2^{−D_f}).

### 4.3 Small-set refinement [D]

Let Φ(δ) be the largest fraction of the edge-ends of a set of density ≤ δ that stay inside the set. For each
x the monochromatic edge fraction of c_x is ≤ Σ_i δ_iΦ(δ_i) over its colour classes, so

    E_edges 2^{−D_f} ≤ E_x Σ_i δ_i(x)·Φ(δ_i(x)).

With Φ(δ) ≤ δ + λ this is Proposition S (up to the factor 1−λ). For random d-regular graphs
Φ(δ) ≤ (2 + C log d/log(1/δ))/d for small δ (first moment: a subgraph of average degree 2+ε has a component
of density ≥ d^{−2/ε}; trees give Φ ≥ ≈ 2/d at every density, so this is the floor) [D, not written out]. So on random regular graphs a placement with gradient
r < log₂ d − 1 − ε still has a positive fraction (depending on d, ε) of pairs at bounded distance: the window
doubles, from ½log₂ d to log₂ d. Beyond r ≈ log₂ d the subgraphs G_x of §1.3 may be forests and nothing is
forced by this method.

### 4.4 Sharpness and a barrier

- [R] Cay(Mat_μ(F₂), rank one): the eigenvalue at the character of a matrix B of rank ρ is
  (2^{2μ−ρ} − 2^{μ+1} + 1)/(2^μ−1)², so λ₂ = ½ − O(2^{−μ}); the identity placement has E_edges 2^{−D} = ½
  and E_pairs D ≈ μ. Proposition S is tight up to O(2^{−μ}). [D] With generators of rank ≤ r: λ₂ ≈ 2^{−r},
  ratio ≈ μ/r.
- [R] A d-regular family with r-Lipschitz spreading placements has λ₂ ≥ 2^{−r} − o(1) (4.2(e)). Bounded
  number of generators that are identity + rank ≤ r can only generate a group living on dr coordinates, so
  the naive "transvection" Cayley graphs give bounded ratio; the examples of §5 use almost invariant
  subspaces instead.
- [R] **Barrier.** For any graph G and p < 1/(d−1), K_p(u,v) = Pr_p[u ↔ v] (Bernoulli bond percolation) is
  positive semidefinite together with all its integer powers, has K_p = 1 on the diagonal, and
  p^{d_G(u,v)} ≤ K_p(u,v) ≤ 2((d−1)p)^{d_G(u,v)}/(1−(d−1)p) (count self-avoiding paths). So L = −log₂K_p is,
  for p ≤ (d−1)^{−2}, within a factor 2 (and an additive constant) of log₂(1/p)·d_G. Hence the class of functions L with all 2^{−kL} positive semidefinite contains a
  bi-Lipschitz copy of every graph metric at scale r ≈ 2log₂ d: **no argument that uses only Lemma K can
  prove (GE)**; linearity over F₂ in x (§1.3) must enter. Conversely, a "linear percolation" (a placement whose
  G_x behave like independent subcritical percolation) would put the graph metric itself into the rank cone
  and refute (GE) for that graph. I could not construct one outside Cayley graphs of linear groups.

---

## 5. Expanders that are not ports if contracting fails

### 5.1 Almost invariant subspaces [R]

Let G = Cay(Γ,S) with edges g ~ gs, π: Γ → GL_N(F₂) and W ≤ F₂^N. For v(g) = π(g)W:
τ(v(gs),v(g))² = τ(π(s)W,W)² and τ(v(g),v(h))² = τ(W,π(g⁻¹h)W)². So

    β_ρ(Cay(Γ,S)) ≥ E_{g∈Γ} τ(W,π(g)W)² / E_{s∈S} τ(W,π(s)W)².

A subspace moved little by the generators and far by typical elements is a failure of dimension expansion
in the sense of [K] Lubotzky–Zelmanov, "Dimension expanders" (J. Algebra 2008; arXiv:0804.0481), whose
Example 4.I is the subspace used below (powers of x in a finite field, dim(W+xW) ≤ dim W + 1) and whose
Example 4.IV states that F_p[SL_d(F_p[x])] does not have property τ (verified today from the arXiv text).

### 5.2 Theorem M2 [R]

Let p ∈ F₂[x] be irreducible of degree k ≥ 2, F_q = F₂[x]/(p), Γ_p = SL₃(F_q),
S = {e_ab(1), e_ab(x) : a ≠ b} (12 involutions). Let U ⊂ F_q be the F₂-span of 1, x, …, x^{j−1}, j = ⌊k/2⌋,
and W = U³ ⊂ F_q³ = F₂^{3k}. Then for v(g) = gW, with d_J = dim W − dim(W∩·) = τ²/2:

1. d_J(sW,W) = 0 for s = e_ab(1) and ≤ 1 for s = e_ab(x). So E_edges d_J ≤ ½.
2. E_g d_J(gW,W) ≥ 3j − 1.
3. The graphs Cay(Γ_p,S) are an expander family (as deg p → ∞).

Hence β_ρ(Cay(Γ_p,S)) ≥ 6j − 2 ≥ 3k − 5 ≥ (3/8)log₂|Γ_p| − 5.

Proof. 1. e_ab(1) preserves U³. e_ab(x)W ∩ W ⊇ {u ∈ U³ : u_b ∈ U ∩ x⁻¹U}, and U ∩ x⁻¹U ⊇ span(1,…,x^{j−2})
has codimension ≤ 1 in U (j ≤ k−1, no reduction mod p occurs). 2. Γ_p is transitive on F_q³∖0, so for
w ≠ 0 the vector gw is uniform on F_q³∖0 and E_g|gW ∩ W| = 1 + (|W|−1)²/(q³−1) < 1 + 2^{6j−3k} ≤ 2. By
Jensen E_g dim(gW∩W) ≤ 1. 3. [K] SL₃(F₂[x]) is generated by e_ab(1), e_ab(x)
(e_ab(x^{i+1}) = [e_ac(x^i), e_cb(x)]; F₂[x] is Euclidean) and has property (T) (a lattice in
SL₃(F₂((1/x))); Kazhdan); it maps onto SL₃(F₂[x]/(p)) with S ↦ S; Margulis. ∎

**Corollary M2′ [R given `thm_alt_rank_price`].** Let k be any field for which Contracting(k) fails. Then the
AN-Poincaré constant of Cay(Γ_p,S) over k is ≥ (3/8)log₂ n − 5; these expanders are not AN ports, and no
family containing infinitely many of them is. (τ² is a scaled pull-back of ρ, §1.2; pull-backs and multiples
of prices are prices.) The order log n is the largest possible for a metric δ = d² (path bound).
For OA-ports the same holds if ρ_μ is Strassen-spectral (i.e. if C_OA fails).

**Corollary M2″ [R].** λ₂(Cay(Γ_p,S)) ≥ 3/4 − 2^{1−3j}. Proof: 4.2(e) with E_edges 2^{−d_J} ≥ ½·1 + ½·½ = 3/4
and E_pairs 2^{−d_J} = E_g|gW∩W|/|W| < 2^{1−3j}. (2^{−d_J} is the kernel of Lemma K for the pulled-back
placement over F_q-extension, or directly |gW∩hW|/|W| = ⟨1_{gW},1_{hW}⟩/|W|.) [D] The same for SL_n, n ≥ 2,
and any generating set of elementary matrices with coefficients in a fixed finite set of polynomials (with U
adapted).

[N] SL₂(F_{2^k}) with S = {e₁₂(1), e₂₁(1), e₁₂(x), e₂₁(x)}, W = U², exact enumeration (`sl2.py`):

| k | n | E_edges d_J | E_pairs d_J | ratio | bound on λ₂ from 4.2(e) | λ₂ computed |
|---|---|---|---|---|---|---|
| 2 | 60 | 0.5 | 1.500 | 3.0 | 0.583 | 0.731 |
| 3 | 504 | 0.5 | 1.869 | 3.7 | 0.650 | 0.938 |
| 4 | 4080 | 0.5 | 3.313 | 6.6 | 0.717 | 0.965 |
| 5 | 32736 | 0.5 | 3.809 | 7.6 | 0.729 | 0.975 |
| 6 | 262080 | 0.5 | 5.270 | 10.5 | 0.742 | 0.976 |

(E_pairs ≥ 2⌊k/2⌋ − 1 as in the theorem, with 2 in place of 3.)

### 5.3 Remarks

1. These are the standard "super-expanders": quotients of a lattice in SL₃ over a local field ([K*] Lafforgue:
   strong Banach property (T) for SL₃ of a non-archimedean local field, giving expanders with respect to
   uniformly convex Banach spaces for cocompact lattices; I did not check the non-uniform lattice
   SL₃(F₂[x])). They are **maximally bad** against the Bruhat–Tits buildings of GL_N(F₂((t))), N → ∞: the
   lattice acts on the F₂-vector space F₂[x]³, i.e. on the unit-scale Grassmannians. This answers one of the
   lead's literature questions: Lafforgue-type expanders in characteristic 2 do not give expanders against
   buildings of all ranks; property (T) says nothing about isometric actions on CAT(0) spaces of unbounded
   rank, and the group Γ = SL₃(F₂[x]) has an unbounded-orbit isometric action on the (CAT(0)-embedded
   snowflake of the) commensurability class of U³.
2. The construction needs a module over F₂ (the field that indexes the matrices in AN D.1 and in EG §11), not
   over the coefficient field k. For Cayley graphs of SL₃(F_ℓ[x]/(p)), ℓ odd, the same argument defeats the
   rank metrics over F_ℓ, which are not known to be prices under ¬contracting [C: an F_ℓ-analogue of AN D.2,
   "contracting_ℓ"; cf. `../ideas-ports.md` Ad.1 item 3].
3. Other families of the same kind [D]: any Γ ≤ GL_m(R), R a finite quotient of F₂[x₁,…,x_t], generators with
   entries in a fixed finite-dimensional space of polynomials; AN's own U_h(F₂) with f = identity
   (E_edges D = 1, E_pairs D ≈ h, so β_ρ ≥ ch, matching the form C₀(h−1) of F.6; here λ₂ → 1).
4. Dense or unbounded-degree versions: random Cayley graphs Cay(Mat_μ(F₂), Cμ² random rank-one matrices) are
   expanders of degree O(log n) with λ₂ ≈ ½ and ratio μ = √log₂ n.
5. [C] A random d-regular spanning subgraph of Cay(Mat_μ(F₂), rank ≤ r) should have
   λ₂ ≈ max(2^{−r}, 2√(d−1)/d); for 2^{−r} ≪ 2/√d this would be a bounded-degree near-Ramanujan family with
   r-Lipschitz placements of spread μ/r → ∞, i.e. with λ₂ < ½ and still not a port family. Not proved.

---

## 6. Is (GE) true? Evidence, heuristics, and what a proof must do

### 6.1 For (GE)

1. Theorem 4.2: the Poincaré inequality holds for all placements of energy below log₂(1/λ₂), and below
   ≈ log₂ d on random regular graphs [D].
2. **Dimension count [heuristic].** A placement into Mat_μ with all edges of rank ≤ r has nμ² free bits and
   (dn/2)(μ−r)² bits of constraints. "Generic" solutions exist only for r ≥ (1−√(2/d))μ, i.e. ratio
   ≤ (1−√(2/d))⁻¹ = 1 + O(d^{−1/2}) (compare the Hilbert value (1−λ)⁻¹ = 1 + O(d^{−1/2}) and the Boolean ball
   value 1 + 2/d). The count is scale free (the same in the Grassmann form, where the locus
   dim(U∩V) ≥ m−r has codimension (m−r)(N−m−r)). All spreading placements found so far are special
   solutions of an over-determined system, tied to an F₂-linear structure of the graph (Cayley graphs of
   linear groups over F₂[x], spanning subgraphs of Cay(Mat_μ, ·)). A random regular graph, or a Cayley graph
   of PSL₂(F_q), q odd, has no such structure in sight.
3. First moment [D, sketch]: for the union of d random perfect matchings and a fixed f, Brégman gives
   Pr[f is r-Lipschitz] ≤ ∏_v (e·deg_f(v)/n)^{d/2}, deg_f(v) = #{u : D_f(u,v) ≤ r}. A union bound over the
   2^{nμ²} maps shows that w.h.p. every r-Lipschitz f has geometric-mean r-ball density ≥ 2^{−2μ²/d−3}. With a
   random compression a ↦ PaQ (which preserves all ranks ≤ 6r when μ′ = 6r + 3log₂ n) this proves bounded
   ratio for **dense** random graphs (d = n^ε) and r ≤ c·n^{ε/2}, and nothing for bounded d: there are more
   configurations than graphs once μ² ≫ d log n. A proof of (GE) needs a multi-scale (chaining) version.
4. [N] The small searches of §3.

### 6.2 Against (GE)

1. §5: the best understood expanders fail, at the lowest possible energy and with the worst possible ratio.
2. §4.4: above r ≈ log₂ d no known inequality constrains placements, and the percolation kernels show that
   the available positivity is compatible with full graph metrics.
3. Mendel–Naor's template cuts both ways: [K, verified today from arXiv:1306.5434] Theorem 1.1: there are a
   Hadamard space X and 3-regular graphs G_n with sup_n γ(G_n,d_X²) < ∞ while random d-regular graphs have
   γ(H,d_X²) ≥ c(log_d n)² a.a.s.; Theorem 1.2: there are 3-regular graphs that are expanders with respect to
   (random regular graph, d_H²) a.a.s. Their X is the Euclidean cone over a class of graphs with
   diam ≤ K·girth; random graphs fail against the cone over themselves. So "is an expander" in the classical
   sense neither implies nor excludes (GE)-type statements; the target decides. Their positive result uses
   the zigzag iteration with a base graph, which is exactly HC 4.2.

### 6.3 What a proof of either side must do

- **To prove (GE)** (hence: ρ_μ alone cannot empty the middle cell): by HC 4.2 applied to the class of
  buildings B_N of GL_N(F₂((t))), all N (complete CAT(0); the proof of HC 4.2 uses only barycentres inside
  one space), it would suffice to find ONE graph, of any degree, with Poincaré constant against all B_N
  below c·log n/log(d+1) [D]. Rational points of B_N are vertices of the building over F₂((t^{1/e})), which
  is isomorphic to B_N, so only vertex placements matter; but the CAT(0) metric on vertices is
  (Σa_i²)^{1/2} in the elementary divisors a_i, while the kernel lemma sees d₁ = Σ|a_i|. The two agree
  (d₂² = d₁) exactly on the ρ-type configurations, inside one link. A proof must combine the kernel at unit
  scale with a tree/flat (Izeki–Nayatani δ = 0) argument across scales. Candidate base graph: a random graph
  of degree n^ε, ε tiny, where 6.1.3 already gives the bounded-gradient case up to r ≈ n^{ε/2}.
- **To refute (GE)** (hence: AN-ports ⇔ contracting): for every bounded-degree G produce a low-rank
  Mat_μ-valued coboundary with spread (§1.4). By §4.2 its edge ranks must be ≥ log₂(1/λ₂(G)), and by the
  dimension count it must be a special solution. The natural universal object is the Schreier presentation
  G = Sch(F_d, V): for an F_d-module M over F₂ and an almost invariant W ≤ M, the images of gW in the
  coinvariants M_H = M/⟨(h−1)M : h ∈ H⟩ (H = vertex stabiliser) are well defined on V and
  τ(q(A),q(B))² ≤ τ(A,B)² for a linear map q [R]; but M_H is typically 0 unless H is a congruence subgroup of
  the linear group through which M is defined, which brings back Cayley graphs.
- **Barrier (§4.4):** positivity of 2^{−kD} alone cannot decide; linearity in x must be used.

### 6.4 The literature questions of the brief, answered as far as I can

| Source | What it gives here |
|---|---|
| Mendel–Naor, Duke 2015 [K, checked] | One Hadamard space, one 3-regular family that expands against it, random graphs do not. Template for "middle cell consistent"; no statement about buildings. |
| Gromov / Kondo cones [K*] | Large-girth graphs fail against their own cones. The cone over a port graph is not known to be a price, and is not in 𝒫_ρ in any way I can see. No universal obstruction for the rank cone. |
| Lafforgue, strong (T) [K*] | Banach targets. For building targets of unbounded rank the SL₃(F₂[x]) quotients are counterexamples (§5). So strong (T) does not give Q-build. |
| Izeki–Nayatani, Toyoda [K, `../ideas-ports.md`] | δ(B_N) < 1 for each N, → 1 as N → ∞. Consistent with §4: the constant against B_N must degrade for graphs with λ₂ ≥ ½, and need not for λ₂ < ½ at unit scale. |
| Lubotzky–Zelmanov 2008 [K, checked] | The source of §5: over finite fields (T) does not give dimension expansion (their Ex. 4.I, 4.IV). Dimension expanders over finite fields exist ([K*] Bourgain–Yehudayoff; Dvir–Shpilka; Forbes–Guruswami), but (GE) asks for much more: no almost-intertwiners in **every** F₂-module (§1.5). |
| Eskenazis–Mendel–Naor 2019 [K*] | Rank cone ≠ metric cone (ℓ_∞ grids excluded). Not about expanders. |
| [K*] Arzhantseva–Păunescu; Elek–Grabowski (rank-metric stability of almost commuting matrices) | The right neighbourhood for §1.5: (GE) for Cayley graphs is a uniform rank-metric stability statement for almost-intertwiners. I know no result for expander families. |

---

## 7. Dead ends [X]

1. [X] "Every expander is fine against ρ because of some Izeki–Nayatani-type bound": false, §5 (and
   `../ideas-ports.md` §3.3 for dense graphs).
2. [X] "No bounded-degree graph survives ρ, by a soft/spectral argument": false as an argument; §4.2 proves
   the Poincaré inequality in a window of energies for every graph with λ₂ < 1, and the window grows with
   the degree.
3. [X] Transvection Cayley graphs (generators = identity + rank ≤ r): d generators act on ≤ dr coordinates,
   ratio ≤ d. Equivalently the dimension count.
4. [X] Products and inverses of Lipschitz maps (rk(xy−x′y′) ≤ rk(x−x′)+rk(y−y′), rk(x⁻¹−y⁻¹) = rk(x−y)):
   the bound holds for all pairs, so a product of Boolean maps is dominated by an ℓ₁ metric and cannot
   spread on an expander; gains need cancellation, i.e. conjugation f(v) = g_v⁻¹Mg_v, which is §1.5.
5. [X] Krylov / ball / path-sum constructions W_v = span{Aᵏe_v}, F₂^{B(v,T)}, Σ_{paths} ∏M: no reason for
   neighbours to be close; the Boolean ball has ratio (1−2/d)⁻¹.
6. [X] Truncated tree metrics r·min(d_G,T) on high-girth graphs: realisable on the tree (generic involutions
   of defect r in dimension rT), not on the quotient: the cycle condition is the over-determined system of
   §1.4. Also excluded by §4.3 for r < log₂ d − 1.
7. [X] Linear spreads at a vertex (the d edge-kernels partition F₂^μ∖0): forces μ = 2r, ratio 2.
8. [X] Reading EG Lemma 11.3 backwards ("ports ⇒ Grassmannian inequality"): it works exactly when a port
   graph has a spreading placement (Theorem M0); without one the port inequality says nothing about
   Mat_μ(F₂). The converse-type statement is equivalent to ¬(GE), not a consequence of the proof.
9. [X] Rescaling a high-energy placement to unit energy: there is no map of Mat_μ that divides ranks; the
   positive semidefinite functions of the rank are (up to small corrections) polynomials in 2^{−rk} with
   nonnegative coefficients (bilinear forms scheme), which separate ranks r and R only by ≤ 2^{−r}.
10. [X] Coinvariants of F₂[x]^m under a non-congruence finite-index subgroup of a free group: see §6.3.

---

## 8. Consequences for the case table

1. {contracting, no ports}: impossible (Theorem A), for AN and for OA separately (§2.4).
2. Middle cell, AN form {¬C_AN, P_AN}: **nonempty only if (GE) holds, and then the port graphs are
   Grassmann expanders**: they satisfy the L¹-type Poincaré inequality against all rank metrics
   over F₂ (and against √D for every subspace-valued or lattice-valued map). In particular [R]:
   - no port family contains infinitely many Cayley graphs of SL_m(F₂[x]/(p)) with elementary generators, nor
     infinitely many bounded-degree spanning subgraphs of Cay(Mat_μ(F₂), rank ≤ r) with r = o(μ), nor the
     graphs U_h (unless contracting holds);
   - a port family in which r-Lipschitz ρ-placements spread must have λ₂ ≥ 2^{−r}; conversely graphs with
     small λ₂ are protected at low energy. This is a testable constraint on OA's port graphs: in the
     ¬contracting world the family cannot be "F₂-linear".
3. Middle cell, literal form {¬C_AN, P_OA} = {¬C_AN, P_AN} ∪ (class-gap worlds with P_OA). If (GE) fails it
   equals the class gap {all ρ_μ AN prices, some ρ_μ not Strassen-spectral} (§2.4).
4. Prior. Nothing here moves the 3% prior on the middle cell being the true state of the world in
   characteristic 0 (that is a statement about ports, which Weak ETH excludes). What changes is the
   provability picture: "ports ⇒ contracting" is equivalent, given what ¬contracting provides, to ¬(GE), a
   clean problem in finite linear algebra, and I now think ¬(GE) is more likely false than true. If (GE) is
   true, a proof of "ports ⇒ contracting" must use tensors beyond the wire metrics ρ_μ.
5. Unconditional by-products: Lemma K / Proposition S / Theorem 4.2 (expanders versus rank metrics);
   Theorem M2 ((T)-expanders with Poincaré constant Θ(log n) against rank metrics, and λ₂ ≥ 3/4); the
   rank cone and 𝒦_5^{rk} = MET_5; Theorem M0 as a quantitative replacement of the D.2 route.

---

## 9. Computations worth running (specs)

All use only √rank on Mat_μ(F₂) and exact F₂ linear algebra (tools/tensorlab has both).

**E-M1 (growth of β_ρ on bounded-degree expanders; the most informative).**
Input: a d-regular graph G (adjacency list), integers μ, r_max. Objective: maximise
β(f) = (n⁻² Σ_{u,v} rk(f(u)−f(v))) / ((dn)⁻¹ Σ_{u~v} rk(f(u)−f(v))) over f: V → Mat_μ(F₂).
Search: parallel tempering over single-vertex moves f(v) ← f(v) + (random matrix of rank ≤ 2), f(v) ← f(w) +
(rank ≤ 1) for a neighbour w, and block moves (add one rank-one matrix to all f(v), v ∈ S, S a ball or one
side of a sparse cut); restarts from (i) the best cut, (ii) the Boolean ball placement, (iii) random.
Report β and the histogram of edge ranks and pair ranks; also β_cut = max over cuts (spectral partition +
local search for n > 24).
Instances: (a) cubic: Petersen, Heawood, Pappus, McGee, Tutte–Coxeter, random cubic n = 20, 30, 40, 60;
(b) 4- and 6-regular random graphs n = 16…64; (c) LPS X^{5,13} (n = 1092 or 2184), X^{5,17}; (d) Cayley
graphs of SL₂(F₈) (504), SL₂(F₁₆) (4080), SL₃(F₄) (60480) with elementary generators (known answer from §5:
check that the search finds ratio ≥ 2⌊k/2⌋−1 resp. 3⌊k/2⌋−1); (e) the same groups with generators not of
elementary type (e.g. PSL₂(F₇) ≅ SL₃(F₂), 168 elements, with two random generators). μ ∈ {2,…,6}, and μ up to
8 for (d).
Decision value: β_ρ/β_cut bounded and close to 1 on (a)–(c), (e) while ≫ 1 on (d) supports (GE). A
family in (a)–(c) with β_ρ/β_cut growing with n would be the first sign that (GE) fails.

**E-M2 (rank cone on six and seven points).** Enumerate the extreme rays of MET_6 (296 rays, 7 orbits) and
MET_7 (55 226 rays, 46 orbits) [K*: Grishukhin; Deza–Laurent]. For each orbit representative δ (integer
valued, primitive) decide whether c·δ = D_f for some c ∈ {1,2,3,4} and f: [n] → Mat_μ(F₂), μ ≤ 2c+2: exact
search (SAT or DFS with rank pruning; fix f(1) = 0, f(2) in normal form). Output: the list of rays in
𝒦^{rk}, and for the others the best approximation ratio. Decision value: describes how far the rank cone is
from the metric cone at small n; any ray provably outside (needs a valid inequality, e.g. from CAT(0)
5-point conditions applied to √δ, [K] Toyoda) gives the first explicit facet.

**E-M3 (threshold check).** For random d-regular graphs, d ∈ {8, 16, 32, 64}, n ≈ 200–2000, and μ ≤ 6:
maximise E_pairs D subject to max edge rank ≤ r for r = 1, 2, 3. Prediction from §4.2/§4.3: bounded
(≤ 6r+4, in fact ≈ r + O(1)) whenever 2^r < d/2; look at r just above log₂ d on d = 8 (r = 3, 4).

**E-M4 (eigenvalue by-product).** λ₂ of Cay(SL₃(F₂[x]/(p)), S) for deg p = 2, 3 (n = 60 480 and
16 482 816; the second by Lanczos on the Schreier graphs of the irreducible constituents) against the bound
3/4 − O(2^{−k}) of M2″.

Scripts used for the [N] items: `middle/sl2.py`, `middle/place.py` (plain Python, no dependencies beyond
numpy/scipy for the eigenvalues).

---

## 10. Next steps, in order

1. Referee §2 (Theorem M0, §2.2, §2.4) and §4 (Lemma K, Proposition S, 4.2(a),(b)), §5.2. These are short and
   are the parts to rely on.
2. Decide (GE). Two concrete sub-problems:
   (i) [C] **Random regular graphs are Grassmann expanders**: bounded-gradient form first (multi-scale first
   moment, §6.1.3), for d large.
   (ii) [C] **Cross-characteristic rank stability**: for Γ_q = PSL₂(F_q), q odd, with LPS generators, every
   F₂Γ_q-module and every M: E_g rk[g,M] ≤ γ·E_s rk[s,M] (§1.5). The representation theory is semisimple-like
   only when 2 ∤ |Γ|; a cleaner test family is the p-groups Γ(p)/Γ(pᵏ) ≤ SL₃(ℤ/pᵏ), p odd (expanders by (T);
   all F₂-modules semisimple and monomial).
3. Run E-M1 (a)–(e), then E-M3.
4. If (GE) is proved for the building class (§6.3), state the "model middle cell": a class of Hadamard
   spaces containing all ρ_μ, flats and trees, closed under every operation known to preserve prices, which
   has ports. That would show that the two labs' hypotheses cannot be unified by metric geometry of wire
   prices alone.
5. If instead a universal spreading placement is found, Corollary M0′ gives AN-ports ⇔ contracting at once,
   and §2.4 gives the OA statement.
