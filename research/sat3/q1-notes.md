# Q1: the three-merge floor on nets equals the cap 1/√2 (nets of F_q^m)

Theory notes, 26 Nov 2026. Not committed, not machine-checked, not refereed. Written for a referee.

Tags: **[R]** proved here in full from the cited inputs; **[D]** derived here, proof written, unreviewed (or resting
on an unreviewed input, named); **[N]** numerical (script named); **[K]** quoted; **[C]** conjecture; **[X]** dead,
with reason.

Inputs. K-AN = Anthropic's paper (`scratchpad/fm/paper.txt`): Prop. C.3 (every price is pulled back from a price
space), Lemma C.4(a) (unique geodesics, CN), C.4(f) (flat rectangles), Thm D.2 with the Lean statement
`thm_alt_rank_price` (¬contracting ⇒ √rank on Mat_μ(F₂) is a price, every μ ≥ 3). Ours: `sat3/notes.md` §2 (price
method (★)), §3 (bimedian inequality, Cor. 3.4: every CAT(0) placement gives at most √(E·E_×/2) per merge on a p-net),
Lemma 4.1 (segment filling; refereed in `review-sat3.md`); `ports/middle/notes.md` §1.2 (subspace metrics are
pull-backs of rank metrics, [R] there); `ports/c1d1/notes.md` D1.1–D1.3 (engine class, gap theorem).
Standard facts used only for the unconditional statement: spherical buildings are CAT(1) and Euclidean cones over
CAT(1) spaces are CAT(0) (Bridson–Haefliger II.10A.4, II.3.14).

Script: `q1_verify.py` (exact distances in the filtration space, the placement for m = 2, 3, 4, random four-point
tests of the metric).

---

## 0. Results

1. **The space [R for the metric, K for CAT(0)].** For a finite field F_q let 𝒞_N(q) be the set of real filtrations of
   F_q^N with the metric "Euclidean distance of the level vectors in a basis adapted to both" (§1). It is
   Cone(spherical building of GL_N(F_q)) × ℝ, a CAT(0) space. Its 0/1 points are the subspaces, with
   d² = dim(U+U′) − dim(U∩U′).
2. **Theorem A (F_CAT) [D; arithmetic N].** Let q be any prime power, m ≥ 2, g = q^m, P ⊆ P¹(F_q) a set of p ≥ 2
   slopes, and 𝒩 = 𝒩(q,m,P) the p-net with nodes Mat_{m×2}(F_q) = (F_q^m)² and classes x ∈ P (lines {a : ax = y}).
   For q = 2 and p = 3 this is the 3-net of the group F₂^m (classes r, c, r+c). There is a placement of 𝒩 in
   𝒞_{m+2}(q) in which every generic edge (rank(a − a′) = 2) has saving s^k_e → δ_k/√2 **for all p merges at once**.
   Consequently
   - on every set of generic edges the placement value is exactly 1/√2 (a supremum, legs → ∞), which is the cap;
   - on the full level, min_k b_k/E ≥ (g−q)/(√2(g+1)) + 1/(g+1), against the cap √(g/(2(g+1))) of Cor. 3.4.
   So F_CAT(𝒩) = 1/√2 − Θ(1/g) for fixed q: the supremum over all CAT(0) placements of the p-net value is
   determined up to O(1/g), with no hypothesis.
3. **Theorem B (prices) [D].** If the contracting hypothesis fails over k, every finite subset of 𝒞_N(2^s) is a price
   over k, for all N and s (§3). Hence (Theorem C, §4) for the nets 𝒩(2^s, m, P) every piece family with 2^{o(λ)}
   terms has a piece with c_k ≥ (1/√2 − O(q/g) − ε)·E·λ for all merges k ∈ P at once. Together with Cor. 3.4:
   **when contracting fails, the price floor of these nets equals the cap; the window [0.6124, 0.7071) of
   `notes.md` closes for them**, for every number of merges p ≤ q+1.
4. **Fixed configuration, tower form [D].** The generic edges of 𝒩(q,m,P) are partitioned into copies of one fixed
   all-crossing configuration X_q (the generic edges of the order-q² net; for q = 2: X₄, 16 nodes, 48 edges, 12 hubs),
   with remainder ξ = (q+1)/(g+1). X_q has floor exactly E/√2 per merge when contracting fails (q = 2^s). So the net
   levels are (p, 2, {X_q})-levels in the sense of D1.1, the floor is uniform in g, and D1's gap theorem goes through
   with 1/√2 in place of 1/√p (Theorem D, §4.3). This repairs the gap the referee found in Theorem S for these nets.
5. **P1 (the hull) [D].** The closed convex hull of (Sub(F₂^N), τ) in any CAT(0) space is the cube complex
   K_N = union of the cubes [0,1]^N of all bases = the truncated cone over the spherical building. Every finite subset
   of it is a price when contracting fails ("hull conjecture" of the K_{2,m} notes: true for these vertex sets).
   Mat_μ(F₂) with √rank sits in K_{2μ} (graphs, scale 1/√2), inside the slice Σx_i = μ.
6. **Not covered.** Nets of cyclic groups (m = 1: the realisation is planar and any two node-lines meet), Δ₃ and K₄
   (both are m = 1), nets of Z₄^m and other non-elementary-abelian groups, p ≥ 4 nets whose slopes generate a field
   F_Q with [F_g : F_Q] bounded. For odd q the CAT(0) statement holds but the price statement is not known (the rank
   metric over F₃ is not known to be forced).
7. **Dead [X].** Cones over the incidence graph of the net (Φ = 9/4) or of PG(2,q) (Φ = 1): rank 2 is too small. Exact
   equality with all edge lines through one cone point (net triangles give closed local geodesics of length 3π/2).

Normalisation throughout: `notes.md` §2. A placement puts a point at every leg and every hub; L = Σ_e |e⁺e⁻|,
H_k = Σ_legs |ℓ, o^k(ℓ)|, δ_k = largest hub–hub distance in merge k, b_k = (L − H_k)/δ_k,
s^k_e = |e⁺e⁻| − |e⁺, o^k(e⁺)| − |e⁻, o^k(e⁻)|, value = min_k b_k/E. F_CAT = sup over CAT(0) spaces and placements.

---

## 1. The space of filtrations

Let V = F_q^N. A **filtration** is a family (F_s)_{s∈ℝ} of subspaces, decreasing in s, left-continuous, with F_s = V
for s ≪ 0 and F_s = 0 for s ≫ 0. Equivalently: a chain 0 ⊊ V₁ ⊊ … ⊊ V_k = V with levels s₁ > … > s_k
(F_s = V_j for s_{j+1} < s ≤ s_j). For a basis f = (f₁,…,f_N) and x ∈ ℝ^N put F^{f,x}_s = span{f_i : x_i ≥ s}. A
basis f is **adapted** to F if F = F^{f,x} for some x (then x is unique: x_i = max{s : f_i ∈ F_s}).

**Lemma 1.1 [R; standard].** (a) Any two filtrations have a common adapted basis. (b) If f is adapted to F and F′
with level vectors x, x′, the multiset {(x_i, x′_i)} does not depend on f: the number of i with x_i ≥ s and x′_i ≥ s′
is dim(F_s ∩ F′_{s′}).

*Proof.* (a) is the statement that two flags of V have a common adapted basis (Bruhat decomposition; elementary:
choose bases of the graded pieces (V_j ∩ V′_l)/((V_{j−1} ∩ V′_l) + (V_j ∩ V′_{l−1})) and lift). (b): F_s ∩ F′_{s′} is
spanned by the f_i it contains, because both are coordinate subspaces of f. ∎

**Definition.** d(F,F′) = |x − x′| (Euclidean norm) for any common adapted basis. By (b) it is well defined:
d² = Σ_{j,l} m(j,l)(s_j − s′_l)², m the second difference of dim(V_j ∩ V′_l). 𝒞_N(q) is the set of filtrations with d.
K_N(q) ⊂ 𝒞_N(q) is the set of filtrations with all levels in [0,1]. The **cube** of a basis f is {F^{f,x} : x ∈ [0,1]^N};
its vertices (x ∈ {0,1}^N) are the coordinate subspaces of f, a subspace U being the filtration "U at level 1, V at
level 0". For subspaces, d(U,U′)² = dim(U+U′) − dim(U∩U′) =: τ(U,U′)².

**Fact 1.2 [K, standard].** (𝒞_N(q), d) is isometric to Cone(Δ) × ℝ, Δ the spherical building of GL_N(F_q) (the flag
complex of V with its round metric; apartments = bases; the ℝ-factor is the mean level). Hence it is CAT(0)
(B–H II.10A.4 and II.3.14). The identification: in a basis f the points F^{f,x} form the apartment ℝ^N; two points of
Cone(Δ) × ℝ lie in a common apartment, in which the cone metric is the Euclidean one.

Fact 1.2 is used only for the unconditional statement (Theorem A as a statement about CAT(0) spaces). Theorem B does
not use it: there the CAT(0) space is the price space of K-AN C.3. [N] `q1_verify.py` tests d on random quadruples of
filtrations of F₂⁴ and F₂⁵: no violation of the triangle inequality or of the quadrilateral inequality C.4(b).

**Lemma 1.3 (symmetry) [R].** GL(V) acts on 𝒞_N by isometries (g·F)_s = g(F_s). If F is fixed by g then
d(F, U) = d(F, gU) for every subspace U. ∎

**Lemma 1.4 (far-leg formula for point hubs) [R].** Let f be a basis, d ∈ ℝ^N a unit vector, c ∈ ℝ^N, and
x_T = F^{f, c+Td}, y_T = F^{f, c−Td}. For a one-dimensional subspace h = ⟨Σ_{i∈A} α_i f_i⟩ (all α_i ≠ 0; A = supp_f h) and
the hub point "h at level 1":

    |x_T, h| = T + ⟨c,d⟩ − min_{i∈A} d_i + O(1/T),      |y_T, h| = T − ⟨c,d⟩ + max_{i∈A} d_i + O(1/T).

So for hubs h, h′ at the two ends of an edge with legs x_T, y_T:  s → min_{supp_f h} d_i − max_{supp_f h′} d_i.

*Proof.* For large T the basis f can be changed, without changing the filtration x_T, so as to contain a generator of
h: replace f_{i*} by Σ_A α_i f_i, where i* ∈ A minimises c_i + Td_i (the new vector lies in the same F_s as f_{i*} and
not in a smaller one). In the new basis h is the unit vector e_{i*}, so |x_T, h|² = |c+Td|² + 1 − 2(c_{i*}+Td_{i*}).
For y_T the index maximising d_i is used. ∎

---

## 2. Theorem A: the placement

### 2.1 The net as a geometry of planes

Fix q, m ≥ 2, g = q^m, and V = F_q² ⊕ F_q^m, N = m+2, M = 0 ⊕ F_q^m. Choose for every point of P¹(F_q) a
representative x ∈ F_q² (q+1 vectors, pairwise independent).

- **Node** a ∈ Mat_{m×2}(F_q) = Hom(F_q², F_q^m): the plane W_a = {(z, az) : z ∈ F_q²}. These are the g² planes
  complementary to M.
- **Hub** of class x and value y ∈ F_q^m: the point h^x_y = ⟨(x, y)⟩ of PG(V). For fixed x these are g distinct points.
  The hubs of all q+1 classes are the (q+1)g points of PG(V) outside M.
- The hub of node a in class x is h^x_{ax} ⊂ W_a. So W_a contains exactly the q+1 hubs of a, and a, a′ lie on a common
  line of class x iff (a − a′)x = 0 iff h^x_{ax} = h^x_{a′x}.
- W_a ∩ W_{a′} = {(z, az) : (a−a′)z = 0} ≅ ker(a − a′). Hence for a ≠ a′:
  **generic** (rank(a−a′) = 2): W_a ∩ W_{a′} = 0, the edge crosses all q+1 classes;
  **rank one**: W_a ∩ W_{a′} is one point ⟨(z₀, az₀)⟩, z₀ spanning the kernel; it is the common hub if [z₀] ∈ P
  (collinear nodes), and a non-hub point otherwise.

Counts. Each node has (g−1)(g−q) generic partners and (q+1)(g−1) rank-one partners (g−1 per slope);
(g−1)(g−q) + (q+1)(g−1) = g²−1. With E = g²(g²−1)/2 edges:

    E_gen = g²(g−1)(g−q)/2 = E·(g−q)/(g+1),   E_coll(P) = p·g²(g−1)/2 = E·p/(g+1),   E_other = E·(q+1−p)/(g+1).

For q = 2, p = 3: generic 48 of 120 (g = 4), 1344 of 2016 (g = 8), 26880 of 32640 (g = 16).
For m = 1 there are no generic edges (g = q): planes of a 3-space always meet. K₄ (q = 2) and the net containing Δ₃
(q = 3) are of this kind.

### 2.2 The placement

Hubs: the points h^x_y, as filtrations "h at level 1, V at level 0". Any two distinct points are part of a basis, so
all hubs are pairwise at distance √2: **δ_k = √2 for every merge.**

Generic edge e = (a, a′), W = W_a, W′ = W_{a′}. Choose R with V = W ⊕ R ⊕ W′ and T > 0. Legs:

    x_e = (W at level (1+T)/2,  W ⊕ R at level 0,  V at level −T/2),
    y_e = (W′ at level (1+T)/2,  W′ ⊕ R at level 0,  V at level −T/2).

(For m = 2, R = 0 and the middle level is absent.)

**Proposition 2.1 [R].** |x_e y_e| = 2T+1, and |x_e, h| = √(T² + ½) for every point h ⊂ W, |y_e, h′| = √(T²+½) for every
point h′ ⊂ W′. Hence for every class x (all q+1 of them)

    s^x_e = 2T + 1 − 2√(T²+½) ≥ 1 − 1/(2T),     s^x_e → 1 = δ/√2   (T → ∞).

*Proof.* Let u, v be a basis of W and u′, v′ of W′, r a basis of R. The basis f = (u, v, r, u′, v′) is adapted to x_e and
y_e, with level vectors (a,a,0,…,0,−b,−b) and (−b,−b,0,…,0,a,a), a = (1+T)/2, b = T/2. Their difference has four
entries ±(a+b), so |x_e y_e| = 2(a+b) = 2T+1. The hub u is the vector e₁ in f, so
|x_e,u|² = (a−1)² + a² + 2b² = (T²+1)/2 + T²/2 = T² + ½. For any other point h ⊂ W choose a basis (h, u₁) of W: the basis
(h, u₁, r, u′, v′) is again adapted to x_e, with the same level vector, and h is its first vector; so |x_e, h|² = T² + ½
for every h ⊂ W. The same for y_e and W′. ∎

In words: x_e and y_e lie on a Euclidean line (in the apartment of f) through the points
z(a) = (e_u+e_v)/2 and z(a′) = (e_{u′}+e_{v′})/2, which are at distance 1; z(a) is the common midpoint of every two
points of W (the q+1 hubs of the node form a pod with centre z(a) and arms 1/√2), and the leg x_e is equidistant from
all of them. Four hubs of two generic nodes span a flat regular tetrahedron. This is exactly the equality structure
of the cap (`notes.md` §5.5; attain-notes §7 (a)–(c)): hubs pairwise at distance δ, node pods with arms δ/2,
|z(a)z(a′)| = δ/√2, edge lines through the centres and "horizontal" for the arms.

Rank-one edges. Let W ∩ W′ = ⟨i⟩ and let k₁ ∈ P be a class with (a−a′)x_{k₁} ≠ 0, h = h^{k₁}(a) ⊂ W, h′ = h^{k₁}(a′) ⊂ W′.
Then h, i, h′ are independent; complete them to a basis f = (h, i, r, h′) and take d = (1, 0, …, 0, −1)/√2,
x = F^{f,Td}, y = F^{f,−Td}. By Lemma 1.4, s^{k₁} → d_h − d_{h′} = √2. Every point of W other than h has support {i} or {h, i} in f, so
its min is 0; every point of W′ other than h′ has support {i} or {i, h′}, so its max is 0. So

    s^{k₁}_e → √2,   s^k_e → 0 for k ≠ k₁,

and this is optimal for such an edge within placements with these hubs (s^k + s^l ≤ 2|z(a)z(a′)| = √2 by the midpoint
step of Cor. 3.4, and s^{k₀} ≤ 0 for the common class). For a collinear edge of class k₀ take k₁ = the successor of k₀ in a cyclic order of P; then every merge receives √2
from exactly E_coll/p = E/(g+1) edges. (Rank-one edges with kernel slope outside P can be used in the same way; they
are not counted below.)

**Theorem A [D].** For the placement above, as T → ∞,

    min_k b_k / E  ≥  (g−q)/(√2 (g+1)) + 1/(g+1).

On any set C of generic edges (with the same hubs) min_k b_k/|C| → 1/√2. In particular
F_CAT(𝒩(q,m,P)) ≥ 1/√2 − ((q+1)/√2 − 1)/(g+1), and F_CAT(C) = 1/√2 for every balanced set C of generic edges.

*Proof.* b_k = Σ_e s^k_e/√2; generic edges contribute 1/√2 each, the assigned rank-one edges 1 each. The upper bound
is Cor. 3.4 (valid in every CAT(0) space): value ≤ √(E_×/(2E)) = √(g/(2(g+1))) for the full level, and ≤ 1/√2 for
every balanced fully crossing configuration (Thm 3.2 for each pair of merges). ∎

[N] `q1_verify.py` evaluates the placement with the distance formula of §1 (no use of Lemma 1.4 or of the
proposition): s^k = 0.99995 on all generic edges at T = 10⁴; min_k b_k/E = 0.48279, 0.58247, 0.64111 for
g = 4, 8, 16 (formula: 0.48284, 0.58252, 0.64115); caps 0.6325, 0.6667, 0.6860. The coordinator re-derived the
distances by hand and re-ran the script.

**Finite g.** For q = 2, p = 3 the deficit below 1/√2 is between 0.354/(g+1) (cap, to first order) and 1.121/(g+1)
(placement). Within placements having these hubs the rank-one edges cannot do better (previous paragraph), so closing
the O(1/g) gap needs either other hubs or a sharper cap: the Cauchy–Schwarz step of Cor. 3.4 treats an edge internal
to merge k₀ as if |m_{k₀l}(n) m_{k₀l}(n′)| could be δ/√2, while it is at most δ/2. I did not optimise this.

### 2.3 Remarks

1. **Dimension.** The flats of 𝒞_{m+2} have dimension m+2 = log_q g + 2, while the Euclidean optimum for two merges
   uses 2g−2 dimensions. The chain of Cor. 3.4 only needs every generic rectangle {u_a, u_{a′}, v_b, v_{b′}} to be an
   independent 4-set; the building supplies a different apartment for each. With m = 2 and q → ∞ (nets of order q²
   with slopes in F_q) the space is the cone over an A₃ building: **three-dimensional flats suffice**; the generic
   fraction is (q²−q)/(q²+1) → 1. Two-dimensional flats (m = 1, cone over the A₂ building of PG(2,q)) give nothing: all
   node-lines meet, and then Σ_k s^k_e ≤ √2 instead of p (see §6).
2. **All p at once.** The same placement serves all q+1 slopes: with p merges the floor is still E/√2 per merge. At
   node growth β = 2 the exponent is ½ for every p. The table of `notes.md` §5.4 ("pod floor") is superseded for
   these nets: every entry of the column becomes 0.7071.
3. **Mechanism.** In a tree, a far point can be equidistant from the three tips of a tripod only by sitting over the
   centre, and then it sees no hub of another node favourably. In 𝒞_N the leg x_e sits over the centre z(a) of the
   pod of node a *and* moves in a flat direction along which the hubs of a′ recede.

---

## 3. Theorem B: every finite subset of 𝒞_N(2^s) is a price when contracting fails

**Theorem B [D].** Suppose the contracting hypothesis fails over k. Let q = 2^s and let P be a finite subset of
𝒞_N(q). Then the metric d restricted to P is a price over k.

The proof produces **one** price on P whose value on every pair is d. It has six steps; the source of each is named.

**Step 0 (normalisation).** The map "replace every level s by ½ + εs" multiplies d by ε. Prices are closed under
positive multiples (K-AN Def. A.4), so we may assume P ⊂ K_N(q) (all levels in [0,1]).

**Step 1 (finitely many bases).** For each pair {p,p′} ⊂ P choose a basis f_{pp′} adapted to both (Lemma 1.1(a)). Let ℬ
be the set of these bases and 𝔉 the set of all coordinate subspaces of all f ∈ ℬ (at most |ℬ|·2^N subspaces; it
contains 0, V and every member of the chain of every p ∈ P).

**Step 2 ((𝔉, τ) is a price).** Source: `ports/middle/notes.md` §1.2 [R there], `thm_alt_rank_price`.
- (2a) Restriction of scalars F_q^N = F₂^{sN} preserves sums and intersections and multiplies dimensions by s:
  τ_{F₂} = √s·τ_{F_q}.
- (2b) For subspaces of F₂^n (n = sN) the map U ↦ U ⊕ U⁰ ⊂ F₂^n ⊕ (F₂^n)^* (U⁰ the annihilator) goes into the
  n-dimensional subspaces of F₂^{2n}, and dim((U⊕U⁰) + (U′⊕U′⁰)) − n = dim(U+U′) + (n − dim(U∩U′)) − n = τ(U,U′)².
- (2c) Let U₁, …, U_r be n-dimensional subspaces of F₂^{2n} and Q = 2^t > r. Over F_Q the spaces U_i ⊗ F_Q have a
  common complement C (choose its basis vectors one at a time outside the union of the r proper subspaces
  U_i ⊗ F_Q + C_partial). With A = U₁ ⊗ F_Q each U_i ⊗ F_Q is the graph of a linear map a_i: A → C, and
  dim(U_i + U_j) − n = rk_{F_Q}(a_i − a_j). The regular representation Mat_n(F_Q) ⊂ Mat_{nt}(F₂) is additive and
  multiplies ranks by t.
- (2d) So there is a map ι: 𝔉 → Mat_μ(F₂), μ = nt ≥ 3, with τ_{F_q}(U,U′)² = rk(ι(U) − ι(U′))/(st). By
  `thm_alt_rank_price` √rk is a price on Mat_μ(F₂); pull-backs and multiples of prices are prices.

**Step 3 (price space).** By K-AN Prop. C.3 there are a price space Y (complete CAT(0), its metric is a price) and a
map j: 𝔉 → Y with |j(U) j(U′)| = τ(U,U′).

**Step 4 (cubes).** Source: K-AN D.2 Step 8 = `notes.md` Lemma 4.1 (segment filling; from C.4(a),(f); refereed).
For f ∈ ℬ the 2^N coordinate subspaces ⟨f_i : i ∈ S⟩ have τ² = |S Δ S′|, the metric of the vertices of [0,1]^N.
Fill one coordinate at a time: if the map is isometric on [0,1]^i × {0,1}^{N−i}, Lemma 4.1 with
Z = [0,1]^i × {0,1}^{N−i−1} and h = 1 makes it isometric on [0,1]^{i+1} × {0,1}^{N−i−1}. Result: an isometric embedding
Φ_f: [0,1]^N → Y with Φ_f(1_S) = j(⟨f_i : i ∈ S⟩).

**Step 5 (the fillings agree where they must).**

*Lemma 3.1 [R].* Let σ = conv(v₀,…,v_k) be a Euclidean simplex and φ, ψ: σ → Y isometric embeddings into a CAT(0)
space with φ(v_j) = ψ(v_j) for all j. Then φ = ψ.
*Proof.* Induction on k. On the face opposite v₀ they agree. A point p ∈ σ lies on a segment [v₀, p′] with p′ in that
face; φ and ψ map this segment isometrically onto a geodesic from φ(v₀) to φ(p′), which is unique (C.4(a)); so
φ(p) = ψ(p). ∎

Let p ∈ P have chain 0 ⊊ V₁ ⊊ … ⊊ V_k = V and levels 1 ≥ s₁ > … > s_k ≥ 0, and let f ∈ ℬ be adapted to p. Its level
vector is

    x = (1 − s₁)·1_0 + Σ_{j=1}^{k} (s_j − s_{j+1})·1_{V_j}      (s_{k+1} := 0),

where 1_U ∈ {0,1}^N marks the basis vectors lying in U: a convex combination of the vertices 0, V₁, …, V_k of the cube
of f, with coefficients that depend on p only. These vertices are affinely independent (a chain), their mutual
distances √(dim V_j − dim V_i) do not depend on f, and Φ_f maps them to j(0), j(V₁), …, j(V_k). By Lemma 3.1 the point
Φ(p) := Φ_f(x) does not depend on the choice of the adapted basis f ∈ ℬ.

**Step 6 (one price).** For p, p′ ∈ P the basis f = f_{pp′} is adapted to both, so
|Φ(p) Φ(p′)| = |Φ_f(x) Φ_f(x′)| = |x − x′| = d(p,p′). The metric of Y is a price; its pull-back along Φ: P → Y is a
price on P (K-AN Def. A.4: pull-backs to finite sets), and it equals d on every pair. ∎

What is reused from the refereed product-hull theorem (`notes.md` Lemma 4.1–Thm 4.3): the segment filling, and the
pattern of Lemma 4.2 ("isometry is a condition on pairs; any two points lie in one flat piece; two pieces agree on
their overlap by uniqueness of geodesics"). The diamond D_m is the case N = 2: K₂(q) is the union of the squares
[0,p_i] × [0,p_j] glued along the diagonal [0,V]. New here: Step 2 (all coordinate subspaces of several bases in one
price) and the form of the overlaps (the simplex of a chain).

**Corollary 3.2 (the hull; P1) [D].** In Step 4–5 take ℬ = all bases. Then Φ: K_N(q) → Y is an isometric embedding,
its image is convex (the geodesic between two points is the image of the segment in a common cube) and closed, and
every convex set containing j(Sub(V)) contains it. So **the closed convex hull of (Sub(F_q^N), τ) in a CAT(0) space is
K_N(q)** = the union of the cubes of all bases = {points of Cone(Δ) × ℝ with all levels in [0,1]}. It contains a ball
around the centre (all levels ½), and a ball of Cone(Δ) × ℝ is, after scaling, any bounded part of it.

**Corollary 3.3 (Mat_μ(F₂)) [D].** a ↦ U_a = graph of a embeds (Mat_μ(F₂), √rk) in K_{2μ}(2) at scale 1/√2
(dim(U_a + U_b) − dim(U_a ∩ U_b) = 2 rk(a−b)); 0 and I go to the two ends of a diagonal of a μ-dimensional cube whose
centre is the centre of K_{2μ}. The hull of Mat_μ(F₂) lies in the slice {Σ_i x_i = μ} (an affine function on every
cube). It is a proper subset of the slice: a μ-dimensional subspace that is not a graph is a vertex of every cube
that contains it, hence an extreme point, and is not in the hull of the others. I did not determine the hull of the
big cell exactly; it is not needed, because Step 2 reaches all subspaces through extension fields.

What the class contains: pods with q+1 arms (N = 2), pod × ℝ^M, all finite ℓ₂-products of such (block sums), cones
over A_{N−1} buildings. Not contained (the reason is geometric, not a proof of non-realisability as a price): trees
with two branch points (in Cone(Δ) × ℝ three pairwise opposite directions exist only at points whose link is a join
with a discrete set, and a geodesic leaving such a point does not meet a second one of the same kind in the right
position); affine buildings with their Euclidean metric (the lattice model of `ports/middle` §1.2 has √ℓ₁, not ℓ₂,
relative positions).

---

## 4. Consequences for levels and engines

### 4.1 Theorem C (fixed configuration) [D]

Let q = 2^s, P ⊆ P¹(F_q), and let C be a finite set of generic edges of some 𝒩(q,m,P), with the induced merges.

**Theorem C.** If contracting fails over k: for every ε > 0 and every function τ(λ) = o(λ) there is λ₀(C, ε, τ) such
that for λ ≥ λ₀ every identity Σ_{i∈I} A_i = d·f_C over k (d ≠ 0, |I| ≤ 2^{τ(λ)}, f_C the product of the wires ⟨2^λ⟩_e,
e ∈ C) has a piece with c_k(A_i) ≥ (1/√2 − ε)·|C|·λ **for all merges k ∈ P at once.**

*Proof.* The placement of §2.2 restricted to C, with T = T(ε), is a finite subset of 𝒞_{m+2}(q); by Theorem B its metric
is a price; apply the price method (★) of `notes.md` §2 with b_k = |C|(2T+1−2√(T²+½))/√2. ∎

If C is balanced (Def. 2.1 of `notes.md`) no price and no CAT(0) placement gives more than |C|/√2 (Thm 3.2), so the
price floor of C is exactly |C|λ/√2.

**Per-level form (whole level as one configuration).** If contracting fails over k, then for every g = 2^m ≥ 4,
ε > 0 and τ = o(λ): every piece family with ≤ 2^{τ(λ)} terms for the three-merge level tensor of the net of F₂^m has a
piece with c_k ≥ (1/√2 − 1.13/(g+1) − ε)·E·λ for k = 1, 2, 3 at once, for λ ≥ λ₀(g, ε, τ).
(The coordinator's proposed wording is correct with c = 3/√2 − 1 < 1.13 and with "λ large" depending on g. The
dependence of λ₀ on g is not controlled: K-AN D.2 is a compactness argument — Step 2 takes a limit of prices as
s → √μ, and a price is by definition a limit of c·d_φ — so no rate comes out of it. This answers H32, first half: no.)

### 4.2 The fixed configuration X_q: a floor uniform in g

**Lemma 4.1 [R].** Let a, a′ be a generic pair in 𝒩(q,m,P) and S = im(a − a′) (a 2-dimensional subspace of F_q^m). The
coset a + Hom(F_q², S) is a sub-net isomorphic to 𝒩(q,2,P) (q⁴ nodes; two of its nodes are on a common line of class x
in the big net iff they are in the small one), and it is the only such coset containing the edge. Hence the generic
edges of 𝒩(q,m,P) are partitioned into copies of

    X_q(P) := the set of generic edges of 𝒩(q,2,P):   q⁴ nodes Mat₂(F_q), edges {a,a′} with a − a′ ∈ GL₂(F_q),

one copy for each pair (S, coset). Every edge of X_q crosses every merge. The remainder (rank-one edges) is the
fraction ξ = (q+1)/(g+1) of all edges. ∎

**X₄ := X₂({0,∞,1})**: 16 nodes (r,c) ∈ (F₂²)², merges r, c, r+c (four groups of four nodes each), 12 hubs, 48 edges
(each node has |GL₂(F₂)| = 6 neighbours), 96 legs. It is balanced: for lines G, G′ of different classes meeting in n₀,
the edges from G to G′ are the pairs (n₀ + σ⊗φ, n₀ + σ′⊗φ′) with σ ≠ σ′ nonzero: 6 = deg(n₀). So by Theorems A and 3.2:

**F_CAT(X₄) = 1/√2 exactly, and if contracting fails the price floor of X₄ is exactly 48λ/√2 in each merge.**

Smaller still: for D ∈ GL₂(F₂) the translation class E_D = {{a, a+D}} ⊂ X₄ is a perfect matching of the 16 nodes
(8 disjoint wires); it is balanced (for G, G′ of different classes #{y ∈ G : y + D ∈ G′} = 1 = deg) and fully crossing.
So **the eight-wire configuration E_D with three merges into 4 groups of 4 has F_CAT = 1/√2 and, when contracting
fails, price floor exactly 8λ/√2 per merge.** For two of the merges it is a union of four AN crossings (the partner of
a for merges k, l is a + B with Bx_k = 0, Bx_l = Dx_l), so 1/√2 is attained for two merges by App. B; the statement is
that the third merge cannot be used. (Concretely for D = I: wires {(r,c), (r+e₁, c+e₂)}.)

**Positive target (contrapositive of Theorem C).** A sequence λ → ∞ and identities Σ_i A_i = d·f_{E_D} (or f_{X₄}) over
k with 2^{o(λ)} pieces, in which every piece has min_k c_k(A_i) ≤ (1/√2 − η)·8λ (resp. 48λ) for a fixed η > 0, proves
the contracting hypothesis over k, hence power-saving 3-SAT (Theorem R in characteristic 0, C1 in characteristic p).
This is one fixed finite object; no tower and no growing configuration is involved.

### 4.3 Theorem D′ (tower form; repairs Theorem S for these nets) [D]

Let 𝒞 be a finite list of configurations, each a set of generic edges of some 𝒩(2^s, m, P) with |P| = p merges, and
consider (p, 2, 𝒞)-levels and engines in the sense of `c1d1` D1.1 (levels partitioned into all-crossing copies of
members of 𝒞 plus a remainder ξ; one identity with 2^{τ(λ)} pieces per C ∈ 𝒞; a term is evaluated under its best
merge).

**Theorem D′.** (i) If contracting fails over k, every (p, 2, 𝒞)-level has ρ ≥ (1−ξ)(1/√2 − ε_𝒞(λ)) with ε_𝒞 → 0
depending only on 𝒞, τ, k. (ii) Hence a (p, 2, 𝒞)-engine with log-exponent α′ > 1/2 along infinitely many n forces
the contracting hypothesis over k, and then items 3–4 of D1.3 (power-saving 3-SAT). (iii) The level of 𝒩(2^s, m, P)
is a (p, 2, {X_{2^s}(P)})-level with ξ = (2^s+1)/(g+1); so tower engines built from nets of F₂^m (three merges) or from
subfield-slope p-nets, with per-copy pieces for X_q, have certified exponent α′ ≤ 1/2 unless contracting holds.

*Proof.* (i) is Lemma D1 of D1.2 with Theorem C in place of the flat floor: for each C some piece is expensive under
every merge at once; the term using it on every copy costs at least Σ_copies (1/√2 − ε_C)|C|λ under every merge.
(ii) is the proof of D1.3 with θ = 2^{−α′} < 1/√2: some level has ρ ≤ (1−ξ)(1/√2 − η); by Lemma D2 some C ∈ 𝒞 has all
pieces below (1/√2 − η)|C|λ at that λ; 𝒞 is finite, so one C occurs for infinitely many n with λ → ∞, contradicting
Theorem C unless contracting holds. (iii) is Lemma 4.1. ∎

Scope, honestly: the class has per-copy pieces for a *fixed* finite list. A level whose pieces are indexed by
sub-configurations that grow with g (for instance pieces for whole translation classes of the order-g net) is covered
only by the per-level form of §4.1, with λ₀ depending on g. This is the same restriction as in D1; what has changed
is that the net levels now belong to the class (the referee's fix 2), with the floor equal to the cap.

With `notes.md` Cor. 3.4 (no price gives more than 1/√2) and the attainment agent's statement that the level-1
crossing game on nets has value → 1/√2 (two-merge pieces already reach it): **for nets of F₂^m the three-merge level
value is 1/√2 on both sides when contracting fails.** A third (or p-th) net merge buys nothing there.

---

## 5. What equality in the cap forces, and why 𝒞_N has it

For the record (this is how the placement was found; [D], details only sketched).

Equality in Cor. 3.4 for generic edges forces (cf. `notes.md` §5.5, attain-notes §7): (a) the hubs of two merges are
in "Euclidean position" as far as generic rectangles go: triangles (o^k_G; o^l_H, o^l_{H′}) are flat and
|m(G,H) m(G′,H′)|² + |m(G,H′) m(G′,H)|² = ½|o_Go_{G′}|² + ½|o_Ho_{H′}|²; (b) at every node the midpoints of the three hub
pairs lie on the line of every generic edge at that node; in the symmetric case they coincide, z(n), and the three
hubs form a pod around z(n) with the edge lines horizontal; (c) |z(n)z(n′)| = δ/√2 for generic pairs; then all hubs
of different classes are at distance δ as well, and collinear nodes have |z(n)z(n′)| = δ/2.

So the ideal object is: **a set of points pairwise at distance δ, in which concurrent triples are pods (common
midpoint), other triples are flat equilateral triangles, and two disjoint "lines" span pod × pod × segment.** For the
points and lines of a projective space this is exactly the geometry of 𝒞_N: independent points are the vertices of a
flat regular simplex (the basis vectors), and the points of a projective line W are pairwise at distance √2 with the
common midpoint "W at level ½" (K₂ = diamond of the K_{2,m} notes). The net enters as the planes complementary to a
subspace of codimension 2. Locally: around the centre of the cube of a 4-space U = W ⊕ W′ the 16 nodes of a copy of X₄
are the 16 lines of PG(3,2) skew to U ∩ M, all at distance ½ from the centre, complementary ones antipodal, meeting
ones at right angles, and the hubs are at mutual angle arccos(−1/3) seen from the centre.

Two constraints that any other realisation (other groups) must respect, both [D]:
- Around a hub the centres of its g nodes are pairwise at distance δ/2 and form flat equilateral triangles with the
  hub; the space branches along every segment [hub, z(n)] (q arms continue to the other hubs of n).
- For two collinear nodes n, n″ on a line G the four flat triangles (o_G; o^l(n), o^{l′}(n″)), l, l′ ≠ k, share the kite
  (o_G, z(n), X, z(n″)), X their common centroid, and the link at X is K_{3,3} with edges π/3, 2π/3 — a piece of the
  incidence graph of a projective plane. This is what suggested buildings of type A.

---

## 6. Dead ends [X] and negative results

1. **[X] Cone over the incidence (Levi) graph of the net**, hubs at line vertices at radius t, nodes at point
   vertices, edge length φ, legs along the node rays. Generic nodes are at graph distance 4φ ≥ π, so the two rays form
   a line, s^k = 2t cos φ, δ = 2t, Φ = 9cos²φ. The net has triangles, so the graph has 6-cycles and CAT(1) needs
   φ ≥ π/3: **Φ = 9/4 < 3** (worse than flat). φ = π/4 would give 9/2, but the hexagons would be closed local geodesics
   of length 3π/2 < 2π. Filling them (octants) changes the geometry: generic nodes are then at angle π/2, not π, and
   one is led to §5.
2. **[X] Cone over the incidence graph of PG(2,q) (edges π/3; the vertex link of an Ã₂ building)**, hubs at the 3g
   line vertices of the net, radius t. Hubs are pairwise at 2π/3 (δ = √3 t), a node is at π/3 from its three hubs, but
   two nodes are at 2π/3, never opposite. Best legs: a geodesic of length π through both node vertices and their
   common neighbour, ends at π/6 beyond each: Σ_k s^k = √3 t. **Φ = 1.** Reason for both: rank 2. In a 2-dimensional
   cone any two node-lines meet, and (Lemma 6.1) meeting lines give Σ_k s^k ≤ δ instead of pδ/√2. The dimension of the
   flats must be at least 3 (and at least log_q g + 2 in the family of §2).
3. **Lemma 6.1 [R].** In 𝒞_N with hubs at points: if the lines W, W′ of two nodes meet in a point i, then for all legs
   Σ_{k} s^k_e ≤ √2 = δ (any number of classes).
   *Proof.* Legs can be pushed to infinity along a line of an apartment containing them without decreasing any s^k
   (triangle inequality), so Lemma 1.4 applies: s^k = ν(h_k) − ν̄(h′_k), ν(h) = min_{supp h} d, ν̄(h) = max_{supp h} d. ν is
   a valuation, so on W it takes one value a on all points except at most one point J, where ν(J) = a⁺ ≥ a; likewise
   ν̄ = b on W′ except at most one J′ with ν̄(J′) = b⁻ ≤ b; and ν(i) ≤ ν̄(i). If i ∉ {J, J′}: a ≤ b and
   Σ_k s^k ≤ p(a−b) + (a⁺−a) + (b−b⁻) ≤ a⁺ − b⁻. If i = J ≠ J′: all ν(h_k) ≤ a⁺ ≤ b, so Σ ≤ a⁺ − b⁻. Symmetrically for
   i = J′ ≠ J, and for i = J = J′ every term is ≤ 0. Finally a⁺ − b⁻ = d_j − d_{j′} ≤ √2 for a unit vector d. ∎
4. **Proposition 6.2 (Z₃ has no skew realisation) [R].** Let R_r, C_c, D_d (r, c, d ∈ Z₃) be s-dimensional subspaces
   of a vector space over any field with W_{rc} := R_r + C_c of dimension 2s and D_{r+c} ⊂ W_{rc}. Then all nine lie in
   a space of dimension ≤ 3s, and any two W's meet in dimension ≥ s.
   *Proof.* S := W₀₀ + W₁₂ has dimension ≤ 3s (both contain D₀) and contains R₀, R₁, C₀, C₂, D₀; then W₀₂, W₁₀ ⊂ S, so
   D₂, D₁ ⊂ S; then R₂ ⊂ W₂₀ = C₀ + D₂ ⊂ S and C₁ ⊂ W₀₁ = R₀ + D₁ ⊂ S. ∎
   The same closure argument shows: for any group Γ and collinear nodes n, n′ differing by d, the sub-net over the
   cyclic group ⟨d⟩ lies in W_n + W_{n′}. For Γ = F_q^m this is a plane's worth (order q); for a cyclic Γ it is
   everything. So **cyclic nets have no realisation of this kind**, and Δ₃ (generic edges of the Z₃ net) gets
   Σ_k s^k ≤ √2 per edge from point hubs on node-lines: value ≤ 1/3, worse than flat.
5. **[X] Direct sums of planar realisations** (one block per character of Z_p^m ⊂ F_q^*): the blocks are subspaces,
   the incidences hold blockwise, but W_n ∩ W_{n′} is the sum of the blockwise intersections: always half.
6. **[X] tripod³ for Δ₃.** If 1/√2 were attained exactly on Δ₃, the three node-centres of each class-4 line would
   form a tripod and all nine centres would have a common centre c₀, the three class-4 lines being mutually
   perpendicular there (flat squares by C.4(f)) [D]. In tripod³ with the hubs at the corresponding nine "octant"
   points, hubs of different classes are at the right distance δ with the right common midpoints, but hubs of the
   same class are at √(3/2)·δ; value 1/√3. Whether another CAT(0) space has the exact structure for Δ₃ is open.
7. **[X] Products.** A product never beats its best factor (one-factor reduction, attain-notes), and a tree factor
   with a tight bimedian step has, for each pair of merges, all hubs of the two merges on one geodesic: so the gain
   over the pod value has to come from an irreducible factor with flats of dimension ≥ 3.
8. Correction to `notes.md` §5.5: the guess "cones over spherical buildings of type A₂/B₂" was right in kind (type
   A) and wrong in rank (A₂ is too small; A₃ is the first that works). The retraction of "impossible in pod × ℝ^M"
   stands: pod × ℝ^M is a product and cannot beat max(pod, flat).

---

## 7. Lemma S (attainment agent's Steiner crossing inequality) in 𝒞_N

One paragraph, as asked. (i) In the non-contracting world and q = 2^s, Lemma S is not needed for placements in 𝒞_N:
by Theorem B the placement is a price and the price method bounds all covers of all depths. Lemma S in 𝒞_N would make
the statement about crossing-generated covers unconditional (and extend it to odd q). (ii) Plausibility: the tangent
cone of 𝒞_N at any point is again of the same kind (a product of cones over spherical buildings of type A of smaller
rank and a Euclidean factor), so any first-order reduction stays inside the class "cones over A-type buildings";
rank 1 is the pod, where the linearised inequality fails but no violation of Lemma S was found. Every generic edge of
the placement of §2 with its 2(q+1) hubs lies in pod(W) × pod(W′) × ℝ^{m} (the sub-building of the decomposition
V = W ⊕ R ⊕ W′), which is inside the class already tested numerically (`lemmaS.py`, tripod × tripod: no violation). (iii)
The first configuration *not* of product type is two collinear nodes: W ∩ W″ = one hub i, the 3-space W + W″, the
sub-building 𝒞₃(2) = Cone(incidence graph of the Fano plane, edges π/3) × ℝ. Test there: legs at the five points of
W ∪ W″ (level-1 points), two wires joining the two points of W ∖ i to the two points of W″ ∖ i (the level's own
crossing for the two merges that the edge crosses), auxiliary hubs free in 𝒞₃(2); far legs by Lemma 1.4. In the
apartment of a basis containing four of the five points this is a planar Euclidean crossing with margin 0; the
question is whether hubs leaving the apartment through the third chamber at a wall lower a child's value. I have no
argument either way beyond (i): if the game ever lost there with q even, it would prove contracting.

---

## 8. Open problems and specs

**Open.**
1. **Other groups.** F_CAT (and the price floor) for 3-nets of cyclic groups Z_g, of Z₄^m, of non-abelian groups; for
   Δ₃ (in [2/3, 1/√2]); for p ≥ 4 nets of F_g whose slopes are not in a subfield of unbounded codegree. By
   Prop. 6.2 these need something other than points on lines of a projective space. Candidates I did not work out:
   (a) for cyclic Γ, carry-free digit maps Γ ⊃ box → F_q^m (the incidence w_{a+b} ∈ ⟨u_a, v_b⟩ then holds only for pairs
   without carries; the value depends on how the bad nodes are placed) [C]; (b) hubs at higher vertices or interior
   points of 𝒞_N; (c) an upper bound: an inequality valid in all CAT(0) spaces that sees the cyclic structure (the
   sub-net over ⟨d⟩ being everything) and gives a cap < 1/√2 for prime order.
2. **Odd q as prices.** Is √rank on Mat_μ(F₃) (or τ on Sub(F₃^N)) a price when contracting fails? Then nets of F₃^m
   would be closed too. Not implied by anything here.
3. **O(1/g).** The exact value of F_CAT at finite g (deficit between 0.35/(g+1) and 1.12/(g+1) for q = 2).
4. **Rate.** A quantitative form of `thm_alt_rank_price` (H32). None is available; §4.2–4.3 avoid the need for
   engines with per-copy pieces.
5. **Lemma S in Cone(A₂) × ℝ** (§7).

**Specs for executors.**
- **E1 (referee, 1–2 h).** Lemma 1.1, Lemma 1.4, Prop. 2.1, the rank-one edges, Theorem B Steps 0–6 (press on Steps
  2c and 5), Lemma 4.1 (partition into copies of X_q), balance of X₄ and E_D, Lemma 6.1, Prop. 6.2.
- **E2 (independent numeric check, 30 min).** Re-implement d on filtrations (formula in §1) and reproduce
  `q1_verify.py`; in addition verify the partition of the 1344 generic edges at g = 8 into 28 copies of X₄ (7 planes S
  × 4 cosets) and the balance of X₄ and of E_D for the six D ∈ GL₂(F₂).
- **E3 (Δ₃ and small nets in 𝒞_N, compiled search).** Hubs: 9 points of PG(N−1,q), q ∈ {2,3,4}, N ≤ 6 (or subspaces
  of dimension ≤ 2). For an edge with hub points h_k (at n), h′_k (at n′):
  c_e = max over bases f and unit d of Σ_k [min_{supp_f h_k} d_i − max_{supp_f h′_k} d_i]
      = max over bases f of the distance from 0 to conv{Σ_k (e_{i_k} − e_{j_k}) : i_k ∈ supp_f h_k, j_k ∈ supp_f h′_k}
  (a small convex QP; the function is concave and positively homogeneous in d; 0 if the hull contains 0).
  Value = Σ_e c_e/(27·√2) for nine distinct points; compare with 2/3 (tree products) and 0.7071. With coinciding hubs
  use the one-factor ratio S/D̄. Report the best configuration and whether any beats 2/3. Same for the order-4 net
  with all 120 edges (to probe the O(1/g) gap) and for Z₅.
- **E4 (level-2 game on E_D).** For the attainment agent: the eight-wire configuration E_D is the smallest object on
  which "three merges beat two" would have to show; F_CAT = 1/√2 there.
