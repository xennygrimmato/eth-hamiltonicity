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
