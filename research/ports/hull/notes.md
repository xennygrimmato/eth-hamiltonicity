# Hull lemma, tripod × ℝ, and the K_{2,3} rate

Theory notes, 26 Nov 2026. Tags: [R] proved here (complete proof in these notes, from cited statements);
[D] derived, unreviewed or resting on an uncertified step; [C] conjecture; [X] dead, with the reason;
[K] quoted (pointer given); [N] computed. "AN" = Anthropic's "VP ≠ VNP over every field" (line numbers refer
to the pdftotext copy `scratchpad/fm/paper.txt`). "OA" = OpenAI's unrefereed 24 Nov 2026 release (EG, HC, IM
as in `ideas-ports.md`); every use of OA is flagged [OA]. A referee pass on §1 is in `../review-hull.md`.

Notation. Parties u₁,u₂,v₁,v₂,v₃. S = the six wires u_iv_j, T = the wires v₁v₂, v₂v₃, v₁v₃, u₁u₂ (all binary).
For a pseudometric d on the five parties: Σ_S d = Σ_{k,i} d(u_k,v_i), Σ_T d = d(u₁,u₂) + Σ_{i<j} d(v_i,v_j),
R(d) = Σ_S d / Σ_T d. κ = 3/√10 = 0.9486832980…
W5(ℓ,h): v_j at distance ℓ on the three legs of a tripod, at height 0; u_i at the hub at heights ±h, in
tripod × ℝ. R = 6√(ℓ²+h²)/(6ℓ+2h); minimum κ at h = ℓ/3.
ρ_μ(a,b) = √rk(a−b) on Mat_μ(F₂). Contracting(k) = AN Definition D.1 over the field k.
f*(K_{2,3};k) = sup{ f : T^{⊗⌈fn⌉} is a restriction of S^{⊗(n+o(n))} over k }.

---

## 0. Summary of status

| # | Statement | Tag |
|---|---|---|
| 1 | **Hull lemma (Lemma H).** Any CAT(0) space containing the five-point set N5 = √(graph metric of K_{2,3}) contains the solid diamond D ⊂ tripod × ℝ isometrically, hence every W5(ℓ,h). | [R] from AN C.4(a),(f); refereed |
| 2 | N5 ⊂ (Mat₂(F₂), ρ₂) ⊂ (Mat₃(F₂), ρ₃). | [R] |
| 3 | N5 a price over k ⇔ every finite subset of (infinite tripod) × ℝ is a price over k. | [R] (Cor. H1, H3) |
| 4 | Contracting(k) fails ⇒ N5 and all W5(ℓ,h) are prices over k. | [R] given AN `thm_alt_rank_price` (Lean) |
| 5 | Any AN price d bounds the tensor rate: f*(K_{2,3};k) ≤ R(d). Border protocols included over infinite k. | [R] (§2) |
| 6 | Contracting(k) fails ⇒ f*(K_{2,3};k) ≤ 3/√10. | [R] from 4, 5 |
| 7 | A protocol on K_{2,3} over a field of characteristic 0 with asymptotic rate > 3/√10 ⇒ Contracting ⇒ 3-SAT in 2^{O(v^{1−δ})}. | first arrow [R]; second arrow [D]: Theorem A (AN F.6 + [OA] HC 4.2) then [OA] IM 7.1, or Theorem R (AN only, `../rebase/`, [D]) |
| 8 | **Book reduction.** For five points of a CAT(0) space, R ≥ R of the book of three flat comparison triangles on the common side [u₁,u₂]. | [R] from AN C.4(a) (§3.1) |
| 9 | **Calibration.** In a book, Σ_S − κ Σ_T ≥ (D/√10)·Φ(ψ), Φ the explicit function of the six exit angles in §3.3. | [R] (§3.2; algebra checked numerically on 20 000 random books, [N]) |
| 10 | **Inequality (CL\*)**: Φ ≥ 0 on [−π/2,π/2]⁶. Contains the three-angle inequality (I). | [N] (no violation; equality set located); analytic proof missing; spec for an interval certificate in §3.3 |
| 11 | **Five-point theorem.** Every five-point subset of a CAT(0) space, hence every AN price on five parties, has R ≥ 3/√10. | [D]: = 8 + 9 + 10. Independent [N] support: Toyoda's five-point criterion gives minimum 3/√10 (executor, 1000/1000 multistarts) |
| 12 | f*(K_{2,3};k) ≥ 3/√10 over every field; = 3/√10 whenever Contracting(k) fails. | [D], = 11 + Strassen duality + 6 |

---

## 1. The hull lemma

### 1.1 The set N5

In Mat₂(F₂) put

    n = 0,  s = I = e₁₁+e₂₂,  t₁ = e₁₁,  t₂ = e₂₁+e₂₂,  t₃ = e₁₂+e₂₂.

[R] Ranks: t_i has rank 1 (e₁e₁ᵀ, e₂(e₁+e₂)ᵀ, (e₁+e₂)e₂ᵀ); I − t₁ = e₂₂, I − t₂ = (e₁+e₂)e₁ᵀ,
I − t₃ = e₁(e₁+e₂)ᵀ have rank 1; t₁−t₂ = [[1,0],[1,1]], t₁−t₃ = [[1,1],[0,1]], t₂−t₃ = [[0,1],[1,0]] and I are
invertible. Hence under ρ₂

    |n s| = |t_i t_j| = √2 (i ≠ j),    |n t_i| = |s t_i| = 1.

So **N5 is the square root of the graph metric of K_{2,3}**, with {n,s} the 2-side and {t₁,t₂,t₃} the 3-side.
(R(N5) = 6/(4√2) = 1.06; the gain comes from the hull.)

General form: n = a, s = a+W with rk W = 2, t_i = a+R_i with R_i of rank one, rk(W−R_i) = 1, rk(R_i−R_j) = 2.
For W = I the admissible R are the uxᵀ with xᵀu = 1; there are six, forming a hexagon under "difference of rank
one", and the two triples of pairwise non-adjacent ones are the two choices of {t_i}. In the Grassmannian
picture (a ↦ graph Γ_a ⊂ F₂⁴): Γ₀ = P and Γ_I = P′ are complementary planes and t_i ↔ ⟨p_i, ψ(p_i)⟩ for a linear
bijection ψ: P → P′; these three planes are pairwise complementary. In the building of GL₄(F₂((t))) they are
three pairwise opposite vertices of the link of [O⁴].

N5 is not Euclidean [R]: with the origin at the midpoint of n,s the conditions give t_i ⊥ (s−n), |t_i|² = 1/2,
t_i·t_j = −1/2, i.e. t_j = −t_i for all three pairs. Every four-point subset of N5 is Euclidean.

### 1.2 Statement

**Lemma H [R].** Let Y be a CAT(0) space in the sense of AN §C.4 (complete; midpoints satisfying CN) and let
n, s, t₁, t₂, t₃ ∈ Y satisfy, for some a > 0,

    |n s| = |t_i t_j| = √2·a (i ≠ j),    |n t_i| = |s t_i| = a.

Let 𝕋 be the tripod with legs of length a/√2 and hub o, and
D = { (ξ,σ) ∈ 𝕋 × ℝ : |ξ o| + |σ| ≤ a/√2 } with the ℓ₂ product metric. Then there is an isometric embedding
Ψ: D → Y with Ψ(o, ∓a/√2) = n, s and Ψ(tip_i, 0) = t_i. In particular for all ℓ, h ∈ [0, a/√2] the points
v_i = Ψ(point at distance ℓ on leg i, 0), u_± = Ψ(o, ±h) have the metric W5(ℓ,h).

Used about CAT(0) spaces: AN Lemma C.4(a) (unique geodesics) and C.4(f) (flat rectangles): "Suppose that
|xy| = |uv| = δ and |xu| = |yv| = h, that both diagonals of the quadrilateral x, y, v, u have the squared length
δ² + h², and that a ∈ [x,u] and b ∈ [y,v] have |xa| = sh and |yb| = th. Then |ab|² = δ² + h²(s−t)²."
Both are in AN's Lean (lem_toolkit).

### 1.3 Proof

**Step 1 (solid squares; AN D.2 Step 8 for one square).** Let x, y, v, u ∈ Y have
|xy| = |yv| = |vu| = |ux| = a and |xv| = |yu| = √2·a. For s ∈ [0,1] let α(s) ∈ [x,u], β(s) ∈ [y,v] be the points
at fraction s. By C.4(f) with δ = h = a,

    |α(s) β(t)|² = a²(1 + (s−t)²).                                                  (1)

Also |α(s)α(s′)| = |β(s)β(s′)| = a|s−s′|. Fix s ≠ s′ and put x′ = α(s), u′ = β(s), y′ = α(s′), v′ = β(s′). Then
|x′y′| = |u′v′| = a|s−s′| =: δ′, |x′u′| = |y′v′| = a =: h′, and both diagonals x′v′, y′u′ have squared length
a²(1+(s−s′)²) = δ′² + h′² by (1). So C.4(f) applies again: with Φ(s,r) the point at fraction r on [α(s), β(s)],

    |Φ(s,r) Φ(s′,r′)|² = a²((s−s′)² + (r−r′)²).

For s = s′ this is trivial. Hence Φ: [0,1]² → Y is a times an isometry with Φ(0,0) = x, Φ(1,0) = u, Φ(0,1) = y,
Φ(1,1) = v. Geodesics in Y are unique, so the image Q contains the geodesic between any two of its points, and
the two diagonals [x,v], [y,u] are the images of the diagonals of [0,1]²; they cross at Φ(½,½), the midpoint of
x,v and of y,u.

**Step 2 (one hub).** For i ≠ j apply Step 1 to (x,y,v,u) = (n, t_i, s, t_j). Let Q_ij be the solid square and
c = mid(n,s). Then c = mid(t_i,t_j) for every pair, and |c t_i| = |c n| = |c s| = a/√2.

**Step 3 (triangles).** Let Δ_i be the union of the geodesics [t_i, p], p ∈ [n,s]; it depends only on i. Inside
the flat convex square Q_ij it is the half on the t_i side of [n,s], and Q_ij = Δ_i ∪ Δ_j. With
Δ̄ = {(τ,σ) : 0 ≤ τ, τ+|σ| ≤ a/√2} ⊂ ℝ², the isometric parametrisation ψ_i: Δ̄ → Δ_i coming from Q_ij and the one
coming from Q_ik agree at the three vertices, hence everywhere (a point of Δ̄ is determined by its distances to
three affinely independent points).

**Step 4 (gluing).** Put Ψ(ξ,σ) = ψ_i(|ξ o|, σ) for ξ on leg i. Two points on the same leg have their images in
Δ_i, where the distance is Euclidean. Two points on legs i ≠ j have their images in the flat square Q_ij, whose
halves are Δ_i and Δ_j; the distance there is √((τ+τ′)² + (σ−σ′)²), and τ+τ′ is the distance in 𝕋. ∎

Remarks.
1. Nothing about buildings or the rest of Mat_μ(F₂) is used, and of D.2 only "ρ₃ is a price". The feared
   obstruction (only vertices or discrete midpoints forced; no u-points at height ±ℓ/3) does not occur: the
   u-points lie on the diagonal [0, I] of the flat squares and the price space of AN C.3 is geodesic.
2. No three points of (Mat_μ(F₂), ρ_μ) are collinear (√rk(A+B) < √rk A + √rk B), so branching is visible only in
   the hull; it is forced by five points.
3. [D] A second forced tripod in the hull of ρ₂: with the hexagon P₁ = e₁₁, P₂ = e₁₁+e₁₂, P₃ = e₂₁+e₂₂, P₁′ = e₂₂,
   P₂′ = e₁₂+e₂₂, P₃′ = e₁₁+e₂₁ the midpoints of the alternate sides P₁P₂, P₃P₁′, P₂′P₃′ are pairwise at distance 1
   and at distance ½ from c (quadrilateral inequality C.4(b) for (m₁,m₂,P₃,P₂): 5/4+5/4 ≤ |m₁m₂|²+¼+1+¼, after the
   flat-triangle lemma [BH99, II.2.9]). So near c the hull of ρ₂ is (tripod × tripod) × segment, as in the
   building. Not used elsewhere.
4. [D] Larger pods. Mat₂(F_{2^r}) ⊂ Mat_{2r}(F₂) with rk_{F₂} = r·rk_{F_{2^r}}, and Mat₂(F_q) contains q+1
   rank-one matrices R with I−R of rank one and pairwise invertible differences. So √(graph metric of K_{2,m})
   ⊂ ρ_{2r} up to the scale √r for m ≤ 2^r+1, and the proof of Lemma H gives (m-pod) × segment. Not checked by
   machine.

### 1.4 From Lemma H to prices: statements used

- **AN Definition A.4** (def_price; l. 1121–1129): "A price on a finite set V is a limit of functions c·d_φ […].
  A function on the pairs of elements of an arbitrary set Y is a price if all its pull-backs to finite sets are
  prices. […] Pull-backs, nonnegative multiples and pointwise limits of prices are prices."
- **AN Proposition C.3** (prop_space; l. 1608–1622): "Every price on a set V is the pull-back of the metric of a
  price space", a price space being "a CAT(0) space whose metric is a price" (l. 1600–1602).
- **AN `thm_alt_rank_price`** (Paper/Alternative.lean:706, per the referee): ¬Contracting(k), 3 ≤ μ ⊢ there is a
  price w on Mat_μ(F₂) with w² = rank of the difference. (In the paper: D.2 Steps 1–7 and Remark D.3.)

**Corollary H1 [R].** If N5 (any scale) is a price over k, then the metric of every finite subset of the
diamond D is a price over k; in particular every W5(ℓ,h).
Proof. By C.3 there are a price space Y over k and g: N5 → Y isometric. Lemma H gives Ψ: D → Y isometric; the
metric of Y is a price, so its pull-back to Ψ(F) is a price, and prices are closed under positive multiples. ∎

**Corollary H2 [R].** If Contracting(k) fails, N5 and all W5(ℓ,h) are prices over k.
Proof. `thm_alt_rank_price` with μ = 3; a ↦ diag(a,0) pulls ρ₃ back to ρ₂ ⊃ N5; apply H1. ∎

**Corollary H3 [R].** N5 is a price over k ⇔ every finite subset of 𝕋_∞ × ℝ (𝕋_∞ the tripod with infinite legs)
is a price over k.
Proof. ⇐: N5 = {(o,±1/√2), (tips at distance 1/√2, 0)} ⊂ 𝕋_∞ × ℝ. ⇒: a finite F ⊂ 𝕋_∞ × ℝ lies, after a
translation in the ℝ-direction, in {|ξo| + |σ| ≤ M} for some M, which is the diamond for a = √2·M; apply H1 to
N5 at that scale. ∎

[D] Also W5(ℓ,ℓ/3) a price ⇒ N5 a price: in a CAT(0) space each quadrilateral (u₁,v_i,u₂,v_j) of W5 is a rhombus
with equality in the quadrilateral inequality, hence flat ([BH99, II.2.11]-type rigidity; not in AN's toolkit),
and the union of the three flat rhombi contains N5 at scale ℓ/3. So "W5 is a price", "N5 is a price" and
"tripod × ℝ is a price space" are one statement.

---

## 2. Prices bound tensor protocols; which class of functionals is needed

**Claim [R] (referee's wording).** Let d be an AN price on the five parties with Σ_T d > 0. If T^{⊗m} is a
restriction of S^{⊗n} over k, then m·Σ_T d ≤ n·Σ_S d.
Proof. For a spectral point φ (AN A.1): 2^{m Σ_T d_φ} = φ(T^{⊗m}) ≤ φ(S^{⊗n}) = 2^{n Σ_S d_φ} by monotonicity,
multiplicativity and A.2. Multiply by c ≥ 0; the inequality is linear in the distances and closed, so it passes
to pointwise limits. ∎

Hence f*(K_{2,3};k) ≤ R(d) for every AN price d over k. Scope: "protocol" = exact restriction
T^{⊗m_n} ≤ S^{⊗n}, m_n/n → f, the same rate on all four demand wires (a non-uniform demand vector r tests
Σ_e r_e d(e) ≤ Σ_S d instead). Border protocols are included over infinite fields: a degeneration with maps of
degree D in ε writes T^{⊗m} as a sum of D+1 restrictions of S^{⊗n} (interpolation), and the cover clause of A.1
gives the factor D+1 = 2^{o(n)}. Not claimed for border protocols over small finite fields.

**Which spectrum [R].** The J-tensors over k with ⊕, ⊗ and restriction form a Strassen preorder (1 ≤ a for
a ≠ 0, and a ≤ ⟨r⟩ ≤ r·b). Strassen's theorem [Str88] gives: a^{⊗n} ≤ b^{⊗(n+o(n))} iff F(a) ≤ F(b) for all F in
the asymptotic spectrum 𝒳 (monotone, multiplicative, additive, normalised: the "OA" class). Therefore

    f*(K_{2,3};k) = min_{F ∈ 𝒳} R(d_F)          (exact; the minimum over F with F(T) > 1).

Every F ∈ 𝒳 is an AN spectral point (s = Σ s_j, s_j ≤ t_j ⇒ s ≤ ⊕ t_j ⇒ F(s) ≤ Σ F(t_j)). So
min over AN prices ≤ min over 𝒳 = f* ≤ min over AN prices (the last by the Claim): **the two minima coincide.**
A lower bound f* ≥ r needs R ≥ r on 𝒳 only, and may be proved for the larger AN class at no cost; an upper
bound needs one AN price. Nothing from OA is used in either direction.

---

## 3. The five-point theorem: R ≥ 3/√10 on every five-point CAT(0) set

Target. **Theorem 5 [D].** Let u₁,u₂,v₁,v₂,v₃ be points of a CAT(0) space (AN §C.4). Then
Σ_S ≥ κ·Σ_T, κ = 3/√10, with equality for W5(ℓ,ℓ/3).

Proof = Proposition 3.1 [R] + Proposition 3.2 [R] + Inequality (CL\*) [N; to be certified, §3.3].
It uses of CAT(0) only AN C.4(a), so it holds for every AN price on five parties (C.3).

### 3.1 Reduction to books [R]

Let D = |u₁u₂|. If D = 0 then Σ_T = Σ d_ij ≤ Σ_{i<j}(|u₁v_i|+|u₁v_j|) = Σ_S and R ≥ 1. Let D > 0, A_i = |u₁v_i|,
B_i = |u₂v_i|. For t ∈ [0,1] let c_t be the point at fraction t of [u₁,u₂]. AN C.4(a):

    |v_i c_t|² ≤ (1−t)A_i² + tB_i² − t(1−t)D² =: h_i(t)².

h_i(t) is the distance from the apex to the point at fraction t of the base in the Euclidean triangle with
sides D, A_i, B_i (Stewart). By the triangle inequality, for i ≠ j,

    |v_i v_j| ≤ min_{t∈[0,1]} ( h_i(t) + h_j(t) ) =: d^Z_ij.                          (2)

Geometric reading: let Z (the "book") be the three Euclidean triangles (ū₁,ū₂,v̄_i) glued along the common side
I = [ū₁,ū₂] (the "spine"). Two different pages meet only along I, so a path from v̄_i to v̄_j crosses I, possibly
at an end; d^Z_ij is the distance of v̄_i, v̄_j in Z. So Σ_S(Y) = Σ_S(Z), |u₁u₂| is the same, Σ_T(Y) ≤ Σ_T(Z), and
R(Y) ≥ R(Z). Only (2) is used below; that Z is itself CAT(0) (Reshetnyak gluing) is not needed.

### 3.2 Calibration in a book [R]

Coordinates. In page i use (ρ,a) with ρ ≥ 0 the distance from the line of the spine and a the height:
u₁ = (0,0), u₂ = (0,D), v_i = (ρ_i,a_i), ρ_i ≥ 0, a_i ∈ ℝ (the foot may lie outside [0,D]); c(y) = (0,y).
A_i = |v_i−u₁|, B_i = |v_i−u₂|, f_i(y) = |v_i − c(y)| = h_i(y/D).

*Hubs and exit vectors.* For i ≠ j let y_ij = y_ji ∈ [0,D] minimise f_i + f_j (convex in y), so
d^Z_ij = f_i(y_ij)+f_j(y_ij). Let e_ij = (c_ij,σ_ij) = (cos ψ_ij, sin ψ_ij), ψ_ij ∈ [−π/2,π/2], be the unit
vector of v_i − c(y_ij) in page i (first coordinate ρ_i/f_i ≥ 0). If v_i = c(y_ij), take for σ_ij any element
of the subdifferential [−1,1] for which the optimality relation below holds, and c_ij = √(1−σ_ij²). Then
f_i(y_ij) = ⟨e_ij, v_i − c(y_ij)⟩ = ρ_i c_ij + (a_i − y_ij)σ_ij, and since d/dy f_i = −σ_ij:

- y_ij interior: σ_ij + σ_ji = 0 (so ψ_ji = −ψ_ij: the path is straight in the unfolded pages i, j);
- y_ij = D (path through u₂): σ_ij + σ_ji ≥ 0;
- y_ij = 0 (path through u₁): σ_ij + σ_ji ≤ 0.

Put ε_ij = σ_ij + σ_ji, E₂ = Σ_{pairs with y_ij = D} ε_ij ≥ 0, E₁ = Σ_{pairs with y_ij = 0} |ε_ij| ≥ 0, so
Σ_{i<j} |ε_ij| = E₁ + E₂ and Σ_{i<j} ε_ij = E₂ − E₁. In all three cases y_ij·ε_ij = D·ε_ij·[y_ij = D]. Hence

    d^Z_ij = ρ_i c_ij + ρ_j c_ji + a_i σ_ij + a_j σ_ji − y_ij ε_ij,
    Σ_{i<j} d^Z_ij = Σ_i ( ρ_i P_i + a_i Q_i ) − D·E₂,                                   (3)

where (P_i,Q_i) = e_ij + e_ik ({j,k} = the other two indices), P_i ≥ 0, and Σ_i Q_i = E₂ − E₁.

*Calibration of the supply.* For any angles α_i, β_i (Cauchy–Schwarz with the unit vectors (cos α_i, sin α_i),
(cos β_i, −sin β_i)):

    A_i ≥ ρ_i cos α_i + a_i sin α_i,      B_i ≥ ρ_i cos β_i + (D − a_i) sin β_i.          (4)

*Choice.* Write (P_i,Q_i) = 2t_i(cos μ_i, sin μ_i) with μ_i = (ψ_ij+ψ_ik)/2 ∈ [−π/2,π/2], δ_i = (ψ_ij−ψ_ik)/2,
t_i = cos δ_i ∈ [0,1]. Let ν_i = arccos(κ t_i) ∈ (0,π/2] and α_i = ν_i + μ_i, β_i = ν_i − μ_i. Then

    cos α_i + cos β_i = 2 cos ν_i cos μ_i = κ P_i,
    sin α_i − sin β_i = 2 cos ν_i sin μ_i = κ Q_i,
    sin β_i = M_i − κ Q_i/2,   M_i := sin ν_i cos μ_i = cos μ_i √(1 − κ² cos² δ_i) ≥ 0.

*Sum.* Adding (4) over i and inserting these identities and (3):

    Σ_S ≥ κ Σ_i (ρ_i P_i + a_i Q_i) + D Σ_i sin β_i
        = κ ( Σ_{i<j} d^Z_ij + D E₂ ) + D ( Σ_i M_i − (κ/2)(E₂ − E₁) ),
    Σ_S − κ ( D + Σ_{i<j} d^Z_ij ) ≥ D ( Σ_i M_i − κ + (κ/2)(E₁+E₂) ).

Since √10·M_i = cos μ_i √(10 − 9cos²δ_i) = cos μ_i √(1 + 9 sin² δ_i) and √10·κ = 3:

**Proposition 3.2 [R].** In a book, Σ_S − κ Σ_T ≥ (D/√10)·Φ(ψ), where for ψ = (ψ₁₂,ψ₁₃,ψ₂₁,ψ₂₃,ψ₃₁,ψ₃₂)

    Φ(ψ) = Σ_{i=1}^{3} cos μ_i √(1 + 9 sin² δ_i) − 3 + (3/2) Σ_{i<j} | sin ψ_ij + sin ψ_ji |,
    μ_1 = (ψ₁₂+ψ₁₃)/2, δ_1 = (ψ₁₂−ψ₁₃)/2;  μ_2 = (ψ₂₁+ψ₂₃)/2, δ_2 = (ψ₂₁−ψ₂₃)/2;  μ_3 = (ψ₃₁+ψ₃₂)/2, δ_3 = (ψ₃₁−ψ₃₂)/2.

No relation between the angles is used except the sign conventions above, so it is enough to prove Φ ≥ 0 on
the whole cube. (In a real book more is true: ψ_ji = −ψ_ij for interior hubs, and two paths from v_i through
the same end of the spine have the same exit vector at v_i.)

[N] Check of the algebra: on 20 000 random books (all three hub types occurring, 26k/17k/17k pairs) the true
value of Σ_S − κΣ_T exceeded the bound D(ΣM_i − κ + κ(E₁+E₂)/2) every time (minimum excess 0.0058·D), and the
bound was ≥ 0 every time (`scratchpad/hull/calib_check.py`).

At W5(ℓ,ℓ/3) all ψ = 0, the calibrating vectors (3,±1)/√10 are the true directions u_k → v_i, and every
inequality is an equality.

### 3.3 Spec for interval verification

All angles in radians. H := π/2.

**(a) Inequality (I), three-angle form.** For θ = (θ₁,θ₂,θ₃) ∈ [−H,H]³:

    F(θ) := Σ_{1≤i<j≤3} cos((θ_i−θ_j)/2) · √(1 + 9 sin²((θ_i+θ_j)/2))  ≥  3.

*Half-ellipse form.* With z_i = (cos θ_i, √10 sin θ_i) (points of the ellipse x² + y²/10 = 1 with x ≥ 0):
|z_i+z_j| = 2cos((θ_i−θ_j)/2)·√(1+9sin²((θ_i+θ_j)/2)), so (I) ⇔ |z₁+z₂| + |z₁+z₃| + |z₂+z₃| ≥ 6.
*φ-form.* With φ_k = (θ_i+θ_j)/2 ({i,j,k} = {1,2,3}): Σ_k cos(φ_i−φ_j)·√(1+9 sin²φ_k) ≥ 3.
(I) is Φ ≥ 0 on the slice ψ₂₁ = −ψ₁₂, ψ₃₁ = −ψ₁₃, ψ₃₂ = −ψ₂₃, with θ₁ = ψ₁₂, θ₂ = −ψ₁₃, θ₃ = ψ₂₃.

**(b) Inequality (CL\*), six-angle form (covers every case: zero, one, two or three geodesics through a spine
end, at the u₁ end or the u₂ end).** For ψ = (ψ₁₂,ψ₁₃,ψ₂₁,ψ₂₃,ψ₃₁,ψ₃₂) ∈ [−H,H]⁶, with μ_i, δ_i as in
Proposition 3.2:

    Φ(ψ) = Σ_i cos μ_i √(1+9 sin² δ_i) − 3 + (3/2)( |sin ψ₁₂ + sin ψ₂₁| + |sin ψ₁₃ + sin ψ₃₁| + |sin ψ₂₃ + sin ψ₃₂| )  ≥  0.

Vector form: with w(ψ) = (cos ψ, sin ψ), N(x,y) = √(x²+10y²), and the bar denoting y ↦ −y:
cos μ_i √(1+9 sin²δ_i) = ½ N( w(ψ_ij) + w(−ψ_ik) ). Each |ε_ij| enters with weight 3/2 and each ψ enters exactly
one vertex term.
The structured sub-cases, if a smaller domain is preferred (each is a face or subset of the cube):
 - pair (i,j) interior: ψ_ji = −ψ_ij (ε_ij = 0);
 - pair (i,j) through u₂: sin ψ_ij + sin ψ_ji ≥ 0; through u₁: ≤ 0;
 - if (i,j) and (i,k) pass through the same end, ψ_ij = ψ_ik (then δ_i = 0 and the vertex term is cos ψ_ij).
Proving (CL\*) on the full cube makes the case distinction unnecessary.

**(c) Expected equality cases [N].**
 - (I): only θ = 0. Local form F = 3 + (1/8)·(4Σθ_i² + 5Σ_{i<j}θ_iθ_j)·… precisely
   F(θ) = 3 + ½Σ_iθ_i² + (5/8)·… see the exact second-order term: each pair contributes
   1 − (θ_i−θ_j)²/8 + (9/8)(θ_i+θ_j)² + O(4), so F = 3 + 2Σθ_i² + (5/2)Σ_{i<j}θ_iθ_j + O(|θ|⁴); the Hessian form
   2I·… has matrix (3/4)I + (5/4)J in the basis θ (J = all-ones), eigenvalues 3/4, 3/4, 9/2: positive definite.
   Outside the ball |θ| ≤ 0.3 the grid minimum (121³ points) is 3.0655.
 - (CL\*): ψ = 0 (not smooth there because of the absolute values), and six corners of the cube: for one
   vertex i and one sign s = ±1, ψ_ij = ψ_ik = −sH and the other four angles = +sH (all three vertex terms
   vanish, exactly one pair has |ε| = 2). These are collinear configurations (all points on the line of the
   spine), where the true inequality has room but the calibration has none.
   Local behaviour at such a corner: with deviations a₁,a₂ (vertex i), b₁,b₂, c₁,c₂ ≥ 0 from the corner values,
   Φ = ½(a₁+a₂+b₁+b₂+c₁+c₂) − (3/4)(b₂²+c₂²) + (3/4)(|a₁²−b₁²| + |a₂²−c₁²|) + higher order, where b₂, c₂ are the
   deviations of the two angles of the pair with |ε| = 2; so Φ grows linearly.
   Local behaviour at 0: for |ψ|_∞ ≤ r put θ = antisymmetric parts (θ₁ = (ψ₁₂−ψ₂₁)/2 etc.). Replacing ψ_ji by
   −ψ_ij changes one vertex term by at most L_r·|ε_ij|/cos r, where L_r = sup over the box of
   |∂/∂ψ [cos μ √(1+9 sin²δ)]| → 0 as r → 0 (it is ≤ (5r) for small r); so Φ(ψ) ≥ F(θ′) − 3 + (3/2 − L_r/cos r)Σ|ε_ij|
   for a nearby antisymmetric θ′, and (I) with its positive definite Hessian finishes.
 - Trivial region: Φ ≥ 0 whenever Σ|ε_ij| ≥ 2, because the vertex terms are ≥ 0.
 A scan with 6000 Powell starts for further near-zero minima is recorded in §3.4.

**(d) Status of the steps.** §3.1: [R] (C.4(a) + triangle inequality). §3.2: [R]; every line is an identity
or one of the Cauchy–Schwarz bounds (4); the optimality conditions for y_ij are the first-order conditions of a
convex function on [0,D]; a path between two pages always meets the spine (the pages are glued only along it),
either at an interior point or at an end. (CL\*): [N] only. So Theorem 5 is [D] until (CL\*) is certified or
proved; with a certificate it is a computer-assisted proof.

### 3.4 Numerical record for (I), (CL\*) and Theorem 5 [N]

- (I): 121³ grid, minimum 3.000000 at 0; ≥ 3.0655 outside |θ| ≤ 0.3.
- (CL\*): 3000 Nelder–Mead starts and 2·10⁶ random points in the cube: minimum 0 (at the corners described),
  no negative value; all 27 hub-type patterns with the structural constraints: minimum 0.
- Books (7 parameters): 400 starts, minimum 0.9486832980505134 at ρ_i = 1.5·D, a_i = D/2 (this is W5(ℓ,ℓ/3));
  other local minima ≥ 0.9488.
- Independent route (executor): Toyoda's theorem (arXiv:1907.09074, Thm 1.3: ≤ 5 points embed in a CAT(0)
  space iff all weighted quadruple inequalities hold) turns the five-point minimum into a semi-infinite
  program; its value is 3/√10 at W5 in 1000/1000 multistarts, active constraints the three inequalities at
  (t,s) = (½,½). Unweighted quadruple inequalities alone give only f_Q = 0.94461.

### 3.5 What an analytic proof of (I) has to do, and what failed

- [X] "One term at a time": |z_i+z_j| ≥ 2 holds when sin θ_i sin θ_j ≥ 0 ([R]: the square is
  2 + 9(s_i²+s_j²) + 2c_ic_j + 20s_is_j ≥ 4 + 7(s_i²+s_j²) + 20 s_is_j, using c_ic_j ≥ 1 − s_i² − s_j²), but
  fails for opposite signs; so the three-sign pattern (+,+,−) needs a joint argument.
- [X] Chord bound √(1+9x) ≥ 1+(√10−1)x: the resulting trigonometric inequality fails at θ = (−π/2,0,π/2)
  (1.529 < 1.586), although the true F there is 3.317. Also [X] √(1+9x) ≥ 1+2x (value 2.83 < 3).
- [X] Decoupled bounds |z_i+z_j| ≥ 2 + a(x_i²+x_j²) + b x_ix_j for one odd function x(θ): the constraints at
  (π/2,π/2), (π/2,−π/2) and positivity on (x,−x,0) are incompatible.
- Open: a proof by the pattern (+,+,−) with Minkowski for the two mixed terms; the bounds I tried hold with
  margins of 0.3% and were not pursued.

---

## 4. P2: is tripod × ℝ spectral outright?

1. [R] Equivalence (Cor. H3): tripod × ℝ is a price space over k ⇔ the single five-point metric N5 is a price
   over k. [D] ⇔ W5(ℓ,ℓ/3) is a price over k.
2. [D] Equivalence with a protocol statement: given Theorem 5, f*(K_{2,3};k) ≥ κ always, and f* = κ iff some
   point of Strassen's spectrum has R = κ. If W5 is the unique five-point CAT(0) minimiser up to scale ([N]:
   yes in every search; [C]), then **f*(K_{2,3};k) = 3/√10 ⇔ W5 is a (Strassen-)spectral metric over k ⇔
   tripod × ℝ is spectral over k.** So "tripod × ℝ is spectral" is exactly the statement that no asymptotic
   restriction protocol on K_{2,3} beats 3/√10: a tensor lower bound. Constructing the spectral point directly
   means proving that lower bound.
3. [R] No explicit functional can do it. Flattening ranks give cut pseudometrics; support functionals and
   quantum functionals give star metrics θ_u+θ_v on wires ([K], `ideas-ports.md` §4.1). All of these are
   ℓ₁-embeddable, and every ℓ₁ metric has R ≥ 1 on K_{2,3} (a cut separates at least as many supply as demand
   pairs, case check). W5 has R < 1, so it is not the wire metric of any of these points, nor a limit of
   positive multiples of them.
4. [X] Geometric means. Π φ_i^{θ_i} of spectral points is multiplicative and monotone but not subadditive on
   covers (two flattening ranks r₁, r₂: (r₁r₂)^{1/2} is 2√N on the two summands and N+1 on a sum). So one cannot
   mix a "tripod" functional and a "line" functional this way to get an ℓ₂ product.
5. [X] One-point extension [OA: EG Theorem 3.1]. Its proof gives: a new party p with prescribed distances λ_i to
   old parties exists if λ is an exposed minimal point of {λ : Σ u_iλ_i ≥ g_F(u) ∀u}, g_F(u) = sup of
   log F(T)/h over tensors of format 2^{hu_i}. A point on a new branch at distance ε from the wall is dominated
   coordinatewise by the Euclidean point at height ε over the same foot (√(|x|²+ε²) < √((x_⊥+ε)²+x_∥²)), so it
   is not minimal whenever the Euclidean extension exists. Extension theorems produce points that are as close
   as possible; a branch is a point that is far. The only known source of "far" points is the failure of an
   inequality (here: failure of contracting).
6. No obstruction specific to five parties was found: N5 and W5 satisfy every known necessary condition
   (they lie in a CAT(0) space; by Toyoda's theorem there are no further five-point CAT(0) conditions).
7. What a protocol of rate > 3/√10 would have to exploit [D]. By §2 and H2 it is a certificate of Contracting
   over its field: an identity that is false in buildings. Flattening ranks allow rate 1, and every identity
   obtained from the crossing identity (AN B.2) and random-point extension (AN A.8) is consistent with every
   CAT(0) target, hence with W5; such identities reach rate 3/√10 (Theorem 5 + duality) and not more. A better
   protocol needs a rerouting law of the kind AN derives from the contracting hypothesis (G.2), specialised
   to the K_{2,3} inside the rank-one Cayley graph of Mat₂(F₂). Executor's finite facts [R]: no exact
   restriction S ≥ T at equal bond dimension D ≥ 2 over any field (checked here: the v-cuts force A_v
   invertible; then (A_{u₁}⊗A_{u₂})S = M₁⊗M₂ with M_k on {u_k;v₁,v₂,v₃}, whose rank across {u₁} is at most its
   rank across {u₁,u₂}, while for T these are D and 1); no border restriction for demand (2,2,2,1) at bond
   dimension 2.

---

## 5. P3: consequences

Throughout k is a field; statements are per field.

**(i) The value of f*(K_{2,3};k).**
- [K] 3/4 (flow) ≤ f* ≤ 1 (cuts); f* > 3/4 (`ideas-ports.md` §4.5).
- [D] f* ≥ 3/√10 = 0.94868 unconditionally (Theorem 5 + Strassen duality). Tensor coding beats routing by the
  factor 4/√10 = 1.265 on five parties. Needs: Strassen 1988, AN thm_cn in the form C.4(a) (Lean), §3.1–3.2,
  and (CL\*) (uncertified).
- [R] f* ≤ 3/√10 if Contracting(k) fails (H2 + §2).
- [D] Hence **¬Contracting(k) ⇒ f*(K_{2,3};k) = 3/√10 exactly.**
- If Contracting(k) holds: f* ∈ [3/√10, 1], and f* > 3/√10 iff N5 is not a price over k (given uniqueness of
  the minimiser, [C]); Contracting alone does not decide it.

**(ii) Product closure of spectral spaces.**
- [R] If f*(K_{2,3};k) > 3/√10 then tripod × segment is not a price space over k although tripod and segment
  are: ℓ₂ products of spectral spaces are then not always spectral (the question [OA] HC Theorem 6.1 works
  around), and Contracting(k) holds.
- [R] If Contracting(k) fails, tripod × ℝ is a price space over k: the first product of a non-flat factor with
  a line that is forced; also (tripod × tripod) × segment locally [D, Remark 3] and (m-pod) × segment
  [D, Remark 4].
- [R] Conversely, product closure for the single pair (tripod, segment) ⇒ N5 is a price ⇒ f* ≤ 3/√10.

**(iii) Contracting / ports.**
- [R] rate > 3/√10 over k ⇒ N5 not a price over k ⇒ ρ₂, ρ₃ not prices over k ⇒ Contracting(k).
- [D] Contracting(k) ⇒ ports in char k (Theorem A: AN F.6 + [OA] HC 4.2; `../review-theoremAB.md`).
- In characteristic 0: ⇒ 3-SAT in 2^{O(v^{1−δ})} by [OA] IM 7.1 (Lean on their side, unrefereed), or by
  Theorem R (AN J.4 only; [D], `../review-theoremR.md`: no fatal gap, uniformity unverified).
- N5 joins M5 of Theorem B as a five-point test object; unlike M5 it comes with a protocol reading.

**(iv) Falsifiable statement.**

> **Under Weak ETH (3-SAT not in 2^{O(v^{1−δ})}), for every field k of characteristic 0, no asymptotic
> restriction protocol (exact, or border) from the six binary wires of K_{2,3} to the four demand wires
> v₁v₂, v₂v₃, v₁v₃, u₁u₂ has rate above r = 3/√10 = 0.948683…; and rates arbitrarily close to r are attained.**

Dependencies of the first half ("no protocol above r"), all the way down:
1. §2 (prices bound protocols): [R]; AN A.1, A.2.
2. Lemma H, H1, H2: [R], refereed; AN C.3, C.4(a),(f), `thm_alt_rank_price` (all Lean-backed, Anthropic).
3. Contracting over a characteristic-0 field ⇒ fast 3-SAT: either Theorem A ([D]; Anthropic F.6 Lean-backed +
   OpenAI HC 4.2, Lean exists on their side, unrefereed) + OpenAI IM 7.1 (their Lean, unrefereed); or
   Theorem R ([D]; Anthropic only; non-uniform version solid per the referee, uniform version has an
   unverified step).
Dependencies of the second half ("rates up to r are attained"): Strassen 1988; AN C.4(a) (Lean-backed);
§3.1–3.2 [R]; (CL\*) [N], awaiting the interval certificate. No hypothesis.
What is not claimed: nothing for finite sizes (the protocols of the second half are not explicit), nothing
for border protocols over small finite fields, nothing in characteristic p (there "rate > r" gives
Contracting(k) and ports in char p, with the consequences of `../review-c1.md`).

The best r I can prove outright for the first half is exactly 3/√10; it cannot be lowered by any argument that
uses only the CAT(0) property (Theorem 5).

---

## 6. Dead ends [X], with reasons

1. Single hub on [u₁,u₂] (CN at one point c_t, then |v_iv_j| ≤ |v_ic|+|cv_j|): fails, e.g. u₁ = v₁, u₂ = v₂,
   v₃ the apex of an equilateral triangle on [u₁,u₂] gives 4.73·D against the needed 4.22·D (true value 4D).
2. Projection relaxation |v_iv_j| ≤ ℓ_i+ℓ_j+|σ_i−σ_j| with A_i² ≥ ℓ_i²+σ_i²: mixes a flat lower bound with a
   tree-like upper bound; fails on tripods.
3. Unweighted quadruple inequalities (AN C.4(b)) + triangles: minimum f_Q = 0.94461 < 3/√10 (executor); not
   CAT(0)-realisable.
4. Symmetrisation by ℓ₂ products over the symmetry group of K_{2,3}: gives only
   Σ_T ≤ (√10/3)·√6·‖(|u_kv_i|)‖₂ [R], the quadratic mean in place of the sum. No averaging argument can give
   the ℓ₁ statement because the set of CAT(0) metrics is convex in squared distances only.
5. Per-quadrilateral inequality D/3 + d_ij ≤ (√10/6)·perimeter: false for degenerate quadrilaterals
   (u₁ = v_i, u₂ = v_j).
6. "Ellipse lemma" (for fixed |u₁v_i|+|u₂v_i| the perimeter of v₁v₂v₃ is largest at the co-vertices): false
   for thin ellipses.
7. Concavity of the book perimeter in (A_i,B_i): false (distance from the centre of the spine to a confocal
   ellipse is convex in the height).
8. Building structure, apartments, D.2 Steps 4–7 beyond "ρ₃ is a price": not needed for the hull lemma.
9. Reaching W5 from vertices of Mat_μ(F₂) alone: impossible (no collinear triples; rank is subadditive).

---

## 7. What I would do next

1. Certify (CL\*) (spec in §3.3), then referee §3.1–3.2. That makes "f*(K_{2,3}) ≥ 3/√10 over every field" a
   theorem with a computer-assisted proof, independent of both labs' conditional results.
2. Find the analytic proof of (I): three points on a half-ellipse of axis ratio √10, sum of pairwise sums ≥ 6.
3. Prove uniqueness of the minimiser (equality analysis of §3.2: equality forces ψ = 0, the calibration
   vectors to be the true directions, hence ρ_i = 3D/2, a_i = D/2), which turns §4 item 2 into [R].
4. Explicit protocols: Theorem 5 + duality promise restrictions of rate → 3/√10 built, in principle, from the
   crossing identity; the executor's search should target (rate, bond dimension) pairs below 0.9487 first
   (e.g. 16 → 13 or 14), where existence is guaranteed asymptotically, before spending time above it.
5. [C] Hull conjecture: under ¬Contracting the whole convex hull of the vertices L_a in the building of
   GL_{2μ}(F₂((t))) is a price space. Lemma H and Remarks 3–4 are the first cases; the method (flat squares +
   quadrilateral inequality as a lower bound on a side) should extend.
6. Other small instances: for K_{2,m} with demand = all pairs on the m-side plus the pair on the 2-side,
   (m-pod) × segment gives R = 2m/√(m²(m−1)²+4) [D]; compare with cuts and flow; find the instance with the
   largest forced gap between the cut bound and the tensor rate.
