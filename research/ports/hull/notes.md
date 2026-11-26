# Hull lemma, tripod × ℝ, and the K_{2,3} rate

Theory notes, 26 Nov 2026. Tags: [R] proved here (complete proof in these notes, from cited statements);
[D] derived, unreviewed sketch; [C] conjecture; [X] dead, with the reason; [K] quoted (pointer given);
[N] computed. "AN" = Anthropic's "VP ≠ VNP over every field" (line numbers refer to the pdftotext copy
`scratchpad/fm/paper.txt`). "OA" = OpenAI's unrefereed 24 Nov 2026 release (EG, HC, IM as in
`ideas-ports.md`); every use of OA is flagged [OA].

Notation. Parties u₁,u₂,v₁,v₂,v₃. S = the six wires u_iv_j, T = the wires v₁v₂, v₂v₃, v₁v₃, u₁u₂.
For a pseudometric d on the five parties, R(d) = Σ_S d / Σ_T d.
W5(ℓ,h): v_j at distance ℓ on the three legs of a tripod, at height 0; u_i at the hub at heights ±h, in
tripod × ℝ. R = 6√(ℓ²+h²)/(6ℓ+2h); minimum √(9/10) = 3/√10 = 0.948683… at h = ℓ/3.
ρ_μ(a,b) = √rk(a−b) on Mat_μ(F₂).

---

## 0. Summary of status

| # | Statement | Tag |
|---|---|---|
| 1 | **Hull lemma.** Any CAT(0) space containing the five-point set N5 (below) contains the solid "diamond" D ⊂ tripod × ℝ isometrically, hence every W5(ℓ,h). | [R] from AN C.4(b),(f) |
| 2 | N5 ⊂ (Mat₂(F₂), ρ₂) ⊂ (Mat₃(F₂), ρ₃); N5 = √(graph metric of K_{2,3}). | [R] (hand check + [N]) |
| 3 | N5 a price over k ⇒ every finite subset of D, in particular W5(ℓ,ℓ/3), is a price over k. | [R] from 1 + AN Prop. C.3, Def. A.4 |
| 4 | Contracting fails over k ⇒ W5(ℓ,ℓ/3) is a price over k. | [R] given AN D.2 Steps 1–7 (ρ₃ is a price); that step is inside AN's proof of thm_alt, stated in words in AN Remark D.3 |
| 5 | Any AN price d bounds the tensor rate: f*(K_{2,3};k) ≤ R(d). | [R] (three lines, §3) |
| 6 | Contracting fails over k ⇒ f*(K_{2,3};k) ≤ 3/√10. | [R] from 4, 5 |
| 7 | A protocol on K_{2,3} over ℚ of asymptotic rate > 3/√10 ⇒ contracting over ℚ ⇒ ports in characteristic 0 ⇒ 3-SAT in 2^{O(v^{1−δ})}. | [R] modulo Theorem A of `ideas-ports.md` (AN F.6 + [OA] HC 4.2) and [OA] IM 7.1 |

---

## 1. The hull lemma

### 1.1 The set N5

In Mat₂(F₂) put

    n = 0,  s = I = e₁₁+e₂₂,  t₁ = e₁₁,  t₂ = e₂₁+e₂₂,  t₃ = e₁₂+e₂₂.

[R] Ranks: t_i has rank 1 (each is a column times a row: e₁e₁ᵀ, e₂(e₁+e₂)ᵀ, (e₁+e₂)e₂ᵀ);
I − t₁ = e₂₂, I − t₂ = e₁₁+e₂₁ = (e₁+e₂)e₁ᵀ, I − t₃ = e₁₁+e₁₂ = e₁(e₁+e₂)ᵀ have rank 1;
t₁−t₂ = [[1,0],[1,1]], t₁−t₃ = [[1,1],[0,1]], t₂−t₃ = [[0,1],[1,0]] and I are invertible. Hence under ρ₂

    |n s| = |t_i t_j| = √2 (i ≠ j),    |n t_i| = |s t_i| = 1.

So **N5 is the square root of the graph metric of K_{2,3}**, with {n,s} the 2-side and {t₁,t₂,t₃} the 3-side:
supply edges have length 1, demand pairs length √2. (R(N5) = 6/(4√2) = 1.06; the gain comes from the hull.)

General form: n = a, s = a+W with rk W = 2, and t_i = a+R_i where R₁,R₂,R₃ are rank-one matrices with
rk(W−R_i) = 1 and rk(R_i−R_j) = 2. For W = I these are the R = uxᵀ with xᵀu = 1; there are six of them, forming
a hexagon under "difference of rank one", and the two triples of pairwise non-adjacent ones are the two
choices of {t₁,t₂,t₃}. In the Grassmannian picture (a ↦ graph Γ_a ⊂ F₂⁴): Γ₀ = P and Γ_I = P′ are
complementary planes, and t_i ↔ ⟨p_i, ψ(p_i)⟩ for a linear bijection ψ: P → P′; these three planes are pairwise
complementary. In the building of GL₄(F₂((t))) they are three pairwise opposite vertices of the link of the
vertex [O⁴], which is why a tripod appears.

N5 is not Euclidean [R]: in a Euclidean space, with the origin at the midpoint of n,s, the conditions give
t_i ⊥ (s−n), |t_i|² = 1/2 and t_i·t_j = −1/2, i.e. t_j = −t_i for all three pairs, impossible. Every four-point
subset of N5 is Euclidean (squares {n,s,t_i,t_j}; the pyramid {n,t₁,t₂,t₃}).

### 1.2 Statement

**Lemma H (hull lemma) [R].** Let Y be a CAT(0) space in the sense of AN §C.4 (complete; midpoints
satisfying the CN inequality) and let n, s, t₁, t₂, t₃ ∈ Y satisfy, for some a > 0,

    |n s| = |t_i t_j| = √2·a (i ≠ j),    |n t_i| = |s t_i| = a.

Let 𝕋 be the tripod with three legs of length a/√2 and hub o, and

    D = { (ξ,σ) ∈ 𝕋 × ℝ : |ξ o| + |σ| ≤ a/√2 }    (ℓ₂ product metric).

Then there is an isometric embedding Ψ: D → Y with Ψ(o, −a/√2) = n, Ψ(o, a/√2) = s and
Ψ(tip_i, 0) = t_i. In particular, for all ℓ, h ≥ 0 with ℓ + h ≤ a/√2 the five points
v_i = Ψ(point at distance ℓ on leg i, 0), u_± = Ψ(o, ±h) of Y have the metric W5(ℓ,h).

The statements about CAT(0) spaces used are exactly:
- AN Lemma C.4(a): uniqueness of the point at a given fraction of a pair (so geodesics are unique);
- AN Lemma C.4(f) (flat rectangles), quoted: "Suppose that |xy| = |uv| = δ and |xu| = |yv| = h, that both
  diagonals of the quadrilateral x, y, v, u have the squared length δ² + h², and that a ∈ [x,u] and b ∈ [y,v]
  have |xa| = sh and |yb| = th. Then |ab|² = δ² + h²(s−t)²."
Both are in AN's Lean (lem_toolkit). C.4(b) is not needed separately: the hypothesis of (f) is the equality
case of (b).

### 1.3 Proof

**Step 1 (solid squares; this is AN D.2 Step 8 for one square).** Let x, y, v, u ∈ Y have
|xy| = |yv| = |vu| = |ux| = a and |xv| = |yu| = √2·a. For s ∈ [0,1] let α(s) ∈ [x,u] and β(s) ∈ [y,v] be the
points at fraction s. By C.4(f) with δ = h = a,

    |α(s) β(t)|² = a²(1 + (s−t)²)   for all s, t.                                   (1)

Also |α(s)α(s′)| = |β(s)β(s′)| = a|s−s′|. Fix s ≠ s′ and consider x′ = α(s), u′ = β(s), y′ = α(s′),
v′ = β(s′). Then |x′y′| = |u′v′| = a|s−s′| =: δ′, |x′u′| = |y′v′| = a =: h′ by (1), and both diagonals
x′v′ = α(s)β(s′), y′u′ = α(s′)β(s) have squared length a²(1+(s−s′)²) = δ′² + h′² by (1). So C.4(f) applies to
x′, y′, v′, u′: with Φ(s,r) the point at fraction r on [α(s), β(s)],

    |Φ(s,r) Φ(s′,r′)|² = δ′² + h′²(r−r′)² = a²((s−s′)² + (r−r′)²).

For s = s′ the two points lie on one geodesic and the formula is trivial. Hence Φ: [0,1]² → Y is a times an
isometry, with Φ(0,0) = x, Φ(1,0) = u, Φ(0,1) = y, Φ(1,1) = v. Because geodesics in Y are unique, the image
Q(x,y,v,u) of Φ contains the geodesic between any two of its points (it is the Φ-image of the straight
segment). In particular the two diagonals [x,v] and [y,u] are the images of the diagonals of [0,1]², so they
cross at Φ(½,½), which is the midpoint of x,v and of y,u.

**Step 2 (one hub).** For i ≠ j apply Step 1 to (x,y,v,u) = (n, t_i, s, t_j): all sides are a, both diagonals
ns and t_it_j are √2·a. Let Q_ij be the solid square and c = mid(n,s). By Step 1, c = mid(t_i,t_j) for every
pair i ≠ j, and |c t_i| = |c n| = |c s| = a/√2.

**Step 3 (triangles).** Let Δ_i ⊂ Y be the union of the geodesics [t_i, p], p ∈ [n,s]. It depends only on i.
Inside the flat convex square Q_ij it is the half of the square on the t_i side of the diagonal [n,s], a flat
right isosceles triangle with hypotenuse [n,s], and Q_ij = Δ_i ∪ Δ_j. Let Δ̄ = {(τ,σ) : 0 ≤ τ, τ+|σ| ≤ a/√2}
⊂ ℝ². The parametrisation ψ_i: Δ̄ → Δ_i obtained from Q_ij sends (0,∓a/√2), (a/√2,0) to n, s, t_i and is an
isometry; the one obtained from Q_ik (k ≠ j) has the same three values, and an isometric map of a
non-degenerate Euclidean triangle into a uniquely geodesic space is determined by the images of its vertices
(a point of Δ̄ is determined by its distances to the three vertices, and its image has the same distances to
the images, all inside the flat triangle Δ_i). So ψ_i does not depend on the choice of j.

**Step 4 (gluing).** Define Ψ(ξ,σ) = ψ_i(|ξ o|, σ) for ξ on leg i; for ξ = o all three definitions give the
point of [n,s] at height σ. Take two points P = (ξ,σ), P′ = (ξ′,σ′) of D. If ξ, ξ′ lie on the same leg i, both
images lie in Δ_i and |Ψ(P)Ψ(P′)| is the Euclidean distance in Δ̄, which is the distance in 𝕋 × ℝ. If they lie
on legs i ≠ j, both images lie in the flat square Q_ij, in which Δ_i and Δ_j are the two halves; the distance
there is √((τ+τ′)² + (σ−σ′)²) with τ = |ξ o|, τ′ = |ξ′ o|, and τ+τ′ is the distance of ξ, ξ′ in 𝕋. So Ψ is
isometric. ∎

Remarks.
1. Nothing about buildings, apartments or the rest of Mat_μ(F₂) is used; neither are D.2 Steps 4–7 beyond the
   fact that ρ₃ is a price. The feared obstruction ("only vertices or discrete midpoints are forced; the
   u-points at height ±ℓ/3 are missing") does not occur: the u-points lie on the diagonal [0, I] of the flat
   squares, and the price space of AN Prop. C.3 is complete and geodesic.
2. The branching is forced by the metric of five points: three points pairwise at distance √2·a, all at
   distance a from n and from s. No three points of (Mat_μ(F₂), ρ_μ) are collinear
   (√rk(A+B) ≤ √(rk A + rk B) < √rk A + √rk B), so collinear triples appear only in the hull.
3. A second forced tripod in the same hull [R, same method; not needed]: with the hexagon
   P₁ = e₁₁, P₂ = e₁₁+e₁₂, P₃ = e₂₁+e₂₂, P₁′ = e₂₂, P₂′ = e₁₂+e₂₂, P₃′ = e₁₁+e₂₁ (consecutive differences of
   rank 1, all others of rank 2) the midpoints m₁ = mid(P₁,P₂), m₂ = mid(P₃,P₁′), m₃ = mid(P₂′,P₃′) are
   pairwise at distance 1 and at distance ½ from c. Proof of |m₁m₂| ≥ 1: the triangles (P₁,P₂,P₃) and
   (P₂,P₃,P₁′) are flat (halves of solid squares are not available here, but each has its hypotenuse through c
   and |P₂c| = |P₃c| = 1/√2, the equality case of CN), which gives |m₁P₃|² = |m₂P₂|² = 5/4, and the
   quadrilateral inequality C.4(b) for (m₁, m₂, P₃, P₂) reads 5/4 + 5/4 ≤ |m₁m₂|² + ¼ + 1 + ¼. This uses the
   flat-triangle lemma (equality in CN ⇒ flat triangle; [BH99, II.2.9]), which is not in AN's toolkit, so it
   is only [D]. It shows that locally at c the hull of ρ₂ is (tripod × tripod) × segment, as in the building.

### 1.4 From Lemma H to prices: the exact statements used (for the referee)

- **AN Definition A.4** (def_price; paper.txt l. 1121–1129): "A price on a finite set V is a limit of
  functions c·d_φ, where c ≥ 0 is a real number and φ is a spectral point on V. A function on the pairs of
  elements of an arbitrary set Y is a price if all its pull-backs to finite sets are prices. […] Pull-backs,
  nonnegative multiples and pointwise limits of prices are prices."
- **AN Proposition C.3** (prop_space; l. 1608–1622): "Every price on a set V is the pull-back of the metric of
  a price space." A price space is "a CAT(0) space whose metric is a price in the sense of Definition A.4"
  (l. 1600–1602), CAT(0) meaning complete with midpoints satisfying CN.

**Corollary H1 [R].** Let k be a field. If N5 (five parties, the metric of §1.1, any scale a) is a price over
k, then for every finite subset F of the diamond D the metric of F is a price over k. In particular W5(ℓ,h) is
a price over k for all ℓ, h ≥ 0.

Proof. By C.3 there are a price space Y over k and a map g: N5 → Y with |g(p)g(q)| equal to the N5 distance.
Lemma H applies to the five image points and gives the isometric Ψ: D → Y. The metric of Y is a price, so its
pull-back to the finite set Ψ(F) is a price (Def. A.4), and this pull-back is the metric of F. W5(ℓ,h) lies in
D after scaling (prices are closed under positive multiples). ∎

**Corollary H2 [R, given AN D.2].** If the contracting hypothesis fails over k, then N5 and all W5(ℓ,h) are
prices over k.

Proof. AN D.2, Steps 1–7 (l. 1714–1778), under "the contracting hypothesis fails", with μ = 3: there is a
price on Mat₃(F₂) with |a,a′|² = rk(a−a′). (Remark D.3, l. 1786–1789, says this in words: "Outside the
contracting case not every price is Euclidean, because for μ ≥ 3 the price √rk(a−a′) of the proof above is
not.") The map Mat₂(F₂) → Mat₃(F₂), a ↦ diag(a,0), preserves ranks of differences, so ρ₂ and its restriction
N5 are prices (pull-back). Apply H1. ∎

Caveat for the referee: "ρ₃ is a price when contracting fails" is a step of the proof of thm_alt, not a
separately named Lean theorem as far as the paper's table shows. The logical form used is exactly: failure of
"∃ μ ≥ 2 ∃ s, 1 ≤ s, s² < μ: D(μ) ≤ s·D(1) for all prices on Mat_μ(F₂)" at μ = 3.

---
