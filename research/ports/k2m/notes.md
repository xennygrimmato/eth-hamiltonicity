# K_{2,m}: tensor rate, pods, books, and an analytic proof of (CL*)

Theory notes, 26 Nov 2026. Companion to `../note-k23-rate.md` ("the note") and `../hull/notes.md` ("hull notes").

Tags: **[R]** proved here, complete proof in this file from the cited statements; **[D]** derived, unreviewed or resting
on an uncertified step; **[N]** numerical; **[C]** conjecture; **[X]** dead, with the reason; **[AN]** quoted from
Anthropic's paper as in the note §0.3 (C.3 = `prop_space`, C.4(a),(f) = `lem_toolkit`, `thm_alt_rank_price`).

Scripts (this folder; all [N] except `fqpods.py`, which is exact integer arithmetic):
`books.py`, `wscan.py` (book minimisation), `calib_check.py` (calibration identities), `clstar_analytic.py` (steps of
Theorem D), `fqpods.py` (rank tables over F_q), `refined.py`, `refined_m.py`, `cutregime.py` (weights above the
proved range), `twoapex.py`, `scan2.py` (other networks), `three_angle.py` (sharp constant in (I)).

---

## 0. Summary of status

Network K_{2,m}(w): parties u₁, u₂, v₁, …, v_m. Supply S: the 2m binary wires u_k v_i. Demand T_w: the C(m,2) wires
v_i v_j at rate f and the wire u₁u₂ at rate w·f (w > 0 real; w = 1 is the uniform instance). For a pseudometric d:

    Σ_S = Σ_{k,i} d(u_k,v_i),   Σ_vv = Σ_{i<j} d(v_i,v_j),   D = d(u₁,u₂),   R_w(d) = Σ_S / (Σ_vv + w·D).

    R_m(w) := 2m / √(m²(m−1)² + 4w²),        κ(w) := R_3(w) = 3/√(9+w²),   κ(1) = 3/√10.

| # | Statement | Tag |
|---|---|---|
| 1 | **Theorem D (analytic (CL\*)).** Φ_w ≥ 0 on [−1,1]⁶ for 0 < w ≤ 1; w = 1 is (CL\*) = (3.5) of the note. Six lines; no computer. | [R] (§3.3); refereed (`../review-k2m.md`); Lean: `clstar_weighted` in `PortsLean/CLStar.lean` |
| 2 | Weighted five-point theorem: Σ_S ≥ κ(w)(Σ_vv + wD) for five points of a CAT(0) space, 0 < w ≤ 1. | [R] given [AN] C.4(a) (§3.4) |
| 3 | **Theorem B.** For m ≥ 3, 0 < w ≤ m(m−1)/6 and m+2 points of a CAT(0) space: Σ_S ≥ R_m(w)(Σ_vv + wD), with equality at W_{m+2}(ℓ, 2wℓ/(m(m−1))). | [R] (§3.5: Theorem 5_{w′} on every five-point subset, averaged over triples); arithmetic in Lean |
| 4 | Lemma P: explicit rank-one idempotents in Mat₂(F_q), q = 2^r, giving √r·√(graph metric of K_{2,q+1}) inside (Mat_{2r}(F₂), ρ_{2r}); maximality m ≤ 2^{⌊μ/2⌋}+1 in Mat_μ(F₂). | [R] (§2.1–2.2); rank tables machine-checked for r ≤ 6 (`fqpods.py`) |
| 5 | Lemma H_m: m+2 points with the metric a·√(graph metric of K_{2,m}) in a CAT(0) space span an isometric diamond of (m-pod) × ℝ. | [R] from [AN] C.4(a),(f) (§2.3) |
| 6 | **Theorem A.** ¬Contracting(k) ⇒ every finite subset of (m-pod) × ℝ is a price over k, for every m; hence f*(K_{2,m}(w); k) ≤ R_m(w) for every w > 0. | [R] given [AN] `thm_alt_rank_price`, C.3 (§2.4) |
| 7 | **Theorem K_m.** f*(K_{2,m}(w); k) ≥ R_m(w) for every field k, m ≥ 3, 0 < w ≤ m(m−1)/6; equality if Contracting(k) fails. Flow value 2m/(m(m−1)+2w) < R_m(w) < cut bound. | [R] = 3 + 6 + Strassen (§4) |
| 8 | The direct m-page calibration cancels all lengths, but its scalar inequality is false for even m ≥ 4 (all w) and for odd m ≥ 5 at larger w. | [X] (§3.6), explicit counterexample |
| 9 | Book principle: for two-apex networks the minimum over CAT(0) configurations equals the minimum over m-page books. | [R] modulo Reshetnyak gluing [BH99 II.11.1] (§3.1, §6) |
| 10 | Weights above the proved range, refined calibration, cut regime. | §5 ([R] parts, [N], [C], certificate spec) |
| 11 | Which other networks are pinned. | §6 |
| 12 | Three-angle inequality (I) with the sharp constant 8. | [R] (§7) |

---

## 1. Setup

**Rates.** ⟨N⟩_{xy} is the wire of dimension N between x and y. f*(K_{2,m}(w); k) is the supremum of f such that
there are restrictions over k

    ⊗_{i<j} ⟨2^{a_n}⟩_{v_iv_j} ⊗ ⟨2^{b_n}⟩_{u₁u₂}  ≤  S^{⊗n},      a_n/n → f,   b_n/n → w·f.

Put G(w) := min over AN prices d on the m+2 parties (with Σ_vv + wD > 0) of R_w(d). The claim is

    f*(K_{2,m}(w); k) = G(w)      for every real w > 0.                                                   (1.1)

*Upper bound, every real w.* Let d be an AN price. As in the note §1.2(b) (monotonicity and multiplicativity of
spectral points, F(⟨N⟩_{xy}) = N^{d_F(x,y)}, linearity in d, closure under multiples and limits), a restriction as
above gives a_nΣ_vv(d) + b_nD(d) ≤ nΣ_S(d). Divide by n and let n → ∞: f·(Σ_vv + wD) ≤ Σ_S. So f* ≤ G(w).

*Lower bound, rational w = p/q.* Apply Strassen's theorem to T_{p,q} := ⊗_{i<j}⟨2^q⟩_{v_iv_j} ⊗ ⟨2^p⟩_{u₁u₂}, for which
log₂F(T_{p,q}) = q(Σ_vv + wD)(d_F): T_{p,q}^{⊗a} ≤ S^{⊗(b+o(b))} iff a·q·(Σ_vv + wD)(d_F) ≤ b·Σ_S(d_F) for all F ∈ 𝒳.
The rate of such a protocol is f = aq/b on the wires v_iv_j and ap/b = wf on u₁u₂, so the supremum of achievable f is
inf_{F∈𝒳} R_w(d_F), and this equals G(w) because every F ∈ 𝒳 is an AN spectral point (note §1.2(a)) and by the upper
bound. The passage from rational a/b to sequences is as in the note §1.1.

*Lower bound, irrational w.* f*(w) is non-increasing in w (a protocol for weight w′ ≥ w is one for weight w after
discarding part of the wire u₁u₂). 1/G(w) = max over prices with Σ_S = 1 of (Σ_vv + wD) is a maximum of affine
functions of w, finite because Σ_vv ≤ ((m−1)/2)Σ_S and D ≤ Σ_S/m by the triangle inequality; so it is convex and
finite, hence continuous, and G is continuous. For rational w′ ↓ w: f*(w) ≥ f*(w′) = G(w′) → G(w). (For Theorem K_m
one may take the w′ inside the range w′ ≤ m(m−1)/6, since that bound is rational; this is not needed, because
Theorem B bounds G(w) at every real w of the range.)

So a lower bound may be proved for all AN prices, and an upper bound needs one AN price.

**CAT(0) input.** By [AN] C.3 every price on the m+2 parties is the pull-back of the metric of a price space Y, which
is CAT(0) in the sense of [AN] §C.4 (C.3 is a statement about the price space and has no restriction on the number of
parties). So every price is the metric of m+2 points (possibly coinciding) of a CAT(0) space, in which C.4(a) holds.

**The chain of bounds** (any supply graph G with capacities c, demand graph H with weights r, same parties):

    f_flow ≤ f_CAT(0) ≤ f* ≤ f_cut,                                                                       (1.2)

where each is the minimum of Σ_G c·d / Σ_H r·d over a class of pseudometrics: all pseudometrics (LP dual of maximum
concurrent flow); finite subsets of CAT(0) spaces; AN prices over k; cut pseudometrics (= ℓ₁ metrics). The
inclusions are: cut metrics are prices (flattening ranks); prices are CAT(0) (C.3); CAT(0) metrics are metrics.

---

## 2. Upper bound: (m-pod) × segment is forced when contracting fails

### 2.1 Lemma P (the matrices) [R]

Let q = 2^r, F_q the field with q elements, P¹ = P¹(F_q) = {[1:a] : a ∈ F_q} ∪ {∞ = [0:1]} (q+1 points).

*Rank-one idempotents.* A matrix t ∈ Mat₂(F_q) has rk t = 1 and rk(I−t) = 1 iff t is idempotent of rank one:
t = u xᵀ with xᵀu = 1 (if t = uxᵀ then det(I − t) = 1 − xᵀu, so I − t is singular iff xᵀu = 1, and then t² = t).
Such a t is determined by its image line im t = ⟨u⟩ and its kernel line ker t = x^⊥, which are different points of
P¹; conversely every ordered pair of different points (p, p′) is (im t, ker t) for exactly one idempotent t_{p,p′}.
There are (q+1)q of them.

*Differences.* For two rank-one idempotents t = uxᵀ, t′ = u′x′ᵀ:

    t − t′ = [u u′] · diag(1, −1) · [x x′]ᵀ,

so t − t′ is invertible iff u, u′ are independent and x, x′ are independent, i.e. iff
**im t ≠ im t′ and ker t ≠ ker t′.**

*The family.* Let π be a permutation of P¹ without fixed points and t_p := t_{p,π(p)}. Then the q+1 matrices t_p
have pairwise different images and pairwise different kernels. Explicitly, for the derangement
π(0) = ∞, π(∞) = 1, π(1) = 0, π(a) = a+1 for a ∈ F_q∖{0,1} (rows of each matrix separated by ";"):

    t_0 = [1 0; 0 0],   t_∞ = [0 0; 1 1],   t_1 = [0 1; 0 1],   t_a = [a+1  1; a²+a  a]   (a ∈ F_q ∖ {0,1}).

(Check: for image [1:a], kernel [1:b], b ≠ a, the idempotent is (a+b)⁻¹·[b 1; ab a]; for kernel ∞ it is [1 0; a 0];
for image ∞ and kernel [1:b] it is [0 0; b 1]. Each has trace 1 and determinant 0.) For q = 2 these are exactly
t₁ = e₁₁, t₂ = e₂₁+e₂₂, t₃ = e₁₂+e₂₂ of the note §2.1.

> **Lemma P.** In Mat₂(F_q): rk t_p = rk(I − t_p) = 1 for all p ∈ P¹, rk(t_p − t_{p′}) = 2 for p ≠ p′, and rk I = 2.

*Push-forward to F₂.* Fix an F₂-basis of F_q and let ι: F_q → Mat_r(F₂) be the regular representation (ι(a) = matrix
of x ↦ ax). Apply ι entrywise: ι₂: Mat₂(F_q) → Mat_{2r}(F₂). Then ι₂(A) is the matrix of the F₂-linear map
x ↦ Ax on F_q² ≅ F₂^{2r}. Its image is the F_q-subspace A·F_q², of F_q-dimension rk_{F_q}A, hence of F₂-dimension
r·rk_{F_q}A:

    rk_{F₂} ι₂(A) = r · rk_{F_q}(A),      and ι₂ is additive, so   ρ_{2r}(ι₂A, ι₂B) = √r · √rk_{F_q}(A − B).

> **Corollary P.** For m ≤ 2^r + 1 the m+2 matrices 0, ι₂(I) = I_{2r}, ι₂(t_p) (any m of the points p) form, under
> ρ_{2r} = √rank, the metric √r · √(graph metric of K_{2,m}) with {0, I} the 2-side:
> |0 I| = |t_p t_{p′}| = √(2r), |0 t_p| = |I t_p| = √r. The same holds in Mat_μ(F₂) for every μ ≥ 2r (a ↦ diag(a,0)
> preserves ranks).

Machine check (exact integer arithmetic, `fqpods.py`): for r = 1,…,6 the explicit family above and a second
family (cyclic derangement) satisfy all rank conditions over F₂ in Mat_{2r}(F₂) (m = 3, 5, 9, 17, 33, 65);
rk_{F₂}ι₂(A) = r·rk_{F_q}(A) on 2000 random A for each r ≤ 5; for r ≤ 2 an exhaustive search finds no further admissible
point in Mat₂(F_q).

### 2.2 Lemma P′ (maximality) [R]

> **Lemma P′.** Let a₀, a₁, t₁, …, t_m ∈ Mat_μ(F₂) carry, under ρ_μ, the metric c·√(graph metric of K_{2,m}) with
> {a₀,a₁} the 2-side. Then c² = k is an integer with 2k ≤ μ and m ≤ 2^k + 1. Hence the largest m for which
> (Mat_μ(F₂), ρ_μ) contains a scaled copy of √(graph metric of K_{2,m}) is exactly 2^{⌊μ/2⌋} + 1.

*Proof.* Translate so that a₀ = 0 and put W = a₁. The hypotheses are rk W = 2k, rk t_i = rk(W − t_i) = k,
rk(t_i − t_j) = 2k (i ≠ j), with k = c². Put Ω = im W (dimension 2k ≤ μ) and U_i = im t_i (dimension k).
Since W = t_i + (W − t_i), Ω ⊂ U_i + im(W − t_i), and the dimensions k + k = 2k force equality; so U_i ⊂ Ω.
For i ≠ j, im(t_i − t_j) ⊂ U_i + U_j ⊂ Ω has dimension 2k, so U_i ⊕ U_j = Ω. Thus the sets U_i ∖ {0} are pairwise
disjoint subsets of Ω ∖ {0}: m(2^k − 1) ≤ 2^{2k} − 1, i.e. m ≤ 2^k + 1. Corollary P with r = k = ⌊μ/2⌋ attains it. ∎

So the F_{2^r}-structure is not a convenience: the images im t_i form a partial k-spread of F₂^{2k}, and a full spread
(2^k+1 members) is what the Desarguesian construction gives. For K_{2,m} one needs k ≥ ⌈log₂(m−1)⌉, i.e.
μ ≥ 2⌈log₂(m−1)⌉ (m = 3: μ = 2; m = 4, 5: μ = 4; m ≤ 9: μ = 6).

### 2.3 Lemma H_m (the hull) [R]

Let 𝕋_m be the m-pod: m segments ("legs") of length a/√2 glued at one end o ("hub"), with the path metric. The
diamond is D_m = {(ξ,σ) ∈ 𝕋_m × ℝ : |ξo| + |σ| ≤ a/√2} with the ℓ₂ product metric.

> **Lemma H_m.** Let Y be CAT(0) in the sense of [AN] §C.4, m ≥ 2, and let n, s, t₁, …, t_m ∈ Y satisfy
> |ns| = |t_it_j| = √2·a (i ≠ j) and |nt_i| = |st_i| = a. Then there is an isometric embedding Ψ: D_m → Y with
> Ψ(o, −a/√2) = n, Ψ(o, a/√2) = s and Ψ(tip of leg i, 0) = t_i.

The proof is that of Lemma H (note §2.2). We list which statement is used for which points.

*Step 1 (one solid square for each unordered pair {i,j}).* The quadruple (x,y,v,u) = (n, t_i, s, t_j) has
|xy| = |yv| = |vu| = |ux| = a and |xv| = |yu| = √2·a. Step 1 of Lemma H (two applications of C.4(f), uniqueness of
geodesics from C.4(a)) uses these four points only and gives a map Φ_ij: [0,1]² → Y which is a times an isometry,
with Φ_ij(0,0) = n, Φ_ij(1,1) = s, Φ_ij(0,1) = t_i, Φ_ij(1,0) = t_j. Its image Q_ij contains the geodesic between any
two of its points (the image of a straight segment is a geodesic, and geodesics are unique).
There are C(m,2) such squares; nothing relates different pairs at this stage.

*Step 2 (one hub).* Let c be the midpoint of n and s (unique by C.4(a)). In Q_ij the two diagonals are the images of
the diagonals of [0,1]², which cross at Φ_ij(½,½); so Φ_ij(½,½) = c is also the midpoint of t_i and t_j. This holds
for every pair, with the same c, because every Q_ij contains the geodesic [n,s]. So |ct_i| = |cn| = |cs| = a/√2.

*Step 3 (one flat triangle for each i).* Put Δ_i = ∪_{p ∈ [n,s]} [t_i, p]. It is defined by geodesics of Y and does not
depend on a second index. For each j ≠ i, Δ_i ⊂ Q_ij is the image of the half of the square on the t_i side of the
diagonal [n,s], and Q_ij = Δ_i ∪ Δ_j. Let Δ̄ = {(τ,σ) ∈ ℝ² : τ ≥ 0, τ + |σ| ≤ a/√2}. Restricting Φ_ij gives an
isometry ψ_i^{(j)}: Δ̄ → Δ_i with (0, ∓a/√2) ↦ n, s and (a/√2, 0) ↦ t_i. Claim: ψ_i^{(j)} does not depend on j.
Both ψ_i^{(j)} and ψ_i^{(j′)} map the side {τ = 0} isometrically onto the geodesic [n,s] with the same end points,
so they agree there. A point z ∈ Δ̄ lies on the segment from (a/√2, 0) to a point p̄ of that side; both maps send
this segment isometrically onto the unique geodesic [t_i, p] with p the common image of p̄; so they agree at z.
Write ψ_i for the common map.

*Step 4 (gluing: any two points lie in a common solid square).* Define Ψ(ξ,σ) = ψ_i(|ξo|, σ) for ξ on leg i; for
ξ = o all ψ_i agree (Step 3). Let P = (ξ,σ), P′ = (ξ′,σ′) ∈ D_m with ξ on leg i, ξ′ on leg j, and τ = |ξo|,
τ′ = |ξ′o|.
- If i ≠ j: Ψ(P) ∈ Δ_i and Ψ(P′) ∈ Δ_j both lie in Q_ij, and in the Euclidean coordinates of Q_ij (τ counted
  positively on the Δ_i side and negatively on the Δ_j side of the diagonal) they are (τ,σ) and (−τ′,σ′). Φ_ij is
  an isometry up to the factor already absorbed, so |Ψ(P)Ψ(P′)|² = (τ+τ′)² + (σ−σ′)², and τ+τ′ = |ξξ′| in 𝕋_m.
- If i = j: both lie in the flat triangle Δ_i, and |Ψ(P)Ψ(P′)|² = (τ−τ′)² + (σ−σ′)².
In both cases this is the distance in 𝕋_m × ℝ. An isometric embedding is a condition on pairs of points, so no
condition involving three legs has to be checked. ∎

Only C.4(a) and C.4(f) are used, as in Lemma H. For m = 3 this is Lemma H.

### 2.4 Theorem A [R given AN]

W_{m+2}(ℓ,h): v_j at distance ℓ from the hub on leg j, at height 0; u₁, u₂ at the hub at heights ∓h:

    |u_kv_j| = √(ℓ²+h²),  |v_iv_j| = 2ℓ,  |u₁u₂| = 2h;   Σ_S = 2m√(ℓ²+h²),  Σ_vv = m(m−1)ℓ,  D = 2h.

By Cauchy–Schwarz, m(m−1)ℓ + 2wh ≤ √(m²(m−1)²+4w²)·√(ℓ²+h²), with equality iff h/ℓ = 2w/(m(m−1)). Hence

    min_{ℓ,h} R_w(W_{m+2}(ℓ,h)) = R_m(w) = 2m/√(m²(m−1)²+4w²),   attained exactly at h = 2wℓ/(m(m−1)).       (2.1)

This confirms the formula 2m/√(m²(m−1)²+4) of hull notes §7.6 (w = 1) [R]. W_{m+2}(ℓ,h) ⊂ D_m iff max(ℓ,h) ≤ a/√2.

> **Theorem A.** Suppose Contracting(k) fails. Then for every m ≥ 2:
> 1. the metric √(graph metric of K_{2,m}) is a price over k;
> 2. every finite subset of 𝕋_{m,∞} × ℝ (the m-pod with infinite legs, times the line) is a price over k;
> 3. f*(K_{2,m}(w); k) ≤ R_m(w) for every w > 0 (also for border protocols over infinite k with approximation
>    degree 2^{o(n)}, as in the note §1.2(c)).

*Proof.* Choose r with 2^r + 1 ≥ m and μ = max(2r, 3). `thm_alt_rank_price` gives the price ρ_μ on Mat_μ(F₂).
Pull back along the m+2 matrices of Corollary P and rescale by 1/√r: item 1. By C.3 there are a price space Y
and m+2 points of Y with that metric; Lemma H_m (a = 1) embeds the diamond D_m; the metric of Y is a price, so
its pull-back to any finite subset of the diamond is a price. A finite subset of 𝕋_{m,∞} × ℝ fits into a diamond
after a translation along ℝ and a scaling: item 2. Item 3: W_{m+2}(ℓ, 2wℓ/(m(m−1))) is a price by item 2; apply
(1.1) and (2.1). ∎

Remark. Item 2 for m implies it for all m′ ≤ m. So under ¬Contracting(k) every finite subset of (finite pod) × ℝ
is a price.

---

## 3. Lower bound

### 3.1 Reduction to books (m pages) [R]

Let u₁, u₂, v₁, …, v_m be points of a CAT(0) space Y; D = |u₁u₂|, A_i = |u₁v_i|, B_i = |u₂v_i|. If D > 0 let c_t be the
point at fraction t of [u₁,u₂]. By C.4(a), |v_ic_t|² ≤ (1−t)A_i² + tB_i² − t(1−t)D² =: h_i(t)², so

    |v_iv_j| ≤ min_{t∈[0,1]} (h_i(t) + h_j(t)) =: d^Z_ij     for all i ≠ j.                                 (3.1)

This is §3.1 of the note, applied to each pair; m plays no role. In coordinates: page i is the half-plane
{(ρ,a) : ρ ≥ 0}, u₁ = (0,0), u₂ = (0,D), v_i = (ρ_i,a_i) with A_i = |(ρ_i,a_i)|, B_i = |(ρ_i,a_i−D)|,
f_i(y) = |v_i − (0,y)| = h_i(y/D), and d^Z_ij = min_{y∈[0,D]} (f_i(y)+f_j(y)).

Since Σ_S and D are unchanged and Σ_vv ≤ Σ_{i<j} d^Z_ij, a lower bound for R_w needs only the 2m+1 numbers
D, ρ_i, a_i. (Conversely the book — m flat triangles glued along the spine — is CAT(0) by Reshetnyak's gluing theorem
[BH99, II.11.1] and realises equality in (3.1); so min over CAT(0) configurations = min over books. This converse
is used only for numerics and for §6, not for any lower bound.)

### 3.2 Calibration with a general constant (m pages) [R]

*Hubs and exit vectors (as in the note §3.2).* For i ≠ j let y_ij = y_ji ∈ [0,D] minimise f_i + f_j, and let
e_ij = (c_ij, σ_ij), c_ij = √(1−σ_ij²) ≥ 0, be the unit vector of v_i − (0,y_ij) in page i (if v_i = (0,y_ij), any σ_ij
in the subdifferential [−1,1] for which (3.2) below holds). Then f_i(y_ij) = ρ_ic_ij + (a_i − y_ij)σ_ij and, with
ε_ij := σ_ij + σ_ji,

    y_ij ∈ (0,D): ε_ij = 0;     y_ij = D: ε_ij ≥ 0;     y_ij = 0: ε_ij ≤ 0.                                 (3.2)

Put E₂ = Σ_{pairs with y_ij=D} ε_ij ≥ 0, E₁ = Σ_{pairs with y_ij=0} |ε_ij| ≥ 0, E := E₁ + E₂ = Σ_{i<j}|ε_ij|, and
V_i = (P_i, Q_i) := Σ_{j≠i} e_ij (so P_i ≥ 0, |V_i| ≤ m−1, Σ_iQ_i = Σ_{i<j}ε_ij = E₂ − E₁). Since y_ijε_ij = Dε_ij[y_ij = D],

    Σ_{i<j} d^Z_ij = Σ_{i<j} (ρ_ic_ij + ρ_jc_ji + a_iσ_ij + a_jσ_ji − y_ijε_ij) = Σ_i (ρ_iP_i + a_iQ_i) − D·E₂.     (3.3)

*Supply.* For any angles α_i, β_i (Cauchy–Schwarz with the unit vectors (cos α_i, sin α_i), (cos β_i, −sin β_i)):

    A_i ≥ ρ_i cos α_i + a_i sin α_i,      B_i ≥ ρ_i cos β_i + (D − a_i) sin β_i.                           (3.4)

*Choice of angles for a constant λ with 0 < λ < 2/(m−1).* Write V_i = |V_i|(cos μ_i, sin μ_i), μ_i ∈ [−π/2, π/2]
(μ_i = 0 if V_i = 0). Since λ|V_i|/2 < 1 we may put ν_i = arccos(λ|V_i|/2) ∈ (0, π/2], α_i = ν_i + μ_i,
β_i = ν_i − μ_i. Then

    cos α_i + cos β_i = 2 cos ν_i cos μ_i = λP_i,
    sin α_i − sin β_i = 2 cos ν_i sin μ_i = λQ_i,
    sin β_i = sin ν_i cos μ_i − cos ν_i sin μ_i = M_i − λQ_i/2,     M_i := cos μ_i·√(1 − λ²|V_i|²/4) ≥ 0.

*Sum.* Adding (3.4) over i and inserting the three identities and (3.3):

    Σ_S ≥ Σ_i [ρ_i·λP_i + a_i·λQ_i + D sin β_i] = λ(Σ_{i<j}d^Z_ij + D E₂) + D Σ_i M_i − (λD/2)(E₂ − E₁).

> **Proposition C (m pages, constant λ < 2/(m−1), weight w).** For every book,
>
>     Σ_S − λ(Σ_{i<j} d^Z_ij + w·D) ≥ D · Br,      Br := Σ_i M_i − λw + (λ/2) Σ_{i<j} |ε_ij|,
>     M_i = cos μ_i·√(1 − λ²|V_i|²/4).
>
> All lengths ρ_i, a_i have cancelled; Br depends only on the m(m−1) exit vectors and on λ, w.

*The case m = 3, λ = κ(w) = 3/√(9+w²).* With the two exit angles ψ_ij, ψ_ik at v_i, μ_i = (ψ_ij+ψ_ik)/2 and
δ_i = (ψ_ij−ψ_ik)/2 we have V_i = 2cos δ_i(cos μ_i, sin μ_i), |V_i|² = 4cos²δ_i, and

    M_i = cos μ_i √(1 − 9cos²δ_i/(9+w²)) = cos μ_i √(w² + 9 sin²δ_i)/√(9+w²) = (κ(w)·w/3)·cos μ_i √(1 + (9/w²) sin²δ_i).

So Br = (κ(w)w/3)·Φ_w, where (using c_ij+c_ik = 2cos μ_i cos δ_i, σ_ij−σ_ik = 2cos μ_i sin δ_i, cos μ_i ≥ 0)

    Φ_w := Σ_i cos μ_i √(1 + (9/w²) sin²δ_i) − 3 + (3/(2w)) Σ_{i<j}|sin ψ_ij + sin ψ_ji|
         = ½ Σ_i √((c_ij+c_ik)² + (1+9/w²)(σ_ij−σ_ik)²) − 3 + (3/(2w)) Σ_{i<j}|σ_ij+σ_ji|.                    (3.5_w)

> **Proposition C₃ (weighted Prop. 3.2).** For every three-page book and every w > 0,
> Σ_S − κ(w)(Σ_{i<j}d^Z_ij + wD) ≥ (κ(w)w/3)·D·Φ_w(σ), σ ∈ [−1,1]⁶ the six exit sines.

For w = 1 this is Prop. 3.2 of the note ((κ/3)·Φ = Φ/√10) and (3.5₁) is (3.5) there.
[N] `calib_check.py`: on 20 000 random books for each of (m,w) ∈ {(3,0.2),(3,0.5),(3,1),(4,0.5),(4,1),(4,2),(5,1),
(5,3.3),(6,1),(6,5)} the true left side exceeded D·Br every time.

### 3.3 Theorem D: (CL\*) analytically [R]

> **Theorem D.** For σ ∈ [−1,1]⁶ (σ = (σ₁₂,σ₁₃,σ₂₁,σ₂₃,σ₃₁,σ₃₂), c = √(1−σ²)) and 0 < w ≤ 1: Φ_w(σ) ≥ 0.
> For w = 1 this is (CL\*).

*Proof.* Let m := max of the six |σ|, V := Σ_i |σ_ij − σ_ik| (three vertex differences), E := Σ_{i<j} |σ_ij + σ_ji|
(three pair sums), K := 1 + 9/w².

(1) *Hexagon lemma: V + E ≥ 2m.* The six variables form a hexagon σ₁₂ — σ₁₃ — σ₃₁ — σ₃₂ — σ₂₃ — σ₂₁ — σ₁₂ whose
edges are alternately a vertex (the two exits of v_i) and a pair (σ_ij, σ_ji). Going once around,

    2σ₁₂ = (σ₁₂−σ₁₃) + (σ₁₃+σ₃₁) − (σ₃₁−σ₃₂) − (σ₃₂+σ₂₃) + (σ₂₃−σ₂₁) + (σ₂₁+σ₁₂),

and the six brackets are exactly the three vertex differences and the three pair sums. So 2|σ₁₂| ≤ V + E; by the
symmetry of the hexagon the same holds for each of the six variables.

(2) Every c_ij ≥ √(1−m²), so Σ_i (c_ij + c_ik) ≥ 6√(1−m²).

(3) *Cauchy–Schwarz with one angle for all three vertices.* For x ≥ 0, y ∈ ℝ, χ ∈ [0, π/2]:
√(x² + Ky²) ≥ x cos χ + √K·|y| sin χ. Take sin χ = 3m/√(9+w²) (≤ 3/√(9+w²) < 1). Since √K = √(9+w²)/w,
√K sin χ = 3m/w. Hence

    Φ_w + 3 ≥ ½ cos χ Σ_i (c_ij+c_ik) + (3m/(2w))·V + (3/(2w))·E
            ≥ 3 cos χ √(1−m²) + (3m/(2w))(V + E)                      (by (2), and E ≥ mE as m ≤ 1)
            ≥ 3 √(1 − 9m²/(9+w²))·√(1−m²) + 3m²/w                     (by (1))
            ≥ 3(1−m²) + 3m² = 3                                         (9/(9+w²) ≤ 1 and 1/w ≥ 1). ∎

Lean (`PortsLean/CLStar.lean`, per the coordinator): `clstar_weighted` (Theorem D), the version with a general
vertex constant K ≥ 9/w² (Remark 6), and the three-angle inequality of §7 for every constant c ≥ 8 with sharpness.

Remarks.
1. *Equality.* The last step is strict unless m = 0 or (w = 1 and m = 1). So for w < 1 the only zero of Φ_w is σ = 0,
   and for w = 1 zeros other than 0 have m = 1, V + E = 2 and all c equal to 0: these are the six corners of the note
   §3.4. This proves the "no other zeros" statement that was [N] there.
2. *What made it invisible.* The earlier attempts (hull notes §3.5) bounded one pair term at a time or decoupled the
   angles. The proof uses one linearisation for all terms, tuned to the largest |σ|, and the cyclic telescoping.
3. [N] `clstar_analytic.py`: each inequality of the chain on 4·10⁵ points (uniform, near corners, near 0, random
   w ∈ (0,1]): no violation beyond rounding (−3·10⁻¹⁴).
4. [X] The argument cannot be pushed beyond w = 1, and neither can the statement: at the six corners
   Φ_w = 3/w − 3 < 0 for w > 1. See §5 for what replaces it.
5. The interval certificates of the note §3.3 (two independent checkers) remain as an independent confirmation
   of the case w = 1.
6. *Sharp vertex constant.* The proof uses K only through sin χ = 3m/(w√K) ≤ 1 and cos χ ≥ √(1−m²), i.e. K ≥ 9/w².
   So Φ_w ≥ 0 holds with the vertex terms ½√((c_ij+c_ik)² + K(σ_ij−σ_ik)²) for every K ≥ 9/w² (take
   sin χ = 3m/(w√K)); K = 1 + 9/w² is what the calibration produces. For w = 1 this is the constant 8 of §7.

### 3.4 The weighted five-point theorem [R given AN C.4(a)]

> **Theorem 5_w.** Let u₁, u₂, v₁, v₂, v₃ be points of a CAT(0) space and 0 < w ≤ 1. Then
> Σ_S ≥ κ(w)·(Σ_vv + w·D), κ(w) = 3/√(9+w²), with equality for W5(ℓ, wℓ/3).

*Proof.* If D = 0 then u₁ = u₂, Σ_vv ≤ Σ_{i<j}(A_i + A_j) = Σ_S and κ(w) < 1. If D > 0: by (3.1) Σ_vv ≤ Σ d^Z_ij; by
Proposition C₃ and Theorem D, Σ_S − κ(w)(Σd^Z_ij + wD) ≥ (κ(w)w/3)·D·Φ_w ≥ 0. Equality at W5(ℓ, wℓ/3): (2.1) with m = 3. ∎

For w = 1 this is Theorem 5 of the note, now without the certificate.

### 3.5 Theorem B: all m by averaging over triples [R]

> **Theorem B.** Let m ≥ 3, 0 < w ≤ m(m−1)/6, and let u₁, u₂, v₁, …, v_m be points of a CAT(0) space. Then
> Σ_S ≥ R_m(w)·(Σ_vv + w·D), with equality for W_{m+2}(ℓ, 2wℓ/(m(m−1))).

*Proof.* Put w′ = 6w/(m(m−1)) ∈ (0,1]. For each of the C(m,3) triples τ = {i,j,k} apply Theorem 5_{w′} to the five
points u₁, u₂, v_i, v_j, v_k of the same space:

    Σ_{l∈τ} (A_l + B_l) ≥ κ(w′)·( |v_iv_j| + |v_iv_k| + |v_jv_k| + w′D ).

(No m-page book and no m-page calibration is needed: Theorem 5_{w′} is applied to five-point subsets of the given
configuration.) Sum over all triples. Each v_l lies in C(m−1,2) triples, each pair in m−2 triples:

    C(m−1,2)·Σ_S ≥ κ(w′)·( (m−2)·Σ_vv + C(m,3)·w′·D ).

Divide by C(m−1,2) = (m−1)(m−2)/2 and use C(m,3)/(m−2) = m(m−1)/6:

    Σ_S ≥ (2κ(w′)/(m−1))·( Σ_vv + (m(m−1)/6)·w′·D ) = (2κ(w′)/(m−1))·( Σ_vv + wD ),

and 2κ(w′)/(m−1) = 6/((m−1)√(9 + 36w²/(m²(m−1)²))) = 2m/√(m²(m−1)² + 4w²) = R_m(w). Equality: (2.1). ∎

The counting and the last identity are in Lean (`PortsLean/CLStar.lean`: `k2m_average`, `k2m_rate`).

So K_{2,m} at weight w is exactly as hard as K_{2,3} at weight 6w/(m(m−1)); every triple of pages of the extremal
configuration W_{m+2}(ℓ, 2wℓ/(m(m−1))) is the extremal W5(ℓ, w′ℓ/3). The uniform instance w = 1 is covered for all
m ≥ 3 (for m ≥ 4 with room: w′ ≤ ½).

[N] `books.py`: the minimum over m-page books (2m parameters, 120 starts) is R_m(1) to 12 digits for m = 3, 4, 5,
attained at ρ_i = m(m−1)D/4, a_i = D/2, which is W_{m+2}; the only other local value found is the cut value 2/(m−1).

### 3.6 [X] The direct m-page calibration

Proposition C with λ = R_m(w) is tight at W_{m+2} (all exit vectors (1,0): |V_i| = m−1, M_i = λw/m, Br = 0). So the
natural analogue of (CL\*) would be

    (CL\*_m):   Br = Σ_i cos μ_i √(1 − λ²|V_i|²/4) − λw + (λ/2)Σ_{i<j}|ε_ij| ≥ 0   for all m(m−1) exit angles.

**It is false already on books: for every even m ≥ 4 and every w > 0, and for odd m ≥ 5 when
w > m(m−1)/(2√(m²−1)).** Take the collinear book with all ρ_i = 0 and v₁, …, v_m pairwise different interior
points of the spine, numbered upwards. With ρ ≡ 0 the hubs are not unique (every point of the spine between v_i and
v_j minimises f_i + f_j); they can be taken interior (ε_ij = 0), and then the exit vectors are vertical: v_i exits
upwards towards the i−1 points below it and downwards towards the m−i points above it. So V_i = (0, 2i − m − 1).
- m even: no V_i vanishes, all cos μ_i = 0, and Br = −λw < 0.
- m odd: the middle point has V_i = 0, M_i = 1, the others M_i = 0, and Br = 1 − λw, which is negative for
  λ = R_m(w) iff w > m(m−1)/(2√(m²−1)) (for m = 5: w > 2.04, inside the range w ≤ 10/3 of Theorem B).
The same happens for nearby books with small ρ_i > 0, where hubs and exit vectors are unique (`clm_counter.py`, m = 4,
w = 1: Br = −0.65 at a book where the true left side is +1.73·D; confirmed by the referee, `../review-k2m.md`; `calib_check.py`: negative values of Br on random books for (m,w) = (4,·), (5,3.3), (6,·),
none for (5,1) in 20 000 books). The reason is parity: an odd number m−1 of vertical exit vectors cannot cancel,
so V_i is vertical and non-zero and one of the calibrating vectors (cos α_i, sin α_i), (cos β_i, −sin β_i) points
out of the page (negative cosine), which wastes ρ_i ≥ 0. For m = 3 two opposite vertical exits cancel (V_i = 0,
M_i = 1), and Theorem D shows that this is enough. The refined calibration of §5.2 uses ρ_i ≥ 0 and repairs the
defect ([N]: no violation for m = 4, 5), but Theorem B makes it unnecessary in the range w ≤ m(m−1)/6.

---

## 4. The resulting statement

> **Theorem K_m.** Let m ≥ 3 and 0 < w ≤ m(m−1)/6 (in particular w = 1), and let k be any field.
> 1. *(Unconditional.)* f*(K_{2,m}(w); k) ≥ R_m(w) = 2m/√(m²(m−1)² + 4w²).
> 2. *(Conditional upper bound.)* If Contracting(k) fails, f*(K_{2,m}(w); k) = R_m(w). (The upper bound holds for
>    every w > 0, and for border protocols over infinite k of approximation degree 2^{o(n)}.)
> 3. *(Comparison.)* Routing achieves exactly f_flow = 2m/(m(m−1) + 2w), and the cut bound is
>    f_cut = min( 2/(m−1), m/(⌊m²/4⌋ + w) ). In the stated range f_flow < R_m(w) < f_cut.
> 4. *(Consequence.)* A protocol over k of rate above R_m(w) implies Contracting(k), with the consequences of the
>    note §5.

*Proof.* 1: (1.1), C.3 and Theorem B. 2: Theorem A.3 and item 1. 4: item 2. For 3:
- *Routing.* Send each v_iv_j half through u₁ and half through u₂, and u₁u₂ in equal parts through the m vertices
  v_j. Each edge u_kv_i carries f((m−1)/2 + w/m), so f = 2m/(m(m−1)+2w) is achieved. The path metric of K_{2,m}
  has Σ_S = 2m, Σ_vv = m(m−1), D = 2, i.e. R_w = 2m/(m(m−1)+2w); it is a pseudometric, so no routing does better.
- *Cuts.* For X with a = |X ∩ {u₁,u₂}|, b = |X ∩ {v_i}|, the cut separates a(m−b) + (2−a)b supply pairs and
  b(m−b) + w·[a = 1] demand weight. a = 0 (or 2): ratio 2/(m−b), least at b = 1. a = 1: ratio m/(b(m−b)+w), least
  at b = ⌊m/2⌋.
- *Strictness.* R_m(w) < 2/(m−1) for w > 0. R_m(w) ≤ m/(β+w) (β = ⌊m²/4⌋) iff 4(β+w)² ≤ m²(m−1)²+4w² iff
  w ≤ w_c(m) := (m²(m−1)² − 4β²)/(8β), with strict inequality for w < w_c(m). And m(m−1)/6 < w_c(m): for m = 3,
  w_c = 5/4 > 1; for m ≥ 4, w_c is decreasing in β and β ≤ m²/4, so w_c(m) ≥ (3m−2)(m−2)/8, and
  (3m−2)(m−2)/8 ≥ m(m−1)/6 iff 5m² − 20m + 12 ≥ 0, true for m ≥ 4. (w_c(4) = 5/2, w_c(5) = 16/3.)
  R_m(w) > f_flow because (m(m−1)+2w)² > m²(m−1)² + 4w². ∎

Numbers for w = 1:

| m | f_flow = 2m/(m(m−1)+2) | R_m(1) | f_cut = 2/(m−1) | R_m/f_flow |
|---|---|---|---|---|
| 3 | 0.7500 | 0.948683 = 3/√10 | 1 | 1.2649 |
| 4 | 0.5714 | 0.657596 = 8/√148 | 0.6667 | 1.1508 |
| 5 | 0.4545 | 0.497519 = 10/√404 | 0.5 | 1.0945 |
| 6 | 0.3750 | 0.399114 = 12/√904 | 0.4 | 1.0643 |

The gain over routing is (m(m−1)+2w)/√(m²(m−1)²+4w²). In the proved range it is largest at the top weight
w = m(m−1)/6, where it equals 4/√10 = 1.2649 for every m (the K_{2,3}, w = 1 value). At w = 1 it tends to 1 like
1 + 2/(m(m−1)). So K_{2,3} is the member of the uniform family with the largest forced gap, both to routing and
to the cut bound (f_cut/R_m(1) = √(1 + 4/(m²(m−1)²))).

*What is not claimed.* Nothing for w > m(m−1)/6 beyond §5. No explicit protocols. If Contracting(k) holds only
f* ∈ [R_m(w), f_cut] is known. Uniqueness of the minimiser is not proved (for w < 1, m = 3, equality in Theorem D
forces σ = 0, which is a step towards it).
