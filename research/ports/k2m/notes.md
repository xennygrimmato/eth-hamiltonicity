# K_{2,m}: tensor rate, pods, books, and an analytic proof of (CL*)

Theory notes, 26 Nov 2026. Companion to `../note-k23-rate.md` ("the note") and `../hull/notes.md` ("hull notes").

Tags: **[R]** proved here, complete proof in this file from the cited statements; **[D]** derived, unreviewed or resting
on an uncertified step; **[N]** numerical; **[C]** conjecture; **[X]** dead, with the reason; **[AN]** quoted from
Anthropic's paper as in the note §0.3 (C.3 = `prop_space`, C.4(a),(f) = `lem_toolkit`, `thm_alt_rank_price`).

Scripts (this folder; all [N] except `fqpods.py`, which is exact integer arithmetic):
`books.py`, `wscan.py` (book minimisation for K_{2,m}(w)), `calib_check.py`, `clm_counter.py` (calibration identities,
counterexample of §3.6), `clstar_analytic.py` (steps of Theorem D), `fqpods.py` (rank tables over F_q),
`refined.py`, `refined_m.py`, `cutregime.py`, `thmE_check.py`, `hardregion.py`, `hardregion2.py` (§5),
`twoapex.py`, `scan2.py`, `scan3.py`, `k33.py`, `k33_models.py` (§6), `three_angle.py` (§7). Outputs: `*.out`.

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
| 10 | **Theorem E / Corollary E (cut regime, unconditional).** Five CAT(0) points, w ≥ w₁ = 1.91345: Σ_S ≥ (3/(2+w))(Σ_vv + wD). Hence f*(K_{2,3}(w); k) = 3/(2+w) for w ≥ w₁ and f*(K_{2,4}(w); k) = 4/(4+w) for w ≥ 2w₁, every field, no hypothesis; routing gives 3/(3+w), 4/(6+w). | [R] (§5.2–5.3: refined calibration Prop. C′, bounds (X1),(X2), one-vertex lemmas (V1),(V2)); not yet refereed |
| 10a | Lemma R: outside the hard region 𝓕′ the refined bracket is ≥ 0 for every (λ,η) of the conjectured region. | [R] (§5.4) |
| 10b | Conjecture W (valid region = ellipse ∩ cut half-plane), (CL\*\*), (★): 13Σ_S ≥ 12Σ_vv + 15D; statements S(λ₂). | [C], [N]; certificate spec in §5.4 (S(9/10): six variables, margin +0.063, no zeros) |
| 11 | P2: pinned / cut-pinned networks; book principle; Prop. T (triangle-decomposable demands on K_{2,m}); Conjecture P; instances. | §6: [R] / [N] / [C] as marked |
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

---

## 5. Weights above the proved range: refined calibration, the cut regime, and what is open

### 5.1 The picture [R for the stated inclusions; C for the full description]

For fixed m let 𝒱_m be the set of (λ,η) ∈ ℝ²_{≥0} such that Σ_S ≥ λΣ_vv + ηD for all m+2 points of all CAT(0)
spaces. It is closed, convex and downward closed, and min over CAT(0) configurations of R_w = max{λ : (λ, λw) ∈ 𝒱_m}.

*Necessary conditions.* W_{m+2}(ℓ,h) for all ℓ,h gives (m(m−1)λ)² + (2η)² ≤ 4m² (an ellipse 𝓔_m); the cut metric of
X = {u₁} ∪ B with |B| = b gives b(m−b)λ + η ≤ m, strongest for b(m−b) = β := ⌊m²/4⌋.

*Known inside.* (0, m) (triangle inequality A_i + B_i ≥ D); the arc of 𝓔_m with η/λ ≤ m(m−1)/6 (Theorem B);
for m = 3 the part λ ≤ λ₁ of the cut line 2λ + η = 3 (Theorem E below); and convex combinations.

> **Conjecture W** [C; N for m = 3, 4, 5]. 𝒱_m = 𝓔_m ∩ {βλ + η ≤ m}. Equivalently, for every w > 0,
> min over CAT(0) configurations of R_w = min( R_m(w), m/(β + w) ), with the switch at w_c(m) = (m²(m−1)²−4β²)/(8β)
> (w_c = 5/4, 5/2, 16/3 for m = 3, 4, 5).

[N] `wscan.py` (minimum over m-page books, 150 starts each): the book minimum equals R_m(w) for
(m,w) = (3, 0.3 … 1.25), (4, 2 … 2.5), (5, 3.33 … 5.33), and equals the cut value m/(β+w) for (3, 1.3 … 3),
(4, 2.6 … 6), (5, 5.6, 8); no other minimiser appeared.

For m = 3 the corner of the conjectured region is (λ,η) = (12/13, 15/13), i.e. the single inequality

    (★)   13 Σ_S ≥ 12 Σ_vv + 15 D      for five points of a CAT(0) space,

with equality both at W5(ℓ, 5ℓ/12) and at the cut metric of {u₁, v₁}. By convexity, (★) together with (0,3) gives
the whole segment of the cut line, i.e. the cut regime w ≥ 5/4. The arc for 1 < w < 5/4 consists of extreme
points of the conjectured region and needs each point separately.

*What follows unconditionally from the proved points* (convexity: the chord from the arc point at w = 1,
(3/√10, 3/√10), to the point (λ₁, 3−2λ₁) of Theorem E lies in 𝒱₃):

| w | proved lower bound on f*(K_{2,3}(w)) | conjectured value min(3/√(9+w²), 3/(2+w)) | routing 3/(3+w) |
|---|---|---|---|
| 1 | 0.948683 (Theorem 5) | 0.948683 | 0.7500 |
| 1.1 | 0.9246 | 0.938876 | 0.7317 |
| 1.25 | 0.8908 | 0.923077 | 0.7059 |
| 1.5 | 0.8395 | 0.857143 | 0.6667 |
| 1.75 | 0.7939 | 0.800000 | 0.6316 |
| ≥ 1.91345 | 3/(2+w) (Theorem E) | 3/(2+w) | 3/(3+w) |

(The entries for 1 < w < w₁ are the intersection of the chord with the ray η = wλ.)

### 5.2 Refined calibration [R]

The calibration of §3.2 asks for cos α_i + cos β_i = λP_i exactly. Since ρ_i ≥ 0, the inequality ≥ suffices. This
gains exactly when one of α_i, β_i would exceed π/2.

> **Proposition C′ (m pages, any λ ∈ (0, 2/(m−1)), any η).** In a book, with the notation of §3.2, let
> sin κ_i := λ|V_i|/2 (κ_i ∈ [0, π/2)) and
>
>     N_i := cos( (κ_i − |μ_i|)₊ ),        X := Σ_i |Q_i| − Σ_{i<j} |ε_ij|.
>
> Then  Σ_S − λ Σ_{i<j} d^Z_ij − ηD ≥ D · Br′,   Br′ := Σ_i N_i − (λ/2)·X − η.

*Proof.* Let a_i = (a_ix, a_iy), b_i = (b_ix, b_iy) ∈ ℝ² with |a_i| ≤ 1, |b_i| ≤ 1 and

    a_ix + b_ix ≥ λP_i,        a_iy − b_iy = λQ_i.                                                         (5.1)

By Cauchy–Schwarz, A_i ≥ ⟨a_i, (ρ_i, a_i)⟩ and B_i ≥ ⟨(b_ix, −b_iy), (ρ_i, a_i − D)⟩ = ρ_ib_ix + (D − a_i)b_iy
(here a_i also denotes the height of v_i; no confusion arises). Adding, and using ρ_i ≥ 0 in the first term:

    A_i + B_i ≥ ρ_i(a_ix + b_ix) + a_i(a_iy − b_iy) + D b_iy ≥ λ(ρ_iP_i + a_iQ_i) + D b_iy.

Sum over i, use (3.3), b_iy = (a_iy + b_iy)/2 − λQ_i/2 and Σ_iQ_i = E₂ − E₁:

    Σ_S ≥ λ(Σ d^Z_ij + DE₂) + D Σ_i (a_iy+b_iy)/2 − (λD/2)(E₂ − E₁),
    Σ_S − λΣ d^Z_ij − ηD ≥ D·( Σ_i (a_iy+b_iy)/2 + (λ/2)Σ_{i<j}|ε_ij| − η ).

It remains to exhibit, for each i, vectors satisfying (5.1) with (a_iy + b_iy)/2 = N_i − (λ/2)|Q_i|. Recall
P_i = |V_i| cos μ_i, Q_i = |V_i| sin μ_i, so (λ/2)|Q_i| = sin κ_i sin|μ_i|.
- *|μ_i| ≤ κ_i (the old choice).* a_i = (cos α_i, sin α_i), b_i = (cos β_i, sin β_i) with α_i = ν_i + μ_i,
  β_i = ν_i − μ_i, ν_i = π/2 − κ_i. Then (5.1) holds with equality (§3.2), and
  (a_iy+b_iy)/2 = sin ν_i cos μ_i = cos κ_i cos μ_i = cos(κ_i − |μ_i|) − sin κ_i sin|μ_i|.
- *μ_i > κ_i.* a_i = (0, 1), b_i = (√(1−(1−λQ_i)²), 1 − λQ_i). Here 0 < λQ_i ≤ 2 sin κ_i < 2, so |b_iy| ≤ 1 and
  |b_i| = 1; a_iy − b_iy = λQ_i; and a_ix + b_ix ≥ λP_i iff 2λQ_i − λ²Q_i² ≥ λ²P_i² iff 2Q_i ≥ λ|V_i|² iff
  sin μ_i ≥ sin κ_i, which holds. (a_iy+b_iy)/2 = 1 − λQ_i/2.
- *μ_i < −κ_i.* Mirror image: b_i = (0,1), a_i = (√(1−(1−λ|Q_i|)²), 1 − λ|Q_i|). ∎

(These choices are optimal for (5.1) — the maximum of (a_y+b_y)/2 is the top of the lens
{p : |p ± h| ≤ 1}, h = λV_i/2 + (x,0), x ≥ 0 — but only feasibility is used.) We call the vertex i *linear* if
|μ_i| ≥ κ_i (N_i = 1) and *curved* otherwise. For m = 3, in the six exit sines, with c = √(1−σ²):

    sin κ_i = λ cos δ_i,   |V_i|² = (c_ij+c_ik)² + (σ_ij+σ_ik)²,   Q_i = σ_ij + σ_ik,
    linear iff 2|Q_i| ≥ λ|V_i|²;   curved: N_i = ½√((1−λ²)(c_ij+c_ik)² + (σ_ij−σ_ik)²) + (λ/2)|Q_i|.

The old bracket is Br = Σ_i cos(κ_i − |μ_i|) − (λ/2)X − η ≤ Br′ (it has the cosine without the positive part).
[N] `refined.py`, `refined_m.py`, `thmE_check.py`: the formula against a direct maximisation; true left side
≥ D·Br′ on 20 000 random books for each of w = 1, 1.1, 1.2, 1.25, 1.3 (m = 3) and 8000 for m = 4, 5.

**Two bounds on X (m = 3)** [R].
- (X1) If Q₁, Q₂, Q₃ are all ≥ 0 or all ≤ 0 ("unfrustrated"), then X ≤ 0: Σ_{i<j}|ε_ij| ≥ |Σε_ij| = |ΣQ_i| = Σ|Q_i|.
- (X2) Otherwise, after renumbering the pages and possibly replacing σ by −σ (which preserves N_i, |Q_i|, |ε_ij|),
  Q₁ ≤ 0 ≤ Q₂, Q₃ ("frustrated at v₁"), and

      X ≤ 2 min(−σ₁₂, σ₂₁) + 2 min(−σ₁₃, σ₃₁) ≤ 4.

  Proof: for any signs s₁₂, s₁₃ ∈ {±1}, Σ|ε_ij| ≥ s₁₂ε₁₂ + s₁₃ε₁₃ + ε₂₃, so
  X ≤ −Q₁ + Q₂ + Q₃ − ε₂₃ − s₁₂ε₁₂ − s₁₃ε₁₃ = (−σ₁₂ + σ₂₁ − s₁₂(σ₁₂+σ₂₁)) + (−σ₁₃ + σ₃₁ − s₁₃(σ₁₃+σ₃₁)), and the first
  bracket is −2σ₁₂ or 2σ₂₁ according to s₁₂, the second −2σ₁₃ or 2σ₃₁.

Consequences for m = 3, any (λ,η):
- unfrustrated configurations: Br′ ≥ Σ_iN_i − η ≥ 3√(1−λ²) − η (N_i ≥ cos κ_i ≥ √(1−λ²)); so Br′ ≥ 0 on and inside the
  ellipse 𝓔₃;
- all three vertices linear: Br′ = 3 − (λ/2)X − η ≥ 3 − 2λ − η; so Br′ ≥ 0 on and below the cut line;
- at the six corners of the cube where Br < 0 for w > 1 (§3.3 Remark 4), Br′ = 3 − 2λ − η exactly.

### 5.3 Theorem E: the cut regime [R]

Let λ₁ = 0.766588… be the real root of 4λ³ − 8λ² + 9λ − 4 = 0, and w₁ := (3 − 2λ₁)/λ₁ = 1.913443…

> **Theorem E.** For 0 < λ ≤ λ₁ and five points u₁, u₂, v₁, v₂, v₃ of a CAT(0) space:
> Σ_S ≥ λ Σ_vv + (3 − 2λ) D. Equivalently, for every w ≥ w₁,
>
>     Σ_S ≥ (3/(2+w)) · (Σ_vv + w D),       with equality for the cut metric of {u₁, v₁}.

> **Corollary E (unconditional exact rates).** For every field k:
> 1. f*(K_{2,3}(w); k) = 3/(2+w) for all w ≥ w₁ (in particular for w ≥ 2). Routing gives 3/(3+w).
> 2. f*(K_{2,4}(w); k) = 4/(4+w) for all w ≥ 2w₁ = 3.82689 (in particular for w ≥ 4). Routing gives 4/(6+w).

*Why 3/(2+w) is the upper bound.* The cut X = {u₁, v₁} is crossed by three supply wires (u₁v₂, u₁v₃, u₂v₁) and by
the demand wires v₁v₂, v₁v₃ (rate f each) and u₁u₂ (rate wf). The flattening rank across X is a spectral point, so
(2 + w) f ≤ 3 for every protocol over every field. This is the smallest cut ratio as soon as w ≥ 1, and it is
below the W5 value κ(w) iff w > 5/4. For K_{2,4}: X = {u₁, v₁, v₂}, four supply wires against 4 + w.

*Proof of Corollary E.* 1: lower bound by (1.1), C.3 and Theorem E; upper bound by the cut. 2: apply Theorem E with
weight w′ = w/2 ≥ w₁ to the four triples as in §3.5: 3Σ_S ≥ (3/(2+w′))(2Σ_vv + 4w′D), i.e.
Σ_S ≥ (4/(4+w))(Σ_vv + wD); upper bound by the cut. (For m ≥ 5 the same averaging gives m/(w + m(m−1)/3), which is
below the cut bound m/(w + ⌊m²/4⌋): triples are not enough there.) ∎

*Proof of Theorem E.* The case D = 0 is Σ_vv ≤ Σ_S. Let D > 0, η = 3 − 2λ, τ = √(1−λ²). By (3.1) and Proposition C′
it suffices to show Br′ ≥ 0, i.e.

    Σ_i (1 − N_i) ≤ (λ/2)(4 − X).                                                                          (5.2)

Two one-vertex lemmas. For a vertex with exit angles ψ, ψ′ ∈ [−π/2, π/2] put μ = (ψ+ψ′)/2, d = |ψ−ψ′|/2,
sin κ = λ cos d, N = cos((κ−|μ|)₊), Q = sin ψ + sin ψ′ = 2 cos d sin μ. Let sin κ₀ = λ (so cos κ₀ = τ and κ ≤ κ₀).

(V1) *1 − N ≤ (1−τ)(1 − |Q|/2).* If |μ| ≥ κ the left side is 0. Let 0 ≤ μ ≤ κ (the case μ < 0 is symmetric) and
t := (1−τ)/λ = tan(κ₀/2) ∈ (0,1). Since |Q|/2 = sin κ sin μ/λ, right minus left equals

    g(μ) = cos κ cos μ + (1 − t) sin κ sin μ − τ,

which is concave in μ on [0, κ] (non-negative coefficients of cos μ and sin μ). g(0) = cos κ − cos κ₀ ≥ 0 and
g(κ) = 1 − t sin²κ − τ ≥ 1 − tλ² − τ = (1−τ)(1−λ) ≥ 0. So g ≥ 0.

(V2) *If μ ≥ 0, then 1 − N ≤ λ²(1 − s), where s = sin(μ + d) is the larger exit sine.* (Mirror statement for μ ≤ 0
with 1 + the smaller exit sine.) If μ ≥ κ the left side is 0. Let 0 ≤ μ ≤ κ and φ := π/2 − d, so sin κ = λ sin φ,
0 ≤ κ ≤ φ, and 1 − s = 1 − cos(φ − μ) = 2 sin²((φ−μ)/2), 1 − N = 2 sin²((κ−μ)/2). Put
h(μ) = λ sin((φ−μ)/2) − sin((κ−μ)/2). Then h′(μ) = ½[cos((κ−μ)/2) − λ cos((φ−μ)/2)] ≥ 0 because 0 ≤ κ−μ ≤ φ−μ,
and h(0) = λ sin(φ/2) − sin(κ/2) ≥ 0 because sin(κ/2) = λ sin(φ/2)·cos(φ/2)/cos(κ/2) and κ ≤ φ. So h ≥ 0 on [0,κ].

*Unfrustrated case.* X ≤ 0 by (X1), and 1 − N_i ≤ 1 − τ. (5.2) follows from 3(1−τ) ≤ 2λ, which is
(3−2λ)² ≤ 9(1−λ²), i.e. λ ≤ 12/13.

*Frustrated case,* Q₁ ≤ 0 ≤ Q₂, Q₃. Put α := (1−τ)/(2λ) ∈ (0,1). By (X2) and min(x,y) ≤ αx + (1−α)y,

    4 − X ≥ 2α(2 + σ₁₂ + σ₁₃) + 2(1−α)(1 − σ₂₁) + 2(1−α)(1 − σ₃₁) = 2α(2 − |Q₁|) + 2(1−α)[(1−σ₂₁) + (1−σ₃₁)].

By (V1) at v₁: 1 − N₁ ≤ (1−τ)(1 − |Q₁|/2) = λα(2 − |Q₁|). By (V2) at v₂ and v₃ (μ₂, μ₃ ≥ 0):
1 − N₂ ≤ λ²(1 − σ₂₁), 1 − N₃ ≤ λ²(1 − σ₃₁). Hence

    (λ/2)(4 − X) − Σ_i(1 − N_i) ≥ (λ(1−α) − λ²)·[(1−σ₂₁) + (1−σ₃₁)] ≥ 0

as soon as λ(1−α) ≥ λ², i.e. G(λ) := 2λ(1−λ) − (1 − √(1−λ²)) ≥ 0. Now G(0) = 0, G′(0) = 2 > 0, and G(λ) = 0 with
λ > 0 forces √(1−λ²) = 1 − 2λ + 2λ², hence 4λ³ − 8λ² + 9λ − 4 = 0, whose derivative 12λ² − 16λ + 9 has no real root; so
the cubic has the single real root λ₁, and G > 0 on (0, λ₁). ∎

[N] `thmE_check.py`: (V1), (V2), (X1), (X2) and Br′ ≥ 0 for λ ≤ λ₁ on 3·10⁵ points: no violation beyond rounding
(−10⁻¹⁵). `wscan.py`: book minimum at w = 2, 3 (m = 3) and w = 4.5, 6 (m = 4) equals the cut value.

Remarks.
1. This is an *unconditional exact* value of a tensor rate strictly above the routing rate (ratio (3+w)/(2+w):
   1.25 at w = 2), with no hypothesis on contracting: the lower bound uses only Strassen duality and C.3/C.4(a), the
   upper bound a flattening rank.
2. The threshold w₁ is where the two one-vertex lemmas stop being compatible: (V1) is tight at the centre σ = 0 and
   (V2) on vertices with exits ≈ (1, −1). The conjectured truth is w ≥ 5/4 (λ ≤ 12/13).
3. Example, K_{2,3}(2): from n copies of the six binary wires one obtains asymptotically 0.75n binary wires on each
   pair v_iv_j together with 1.5n on u₁u₂, and no more; routing obtains 0.6n and 1.2n.

### 5.4 The remaining range 1 < w < w₁: reduction, statement and certificate spec [R reduction; C; N]

Write Br′ = (3 − 2λ − η) + (λ/2)(4 − X) − Σ_i(1 − N_i). In the frustrated case Q₁ ≤ 0 ≤ Q₂, Q₃ the middle term is
exactly (a + b + |a−b| = 2max(a,b))

    (λ/2)(4 − X) = λ·[ max(1+σ₁₂, 1−σ₂₁) + max(1+σ₁₃, 1−σ₃₁) + (−σ₂₃−σ₃₂)₊ ].                             (5.3)

> **Lemma R (reduction to the hard region)** [R]. Let λ ∈ (0, 12/13] and η ≤ min(3√(1−λ²), 3 − 2λ). Then Br′ ≥ 0 at
> every σ ∈ [−1,1]⁶ outside the set
>
>     𝓕′ := { frustrated at some v_i (Q_i of one sign, the other two of the opposite sign, weakly),
>             v_i curved, and at least one of the other two vertices curved }.

*Proof.* Unfrustrated: §5.2 (needs η ≤ 3τ). Frustrated at v₁, say Q₁ ≤ 0 ≤ Q₂, Q₃ (the other cases by symmetry):
- *v₁ linear.* 1 − N₁ = 0; by (V2), 1 − N₂ ≤ λ²(1−σ₂₁) and 1 − N₃ ≤ λ²(1−σ₃₁); by (5.3),
  (λ/2)(4−X) ≥ λ[(1−σ₂₁) + (1−σ₃₁)]. So Br′ ≥ 3 − 2λ − η ≥ 0.
- *v₂ and v₃ linear.* By (V1), 1 − N₁ ≤ ((1−τ)/2)[(1+σ₁₂) + (1+σ₁₃)], and (1−τ)/2 ≤ λ; by (5.3),
  (λ/2)(4−X) ≥ λ[(1+σ₁₂) + (1+σ₁₃)]. So Br′ ≥ 3 − 2λ − η ≥ 0. ∎

In particular all zeros of Br′ at the corner λ = 12/13 that come from the cut configuration (the points with X = 4,
a two-dimensional family in faces of the cube) lie outside 𝓕′, and the six corners where the old bracket fails
lie outside 𝓕′. On the closure of 𝓕′, v_i curved means |μ_i| ≤ κ_i, i.e. 2|Q_i| ≤ λW_i in the notation below.

> **Conjecture (CL\*\*).** For 12/13 ≤ λ ≤ 3/√10 and σ in the closure of 𝓕′:  Br′(σ; λ, 3√(1−λ²)) ≥ 0, with
> equality only at σ = 0. **(CL\*\*₀)** is the case λ = 12/13 (η = 15/13).
> **Statement S(λ₂)**, for a fixed λ₂ ∈ (λ₁, 12/13): Br′(σ; λ₂, 3 − 2λ₂) > 0 on the closure of 𝓕′.

Consequences [R given the respective statement, by Lemma R, Proposition C′ and (3.1)]:
- S(λ₂) ⇒ Theorem E and Corollary E for all w ≥ (3−2λ₂)/λ₂ (by convexity with (0,3) one certified λ₂ covers all
  smaller λ): w ≥ 3/2 for λ₂ = 6/7, w ≥ 4/3 for λ₂ = 9/10.
- (CL\*\*₀) ⇒ (★) ⇒ f*(K_{2,3}(w)) = 3/(2+w) for all w ≥ 5/4 and f*(K_{2,4}(w)) = 4/(4+w) for all w ≥ 5/2,
  unconditionally.
- (CL\*\*) ⇒ Theorem 5_w for 0 < w ≤ 5/4 ⇒ Theorems B, K_m for 0 < w ≤ 5m(m−1)/24; with (CL\*\*₀) this is
  Conjecture W for m = 3 and m = 4.

[N] `hardregion.py` (minimum of Br′ over the closure of 𝓕′, 400 penalised local searches each):

| (λ, η) | w | min over closure(𝓕′) | where |
|---|---|---|---|
| (0.8, 1.4), cut line | 7/4 | +0.1619 | boundary "v₁ becomes linear" |
| (6/7, 9/7), cut line | 3/2 | +0.1035 | same |
| (9/10, 6/5), cut line | 4/3 | +0.0627 | same |
| (12/13, 15/13), corner | 5/4 | 0 (searches stop at +9·10⁻⁴ near σ = 0) | σ = 0 |
| arc, w = 1.2 and w = 1.1 | | 0 (+1·10⁻³, +3·10⁻⁴ near σ = 0) | σ = 0 |

So S(λ₂) has a positive margin and no zero in its domain: it is a plain interval problem in six variables.
`refined.py`: on the whole cube the minimum of Br′ is ≥ 0 for w = 1, 1.1, 1.2, 1.25 and negative (−0.028) for
w = 1.3, as it must be.

**Certificate spec.** Variables σ = (σ₁₂,σ₁₃,σ₂₁,σ₂₃,σ₃₁,σ₃₂) ∈ [−1,1]⁶, c = √(1−σ²); parameters λ, τ = √(1−λ²), η.

    vertex (σ,σ′):   Q = σ + σ′,   W = (c+c′)² + Q²,
                     C(σ,σ′) = ½√(τ²(c+c′)² + (σ−σ′)²) + (λ/2)|Q|        ("curved expression"; C ≤ 1 everywhere)
                     N(σ,σ′) = 1 if 2|Q| ≥ λW ("linear"),   = C(σ,σ′) otherwise ("curved")
    E = |σ₁₂+σ₂₁| + |σ₁₃+σ₃₁| + |σ₂₃+σ₃₂|,     X = |Q₁| + |Q₂| + |Q₃| − E,
    Br′ = N(σ₁₂,σ₁₃) + N(σ₂₁,σ₂₃) + N(σ₃₁,σ₃₂) − (λ/2)·X − η.

N is continuous and C ≤ N, so on any box a valid lower bound of Br′ is obtained by using C for every vertex, or 1
for a vertex that is certainly linear on the box. Domain (after the symmetries S₃ on the pages and σ ↦ −σ, which
preserve Br′): the closed set

    𝓕′₁ = { Q₁ ≤ 0,  Q₂ ≥ 0,  Q₃ ≥ 0,  2|Q₁| ≤ λW₁,  2Q₂ ≤ λW₂ }        (frustrated at v₁, v₁ curved, v₂ curved)

(the case "v₃ curved" is its image under the exchange of pages 2 and 3). On 𝓕′₁ one has N₁ = C₁, N₂ = C₂, and
X = −Q₁ + Q₂ + Q₃ − E. A leaf box is closed if one of the five defining inequalities is certainly violated on it, or
if the lower bound of Br′ on it is ≥ 0.
1. **S(9/10):** λ = 9/10, τ = √19/10, η = 6/5. Expected minimum +0.0627 [N]. No special points. This is the
   recommended first run; it lowers the threshold of Theorem E from 1.9134 to 4/3. (S(6/7): η = 9/7, margin 0.10.)
2. **(CL\*\*₀):** λ = 12/13, τ = 5/13, η = 15/13. The only zero in the domain is σ = 0, where Br′ is not smooth
   (the terms |ε_ij|, |Q_i|). Treat a neighbourhood as in `clnear` of the note §3.3: in the coordinates
   a_k = (σ_ij − σ_ji)/2, e_k = (σ_ij + σ_ji)/2, on the slice e = 0 the function is 3τ(F_c/3 − 1)-like with
   positive definite Hessian (margin λ² − 3τ² = 69/169, cf. §7 Remark 3), and it grows linearly in |e|; note that
   near 0 every vertex is curved, so Br′ equals the old bracket Br there and the gain test of `clnear` applies with
   the constants 1 + 9/w² → 1/τ² and 3/(2w) → λ/(2τ) (after division by τ).
3. **(CL\*\*):** the same with λ ∈ [12/13, 3/√10] as a seventh variable and η = 3√(1−λ²); zero at σ = 0 for
   every λ. Only after 2.

An analytic proof of S(λ₂) or (CL\*\*₀) would have to use (5.3) with its third term: at λ = 12/13 the one-vertex
bounds (V1), (V2) alone are not sufficient ([X]: with 1+σ₁₂ = 1+σ₁₃ = 1−σ₂₁ = 1−σ₃₁ = e they allow 2.32e on the left
against 1.85e on the right, although the true left side is smaller).

---

## 6. P2: which networks are pinned

### 6.1 The principle [R]

For supply G (capacities c) and demand H (weights r) on the same parties, (1.2) reads
f_flow ≤ f_CAT(0) ≤ f*(k) ≤ f_cut. Let 𝓗 be the class of finite metric spaces that are *forced*: X ∈ 𝓗 if for some μ
every CAT(0) space containing an isometric copy of a scaled (Mat_μ(F₂), ρ_μ) contains an isometric copy of X.
If Contracting(k) fails, every X ∈ 𝓗 is a price over k (C.3 + `thm_alt_rank_price`), so
f*(k) ≤ f_𝓗 := inf over configurations in 𝓗.

> **Definition.** (G,H) is *pinned* if f_CAT(0) = f_𝓗. Then f*(k) = f_CAT(0) whenever Contracting(k) fails, and a
> protocol of rate above f_CAT(0) proves Contracting(k). It is *cut-pinned* if f_CAT(0) = f_cut; then
> f*(k) = f_cut for every field, unconditionally.

Known members of 𝓗: all finite subsets of (m-pod) × ℝ, every m (Theorem A.2); 𝓗 is closed under subsets, scaling
and (for the purpose of prices) pointwise limits. Not known to be in 𝓗: products of two pods; (tree with two
branch points) × ℝ; a book with a geodesic through an end of the spine.

> **Hull conjecture** [C]. If Contracting(k) fails, every finite subset of the Euclidean building of
> GL_n(F₂((t))) (every n, standard metric) is a price over k.

(The points L_a of the hull notes §1.1 are vertices of this building and their distance is √2·ρ_μ [D, hull notes /
c1].) It would give pods of every valence (via F_q((t))), products of trees and flats (Levi sub-buildings), and
hence every configuration that has appeared as a minimiser so far. What is proved towards it is Theorem A. The
obstacle to more is that forcedness is not obviously closed under ℓ₂ products: for S₁ × S₂ realised by block
diagonal matrices, flat rectangles (C.4(f)) give the product structure on (geodesics between points of S₁) × S₂,
but a point of the hull of S₁ that is not on such a geodesic has distances to S₁ that depend on the ambient
space, so the induction does not close without a rigidity statement for the hull of S₁ itself. [X] as a general
lemma; open for S₁ = N_{m+2}, S₂ = a cube.

### 6.2 Two-apex networks [R / N / C]

A network is *two-apex* if every supply wire has an end in {u₁,u₂} (supply ⊂ {u_kv_i} ∪ {u₁u₂}, any capacities);
the demand is arbitrary.

> **Proposition B (book principle)** [R, using Reshetnyak gluing for "≤"]. For a two-apex network,
> f_CAT(0) = minimum of the ratio over m-page books (2m+1 real parameters; D = 0, a star centred at u₁ = u₂, included).

Proof: (3.1) leaves the supply side unchanged and can only increase the demand side; conversely a book is CAT(0).
(Demand on pairs u_kv_i is allowed: those distances are unchanged.)

A book differs from the configuration with the same coordinates in (m-pod) × ℝ only when a geodesic v_iv_j would
leave the spine segment: in the pod the hub may lie anywhere on the line, so d^pod_ij ≤ d^Z_ij and
f_pod ≥ f_book, with equality if some optimal book has all its (unconstrained) hubs on the spine.

> **Conjecture P** [C; N]. For every two-apex network some optimal book has all hubs on the spine; hence
> f_CAT(0) = f_pod, the network is pinned, and f*(k) = f_book whenever Contracting(k) fails.

[N] `scan2.py`, `scan3.py`, `twoapex.py`: no instance with f_book < f_pod was found (the list of §6.3 and 138 random
instances, §8). For the triangle-decomposable family it is a theorem:

> **Proposition T** [R]. Let H be an r-regular graph on v₁,…,v_m with a fractional triangle decomposition
> (weights x_t ≥ 0 on the triangles of H with Σ_{t∋e} x_t = 1 for every edge e). For the network "supply K_{2,m},
> demand H at rate f and u₁u₂ at rate wf", 0 < w ≤ mr/6:
> f_CAT(0) = 2m/√(m²r² + 4w²), attained at W_{m+2}(ℓ, 2wℓ/(mr)); the network is pinned.

Proof: Σ_{t∋i}x_t = r/2 and Σ_t x_t = mr/6. Summing Theorem 5_{w′}, w′ = 6w/(mr), over the triangles with weights x_t:
(r/2)Σ_S ≥ κ(w′)(Σ_H + (mr/6)w′D), i.e. Σ_S ≥ (2κ(w′)/r)(Σ_H + wD) and 2κ(w′)/r = 2m/√(m²r²+4w²). Equality at W_{m+2}:
Σ_S = 2m√(ℓ²+h²), Σ_H = mrℓ, D = 2h and Cauchy–Schwarz. ∎
(H = K_m is Theorem B. Non-regular H: the same with capacities deg_H(v_i) on the wires at v_i.)

### 6.3 Instances [R where stated, otherwise N]

| network | f_flow | f_CAT(0) | f_cut | status |
|---|---|---|---|---|
| K_{2,3}(w), 0 < w ≤ 1 (5 parties) | 3/(3+w) | 3/√(9+w²) | 1 | [R]; three values distinct; pinned |
| K_{2,3}(w), 1 < w < 5/4 | 3/(3+w) | 3/√(9+w²) [N]; ≥ chord of §5.1 [R] | 3/(2+w) | distinct [N]; pinned [N] |
| K_{2,3}(w), w ≥ 1.91345 | 3/(3+w) | 3/(2+w) | 3/(2+w) | [R]; cut-pinned: f* exact, unconditional |
| K_{2,4}(1) (6 parties) | 4/7 | 8/√148 = 0.65760 | 2/3 | [R]; distinct; pinned |
| K_{2,4}(w), w ≥ 3.8269 | 4/(6+w) | 4/(4+w) | 4/(4+w) | [R]; cut-pinned |
| K_{2,6} + octahedron demand, w = 1 (8 parties) | 6/13 | 12/√580 = 0.498273 | 1/2 | [R] (Prop. T, r = 4); distinct; pinned |
| K_{2,5} + pentagon demand C₅, w = 1 (7 parties) | 5/6 | 5/√26 = 0.980581 [N: books] | 1 | distinct [N]; optimum is W₇, pinned [N]; no triangle, so no proof |
| K_{2,3}, supply u₁v₁, u₁v₂ doubled, demand v₁v₂ doubled (5 parties; scan #2 of e3) | 0.8 | 0.965136 [N: books and Toyoda] | 1 | distinct; optimum an asymmetric book with interior hubs (ρ = (1.572,1.572,1.763)D, a = (0.204,0.204,0.892)D), in tripod × ℝ: pinned [N]. The W5 value 0.97301 of the e3 scan is not optimal |
| K_{2,3}(1) + supply wire u₁u₂ of capacity ½ (5 parties) | 7/8 | 0.986750 [N: books and Toyoda] | 1 | distinct; symmetric book ρ = 3.041D; pinned [N] |
| 4-cycle with the two diagonals; C₅ with pentagram; octahedron with antipodal pairs; K_{2,4} with C₄ or a perfect matching on the 4-side | = f_cut | = f_cut | 1; ½; 2; 4/5, 4/3 | [R] flow = cut: no gain |
| K_{3,3}, demand = the six pairs inside the sides (6 parties; not two-apex) | 3/4 | ∈ [3/√10, 1] [R]; see below | 1 | open whether f_CAT(0) < 1 |

*K_{3,3}.* Lower bound [R]: apply Theorem 5 (w = 1) to the six sub-instances (two parties of one side, the three of the
other): each cross wire lies in 4 of them, each inside pair in 3 + 1: 4Σ_S ≥ (3/√10)·4·Σ_T, so f_CAT(0) ≥ 3/√10.
(In general f_CAT(0)(K_{3,3}) ≥ (3λ+η)/4 for every (λ,η) ∈ 𝒱₃; the proved part of 𝒱₃ gives its maximum 3/√10 at w = 1; S(9/10) of §5.4 would give 0.975 and (★) 51/52 = 0.9808.) Upper bound 1 from the cut {u₁, v₁}. The natural
product configuration (tripod × tripod, u's on the legs of one factor, v's on the legs of the other) has
R = 3/(2√2) = 1.0607 > 1; every metric of negative type (trees, Euclidean, ℓ₁) has R ≥ 1 because Σ c_ic_j d_ij ≤ 0
for c = ±1 on the two sides. Numerics (§8): no configuration below 1 found; [C] f_CAT(0)(K_{3,3}) = 1, which would
make K_{3,3} cut-pinned with f* = 1 unconditionally against routing 3/4.

---

## 7. P3: the three-angle inequality, analytically and with the sharp constant [R]

> **Theorem I.** For θ ∈ [−π/2, π/2]³ and every constant c ≥ 8,
>
>     F_c(θ) := Σ_{i<j} cos((θ_i−θ_j)/2)·√(1 + c sin²((θ_i+θ_j)/2)) ≥ 3.
>
> Equivalently, three points z_i on the half-ellipse x² + y²/b² = 1, x ≥ 0, with b ≥ 3 satisfy
> |z₁+z₂| + |z₁+z₃| + |z₂+z₃| ≥ 6. For c = 8 (b = 3) equality holds at θ = 0 and at (π/2, π/2, −π/2) and its images;
> for c < 8 the inequality fails at (π/2, π/2, −π/2), where F_c = √(1+c) < 3.

(I) of the note is c = 9 (b = √10).

*Proof.* Let s_i = sin θ_i, c_i = cos θ_i ≥ 0, b² = 1 + c ≥ 9. Then 2cos((θ_i−θ_j)/2)·√(1 + c sin²((θ_i+θ_j)/2))
= √((c_i+c_j)² + b²(s_i+s_j)²) = |z_i + z_j|. Let m = max|s_i|, say m = |s₁|.
(1) Σ_{i<j}|s_i+s_j| ≥ |(s₁+s₂) + (s₁+s₃) − (s₂+s₃)| = 2m.
(2) c_i ≥ √(1−m²), so Σ_{i<j}(c_i+c_j) = 2Σc_i ≥ 6√(1−m²).
(3) With (cos χ, sin χ) = (√(1−m²), m): |z_i+z_j| ≥ cos χ·(c_i+c_j) + b sin χ·|s_i+s_j|. Sum:
    Σ|z_i+z_j| ≥ 6(1−m²) + b·m·2m ≥ 6(1−m²) + 6m² = 6. ∎

This is Theorem D restricted to the slice σ_ji = −σ_ij (E = 0, hexagon lemma = (1)); it was found first and suggested
Theorem D. Lean: the trigonometric form for every c ≥ 8 with sharpness (`PortsLean/CLStar.lean`).

Remarks.
1. *Why the earlier attempts failed* (hull notes §3.5): they bounded each pair term separately or used one fixed
   linearisation. The proof needs the direction of the linearisation to depend on the configuration (through m),
   and the three s-sums to be used together.
2. *Coincidence worth recording:* for b = 3 the bound 6 is both three times the minor axis and the major axis 2b of
   the ellipse; the two equality cases are "all three at the co-vertex" and "two at one vertex, one at the other".
3. Near 0: F_c = 3 + θᵀQ_cθ + O(|θ|⁴) with Q_c = ((c−3)/8)·Id + ((c+1)/8)·J (J the all-ones matrix), eigenvalues
   (c−3)/8 (twice) and c/2 ([N-checked], `three_angle.py`; c = 9 gives 3/4, 3/4, 9/2). So the centre is a strict local minimum for every c > 3 (i.e. w < √3 in the weighted family,
   c = 9/w²), while the global inequality holds only for c ≥ 8 (w ≤ 3/(2√2) = 1.0607): between, the minimum is at the
   corner. With the absolute-value terms (Theorem D) the range shrinks to w ≤ 1, and with the refined calibration it
   extends (conjecturally) to w ≤ 5/4.
4. [N] `three_angle.py` (181³ grid): min F_c = 3.000000 for c = 9, 8.5, 8 and 2.9833, 2.9155 for c = 7.9, 7.5.

---

## 8. Numerical record and dead ends

**[N] record.**
- Books for K_{2,m}(1): §3.5. Weight scan: §5.1. Calibration checks: §3.2, §5.2. Steps of Theorems D, E: §3.3, §5.3.
- Two-apex scans: `scan2.py` (90 random instances with integer capacities/demands in {0,…,3}, m = 3, 4): all have
  f_flow = f_book = f_pod = f_cut within 10⁻⁶ (small integer data are almost always flow-tight), and for m = 3 the
  book value agrees with the Toyoda five-point optimisation (`tensorlab.min_ratio`, families triangle + box) up to
  the local optimiser's error (one start set stopped at 0.750164 against 0.75).
- `scan3.py` (48 instances: K_{2,3}(w) and K_{2,4}(w) with log-normal perturbations of all capacities and demands,
  spread 0.15, 0.4, 0.8, w ∈ [0.3, 3]): in all 48, f_book = f_pod = f_cut within 10⁻⁶; in 14 of them
  f_flow < f_cut (by up to 17%). So perturbed instances are typically *cut-pinned*: a cut drops below the W-type
  value as soon as the symmetry is broken by more than a few percent, and then (numerically) the cut is the CAT(0)
  minimum, which would make f* equal to the cut bound unconditionally. Three distinct values need near-symmetric
  data.
- Toyoda cross-checks (`tensorlab.min_ratio`, triangle + box, 3 × 400 starts), independent of the book reduction:
  scan #2 of §6.3: 0.965136; K_{2,3}(1) + supply u₁u₂ × ½: 0.986750; K_{2,3}(1.2): 0.928477 = 3/√(9+1.44) (Conjecture W at
  w = 1.2); K_{2,3}(2): 0.750000 (Theorem E). All agree with the book minima.

- K_{3,3} (`k33.py`, `k33_models.py`): flow 3/4, cut 1 ({u₁,v₁}). Relaxation by the necessary four-point (box)
  inequalities on six points, 240 feasible local minima from 240 starts: all at 1.06066 = 3/(2√2) (the
  tripod × tripod configuration, a strict local minimum); the local optimiser does not find the degenerate cut
  point 1.0 by itself. Model spaces: all tree topologies on six points: 1.0; star × ℝ: 1.0; star × star: 1.0607
  (local); star × star × ℝ: 1.0. No configuration below 1 was found, so the evidence is for f_CAT(0)(K_{3,3}) = 1
  (cut-pinned), i.e. for the inequality Σ_{i,j}|u_iv_j| ≥ Σ_{i<j}(|u_iu_j| + |v_iv_j|) for 3 + 3 points of a CAT(0) space
  [C]. It holds in every space of negative type; proved here only with the constant 3/√10 in front of the right side.

**[X] dead ends.**
1. Direct m-page calibration with the choice of §3.2: false for even m (§3.6).
2. Per-quadrilateral inequalities for (u₁,v_i,u₂,v_j): K_{2,2} is flow-tight (its valid region is λ′+η′ ≤ 2), so
   summing three of them gives only the flow bound 3λ + η ≤ 3.
3. Proving a point of the arc of 𝓔_m from other valid points by convexity: impossible, arc points are extreme.
   In particular the weighted theorem for w < 1 does not follow from w = 1 by convexity of 𝒱₃; it follows because
   the *calibrated* inequality is monotone in w (Φ_w ≥ Φ_1), which Theorem D makes explicit.
4. Monotonicity in λ of the refined bracket Br′/η along the arc: fails in the linear regime
   ((1 − λ|Q|/2)/√(1−λ²) is decreasing in λ for |Q|/2 > λ), so (CL\*\*₀) does not imply (CL\*\*).
5. Triangle-inequality bounds Σ_{i<j}|z_i+z_j| ≥ ½Σ_i|z_i + (z₁+z₂+z₃)| and ≥ ½Σ|z_i − z_j| for (I): each is tight at one
   of the two equality cases but both fail to second order along θ = (t,−t,0).
6. Lifting the configuration to Y × ℝ with heights and applying Theorem 5 there: gives weaker inequalities
   (the supply side grows).
7. One-vertex lemmas (V1),(V2) with a common α beyond λ₁: incompatible (§5.4).
8. ℓ₂-product closure of forced hulls as a general lemma (§6.1).

---

## 9. Next steps

1. Referee Theorem E (§5.2–5.3): it gives unconditional exact rates above routing. Then Lean for (V1), (V2), (X1), (X2).
2. (CL\*\*₀): either the two-vertex lemma of §5.4 or the certificate; it moves the threshold from 1.913 to 5/4 and
   settles K_{2,3}(w) and K_{2,4}(w) completely together with (CL\*\*).
3. Conjecture P (optimal books have their hubs on the spine): a proof would make every two-apex network pinned and
   reduce its conditional rate to a finite-dimensional minimisation.
4. K_{3,3}: decide whether f_CAT(0) < 1. If f_CAT(0) = 1 it is cut-pinned and f* = 1 unconditionally (routing 3/4).
5. Uniqueness of the minimiser in Theorem 5_w for w < 1 from the equality analysis of Theorem D (σ = 0 is forced;
   it remains to show that equality in (3.1) and (3.4) forces W5).
6. m ≥ 5 between 5m(m−1)/24 and w_c(m), and the cut regime for m ≥ 5: triples do not suffice; needs an m-page
   version of Theorem E (the refined bracket Br′ with (X1)/(X2)-type bounds for m pages).
