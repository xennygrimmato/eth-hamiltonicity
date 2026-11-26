# The tensor rate of the Okamura–Seymour network K_{2,3}: 3/√10 ≤ f*, with equality unless the contracting hypothesis holds

*Draft note, 26 November 2026. Self-contained. Status tags are defined in §0.3 and collected in §7.*

---

## 0. Statement, scope, provenance

### 0.1 The result

Parties u₁, u₂, v₁, v₂, v₃. Over a field k, let ⟨q⟩_{xy} be the wire of dimension q between parties x and y (the
q×q identity matrix in the indices of x and y; every other party holds a one-element index set). Put

    S = ⊗_{i∈{1,2}, j∈{1,2,3}} ⟨2⟩_{u_i v_j}          (supply: the six edges of K_{2,3}),
    T = ⟨2⟩_{v₁v₂} ⟨2⟩_{v₂v₃} ⟨2⟩_{v₁v₃} ⟨2⟩_{u₁u₂}     (demand: the three pairs on the 3-side, the pair on the 2-side),

and, with ≤ meaning restriction (s ≤ t iff s = (⊗_p A_p) t for linear maps A_p, one per party),

    f*(k) = f*(K_{2,3}; k) = sup { f : there are m_n with T^{⊗m_n} ≤ S^{⊗n} over k and m_n/n → f }.

The same rate f is required on all four demand wires. Write κ = 3/√10 = 0.948683298…

> **Theorem K.**
> 1. *(Unconditional; computer-assisted.)* f*(k) ≥ 3/√10 for every field k.
> 2. *(Conditional upper bound.)* If the contracting hypothesis of [AN] (Def. D.1) fails over k, then
>    f*(k) = 3/√10. Over an infinite field k the upper bound also holds for border protocols whose
>    approximation degree is 2^{o(n)}.
> 3. *(Consequence.)* Let k have characteristic 0. A protocol over k of rate > 3/√10 implies that the
>    contracting hypothesis holds over k. By the companion note [CE] this implies that 3-SAT on n variables is
>    decidable in time 2^{O(n^{1−δ})}·poly for some δ > 0. Hence, under the weak exponential-time hypothesis,
>    f*(k) = 3/√10. The status of this step is that of [CE]; see §5.
> 4. *(Small exact facts.)*
>    - No exact single-shot restriction achieves rate 1: wires of dimension D ≥ 2 cannot be converted into demand
>      wires of dimension D, over any field.
>    - At supply dimension 2, demand with all three v–v wires of dimension 2 is impossible, even as a border
>      restriction over ℂ.
>    - Every ℓ₁-embeddable pseudometric d has R(d) ≥ 1 (R as in §1.2). So none of the spectral points whose wire
>      metrics are explicitly known certifies any upper bound below 1.

For comparison:
- routing gives exactly 3/4;
- the cut bound is 1, and it is attained by a flattening rank, so f* ≤ 1 unconditionally;
- the quadrilateral inequality for prices alone gives only the strict inequality f* > 3/4 (an earlier step of this
  project; we know of no statement of this instance in the literature and have not searched it systematically).

Item 1 says that tensor restriction beats routing on these five parties by at least the factor 4/√10 ≈ 1.265.

### 0.2 What is not claimed

- **Scope of the theorem.** f* is the rate of exact asymptotic restriction, with uniform demand on the four
  wires. Item 1 is non-constructive.
- **No explicit protocol.** No explicit protocol of rate above 3/4 is known. Item 1 comes from Strassen's
  duality theorem, which proves that protocols exist and does not construct them. Numerical searches (§4.6) found
  nothing above 3/4 at the sizes tried.
- **No unconditional value.** If contracting holds over k, we know only f*(k) ∈ [3/√10, 1].
- **No claim that contracting holds or fails** over any field.
- **Border protocols.** Nothing is claimed for border protocols over finite fields, or over infinite fields
  when the approximation degree grows exponentially in n.
- **Non-uniform demands.** Nothing is claimed for demand vectors that differ from wire to wire. Each such vector
  is a different linear test (§1.2).
- **Uniqueness.** It is not proved that W5 (§2) is the unique minimiser in the five-point inequality (§3).
- **No unconditional algorithm or lower bound in complexity.** Item 3 is an implication between hypotheses.

### 0.3 Provenance and tags

**[AN]** is Anthropic, "VP ≠ VNP over every field" (November 2026), with a Lean development.
- The paper is machine-generated and has not been refereed by people. Its §3 says: "The proofs in this paper were
  found and written by AI. No human mathematician has checked the proofs."
- We have not built its Lean. We read the statements we use, and in places their Lean counterparts.
- Line numbers "l." refer to our pdftotext copy of the paper.

The imported facts are used as follows:
- **Item 1** uses only Strassen 1988 [Str88] and the CAT(0) property of prices. In [AN] that property is Theorem
  C.1 (`thm_cn`), packaged as Prop. C.3 (`prop_space`). We use it through Lemma C.4(a).
- **Item 2** additionally uses `thm_alt_rank_price` (from the proof of Theorem D.2), Prop. C.3 and Lemma C.4(f).
- **Items 1–2 use nothing from OpenAI's November 2026 papers.**
- **Item 3** uses the companion note [CE] (`note-contracting-eth.md`). One of its two routes uses OpenAI results;
  see §5.

Tags:
- **[P]**: proved here by hand, completely.
- **[P-ref]**: [P], and also checked by an internal referee (a named report).
- **[L]**: machine-checked in Lean in `research/ports/lean/` (Lean v4.36.0 with Mathlib; per `lean/NOTES.md` the
  files build with no `sorry` and no `axiom`).
- **[IV]**: verified by the interval certifier of §3.4.
- **[N]**: numerical evidence only.
- **[AN]**: quoted from [AN].
- **[cl]**: classical.
- **[C]**: conjecture.

---

## 1. Setup

### 1.1 Strassen duality for this instance [cl]

The tensors on the five parties over k, with direct sum, tensor product and restriction, form a preordered
semiring that satisfies Strassen's conditions. Let 𝒳 be its asymptotic spectrum: the functions F ≥ 0 on tensors
that are
- monotone under restriction,
- multiplicative under ⊗,
- additive under ⊕,
- normalised by F(⟨r⟩) = r on unit tensors.

Strassen [Str88] proved that a^{⊗n} ≤ b^{⊗(n+o(n))} iff F(a) ≤ F(b) for all F ∈ 𝒳.

For F ∈ 𝒳 put d_F(x,y) = log₂ F(⟨2⟩_{xy}). This is a pseudometric on the parties: F(⟨q⟩_{xy}) = q^{d_F(x,y)},
and ⟨2⟩_{xz} ≤ ⟨2⟩_{xy}⟨2⟩_{yz}. By multiplicativity,

    log₂ F(S) = Σ_S d_F := Σ_{i,j} d_F(u_i, v_j),     log₂ F(T) = Σ_T d_F := d_F(u₁,u₂) + Σ_{i<j} d_F(v_i, v_j).

Applying Strassen's theorem to a = T^{⊗p} and b = S^{⊗q} gives the rate formula

    f*(k) = inf_{F ∈ 𝒳, F(T) > 1} R(d_F),        R(d) := Σ_S d / Σ_T d.                                 (1.1)

The formula is an infimum, not a minimum. 𝒳 is compact, but it is not closed under F ↦ F^a. So
log F(S)/log F(T) may approach its infimum along points with F(T) → 1, and we do not know that the infimum is
attained in 𝒳 (review-fivepoint §0.3). Over the larger AN class of §1.2 the infimum is a minimum.

To get from rational rates to the sup in the definition of f*:
- take rationals p/q ↑ the infimum;
- S^{⊗n} ≥ S^{⊗n′} for n ≥ n′, because S ≠ 0 has the unit tensor 1 as a restriction;
- S ≥ ⟨2⟩ on all five parties (via a spanning tree of K_{2,3}), so ≤ S^{⊗(n+o(n))} and ≤ S^{⊗n} ⊗ ⟨2^{o(n)}⟩
  mean the same thing;
- a diagonal choice of sequences then finishes.

Strassen's theorem can be replaced by [AN] Theorem A.6 (`thm_duality`, l. 1164–1167). Under its hypothesis,
C^N is covered by 2^{εN} products of N factors from the A_β. A cover is a restriction of a direct sum, and
⟨2^{εN}⟩ ≤ S^{⊗εN}, so the same lower bound follows. The same formula with weights
covers non-uniform demands. A demand vector r tests Σ_e r_e d(e) ≤ Σ_S d, which is a different inequality.

### 1.2 Prices, and why the AN class is enough in both directions [P-ref]

[AN] Def. A.1 (l. 1058–1061): "A spectral point on I is a function φ ≥ 0 on the tensors on I such that φ(1) = 1,
such that φ(st) = φ(s)φ(t) for all tensors s and t, and such that φ(s) ≤ Σ_{j=1}^r φ(t_j) whenever s is covered
by t₁,…,t_r." Here "covered" means s = s₁ + ⋯ + s_r with s_j a restriction of t_j (l. 1028–1030).

By [AN] Lemma A.2, φ(⟨q⟩_{uv}) = q^{d_φ(u,v)}.

[AN] Def. A.4 (l. 1121–1129): "A price on a finite set V is a limit of functions c·d_φ, where c ≥ 0 is a real
number and φ is a spectral point on V. A function on the pairs of elements of an arbitrary set Y is a price if all
its pull-backs to finite sets are prices. […] Pull-backs, nonnegative multiples and pointwise limits of prices
are prices."

*(a) Every F ∈ 𝒳 is an AN spectral point.* If s = Σ_j s_j with s_j ≤ t_j, then s ≤ ⊕_j s_j. Each party maps its
direct-sum index space onto its original one by adding the blocks. So F(s) ≤ Σ_j F(s_j) ≤ Σ_j F(t_j). Hence each
d_F is an AN price.

*(b) Every AN price bounds every protocol.* Let d be a price on the five parties with Σ_T d > 0, and suppose
T^{⊗m} ≤ S^{⊗n}. For a spectral point φ, monotonicity, multiplicativity and A.2 give
2^{m Σ_T d_φ} = φ(T^{⊗m}) ≤ φ(S^{⊗n}) = 2^{n Σ_S d_φ}. This inequality is linear in the distances, so it survives
positive multiples and pointwise limits: m Σ_T d ≤ n Σ_S d. Hence f*(k) ≤ R(d).

*(c) Border protocols over infinite k.* Suppose (⊗_p A_p(ε)) S^{⊗n} = ε^e T^{⊗m} + O(ε^{e+1}), with the A_p
polynomial in ε of total degree D_n.
- Lagrange interpolation at D_n + 1 points of k writes T^{⊗m} as a combination of D_n + 1 restrictions of
  S^{⊗n}. The scalars are absorbed into one party's map.
- This is a cover, so 2^{m Σ_T d_φ} ≤ (D_n + 1)·2^{n Σ_S d_φ}.
- If D_n = 2^{o(n)}, the rate bound is unchanged. This holds for powers of a fixed single-shot border protocol,
  where D_n = O(n).

Together, (a) and (b) say: min over AN prices of R ≤ inf over 𝒳 = f* ≤ min over AN prices of R. The minimum over
AN prices is attained, because after normalising Σ_T d = 1 the prices form a compact set (Def. A.4, Tychonoff),
and the AN class is closed under φ ↦ φ^a. So f* = min over AN prices on the five parties. Consequently:
- a lower bound f* ≥ r may be proved for all AN prices on the five parties;
- an upper bound needs a single AN price.

Item (b) and the border clause are the argument of review-hull §6.

### 1.3 The CAT(0) input [AN]

[AN] §C.4 (l. 1597–1602): "A metric space is CAT(0) if it is complete and if any two of its points have a
midpoint that satisfies the CN inequality. A price space is a CAT(0) space whose metric is a price in the sense of
Definition A.4." The CN inequality (C.1), for a midpoint m of x, v, is |zm|² ≤ ½|zx|² + ½|zv|² − ¼|xv|².

- **Prop. C.3** (`prop_space`; l. 1608–1609): "Every price on a set V is the pull-back of the metric of a price
  space." Its proof rests on Theorem C.1 (`thm_cn`, "prices have nonpositive curvature") and Prop. A.8.
- **Lemma C.4(a)** (`lem_toolkit_a`; l. 1642–1644): "For x, v ∈ Y and t ∈ [0,1] exactly one point γ(t) has the
  distances t|xv| from x and (1−t)|xv| from v, and |zγ(t)|² ≤ (1−t)|zx|² + t|zv|² − t(1−t)|xv|² for every z ∈ Y."
- **Lemma C.4(f)** (`lem_toolkit`; l. 1658–1660): "Suppose that |xy| = |uv| = δ and |xu| = |yv| = h, that both
  diagonals of the quadrilateral x, y, v, u have the squared length δ² + h², and that a ∈ [x,u] and b ∈ [y,v] have
  |xa| = sh and |yb| = th. Then |ab|² = δ² + h²(s−t)²."

### 1.4 The contracting hypothesis [AN]

Mat_μ(F₂) is the additive group of μ×μ matrices over F₂. For a price on it, D(r)² is the mean of |a, a+W|² over
all a and all W of rank r.

Def. D.1 (`def_cases`; l. 1698–1702): "Contracting hypothesis: There are an integer μ ≥ 2 and a real number s with
1 ≤ s and s² < μ such that D(μ) ≤ s D(1) for all prices on Mat_μ(F₂)." Def. 2.1 states the same with spectral
points in place of prices. The two forms are equivalent, because the inequality is homogeneous and closed under
limits.

**`thm_alt_rank_price`** (`Paper/Alternative.lean`, l. 706–707 of that file; in the paper, Steps 1–7 of the proof
of Thm D.2 and Remark D.3):

    theorem thm_alt_rank_price (hK : ¬ Contracting K) (hμ : 3 ≤ μ) :
        ∃ w : Mt μ → Mt μ → ℝ, IsPrice K w ∧ ∀ a a', w a a' ^ 2 = (a - a').rank

Failure of the hypothesis is the universal statement "for all μ and s, some price violates the bound". So every
μ ≥ 3 is available. The proof needs μ ≥ 3 (l. 1760).

---

## 2. Upper bound: the hull lemma [P-ref]

### 2.1 Five matrices

In Mat₂(F₂) put

    n = 0,   s = I,   t₁ = e₁₁,   t₂ = e₂₁ + e₂₂,   t₃ = e₁₂ + e₂₂.

The relevant ranks:
- Rank one: t₁ = e₁e₁ᵀ, t₂ = e₂(e₁+e₂)ᵀ and t₃ = (e₁+e₂)e₂ᵀ. Also I − t₁ = e₂₂, I − t₂ = (e₁+e₂)e₁ᵀ and
  I − t₃ = e₁(e₁+e₂)ᵀ.
- Rank two: t₁ − t₂ = [[1,0],[1,1]], t₁ − t₃ = [[1,1],[0,1]], t₂ − t₃ = [[0,1],[1,0]], and I.

So under ρ₂(a,b) = √rk(a−b):

    |ns| = |t_i t_j| = √2 (i ≠ j),     |n t_i| = |s t_i| = 1.

The set N5 is the square root of the graph metric of K_{2,3}, with {n,s} as the 2-side. Facts about it:
- The rank table is [L] (`Hull.lean`: `ranks_one`, `ranks_two`, over `ZMod 2`).
- R(N5) = 6/(4√2) ≈ 1.06.
- N5 is ℓ₁-embeddable [N] and not Euclidean [P].
- The map a ↦ diag(a,0) pulls ρ₃ on Mat₃(F₂) back to ρ₂.

### 2.2 Lemma H

Let 𝕋 be the tripod with hub o and legs of length a/√2. The diamond is
D = {(ξ,σ) ∈ 𝕋 × ℝ : |ξo| + |σ| ≤ a/√2}, with the ℓ₂ product metric.

> **Lemma H.** Let Y be CAT(0) in the sense of §1.3, and let n, s, t₁, t₂, t₃ ∈ Y satisfy |ns| = |t_it_j| = √2·a
> and |nt_i| = |st_i| = a. Then there is an isometric embedding Ψ: D → Y with Ψ(o, ∓a/√2) = n, s and
> Ψ(tip_i, 0) = t_i.

*Proof.*

*Step 1 (solid squares).* Let |xy| = |yv| = |vu| = |ux| = a and |xv| = |yu| = √2·a. Let α(s) ∈ [x,u] and
β(s) ∈ [y,v] be the points at fraction s.
- C.4(f) with δ = h = a gives |α(s)β(t)|² = a²(1 + (s−t)²).
- For s ≠ s′, the four points α(s), α(s′), β(s′), β(s) again satisfy the hypotheses of C.4(f), with
  δ′ = a|s−s′| and h′ = a. Their diagonals have squared length a²(1 + (s−s′)²) = δ′² + h′².
- So the point Φ(s,r) at fraction r on [α(s), β(s)] satisfies |Φ(s,r)Φ(s′,r′)|² = a²((s−s′)² + (r−r′)²).

Thus Φ is a times an isometry of [0,1]², with corners x, u, y, v. Geodesics are unique by C.4(a), so the image is
convex, and its diagonals [x,v] and [y,u] meet at the common midpoint.

*Step 2 (one hub).* Apply Step 1 to (n, t_i, s, t_j) for each pair i ≠ j. Every square contains [n,s]. So
c := mid(n,s) = mid(t_i, t_j) for all pairs.

*Step 3 (triangles).* Δ_i := ∪_{p∈[n,s]} [t_i, p] is defined from geodesics alone. In Q_ij it is the t_i-half of
the square. Two isometric parametrisations of Δ_i, from Q_ij and from Q_ik, agree on the three non-collinear
vertices, hence everywhere.

*Step 4 (gluing).* Put Ψ(ξ,σ) = ψ_i(|ξo|, σ) for ξ on leg i.
- Points on one leg lie in the flat triangle Δ_i.
- Points on legs i ≠ j lie in the flat square Q_ij = Δ_i ∪ Δ_j, at distance √((τ+τ′)² + (σ−σ′)²). This is the
  distance in 𝕋 × ℝ. ∎

Only C.4(a),(f) are used. Of [AN] D.2 Step 8 the one-square case is redone here, not cited.

### 2.3 From Lemma H to the rate

W5(ℓ,h) is the five-point metric with v_j at distance ℓ from the hub on leg j at height 0, and u₁, u₂ at the hub at
heights ±h:

    |u_k v_j| = √(ℓ² + h²),   |v_i v_j| = 2ℓ,   |u₁u₂| = 2h,   R(W5(ℓ,h)) = 6√(ℓ²+h²)/(6ℓ+2h).

- Its minimum over h is 3/√10, attained only at h = ℓ/3, because 6√(ℓ²+h²)·√10 − 3(6ℓ+2h) ≥ 0 reduces to
  4(ℓ−3h)² ≥ 0. This is [L] (`W5.lean`: `ratio_lower`, `ratio_at_third`, `ratio_strict`, `w5_ratio`).
- W5(ℓ,h) ⊂ D whenever max(ℓ,h) ≤ a/√2. This is the referee's relaxation of the condition ℓ + h ≤ a/√2 in our
  first draft.

> **Corollary H.** If contracting fails over k, then W5(ℓ,ℓ/3) is a price over k, and f*(k) ≤ 3/√10. The bound
> extends to border protocols as in §1.2(c).

*Proof.*
1. `thm_alt_rank_price` with μ = 3 gives the price ρ₃. Pulling back along a ↦ diag(a,0) gives ρ₂, hence N5.
2. By Prop. C.3, N5 sits isometrically in a price space Y.
3. Lemma H embeds D, so the five points of W5(ℓ,ℓ/3) lie in Y.
4. The metric of Y is a price, so its pull-back to these five points is a price. Rescale.
5. Apply §1.2(b). ∎

A point about Step 4: Prop. C.3 says the metric of the **whole** price space is a price. So points of Y outside
the image of N5 also carry prices, and no separate statement about convex hulls is needed (review-hull §2).

Equivalences:
- [P] N5 is a price over k ⇔ every finite subset of (tripod with infinite legs) × ℝ is a price over k. For ⇒,
  any finite subset fits in a diamond after translation and scaling.
- [P, not refereed] Also ⇔ W5(ℓ,ℓ/3) is a price. This direction uses flat-quadrilateral rigidity [BH99, II.2.11],
  which is not in [AN]'s toolkit.

---

## 3. Lower bound: every five-point CAT(0) configuration has R ≥ 3/√10

> **Theorem 5.** Let u₁, u₂, v₁, v₂, v₃ be points of a CAT(0) space (§1.3) with Σ_T > 0. Then Σ_S ≥ κ Σ_T, with
> equality for W5(ℓ,ℓ/3).

By §1.2(a) and Prop. C.3, every d_F with F ∈ 𝒳 is the restriction of the metric of a CAT(0) space to five
points. With (1.1) this gives Theorem K.1. The same holds for every AN price on five parties, over any field.
Theorem 5 is the combination of three steps:
- §3.1: reduction to books [P-ref];
- §3.2: calibration [P-ref; also checked numerically];
- §3.3: the inequality (CL*) [IV].

The referee's final report (review-fivepoint.md) found no gap, fatal or repairable, in the chain C.3 → C.4(a) →
(3.1) → Prop. 3.2 → (CL*) → duality.

Write D = |u₁u₂|, A_i = |u₁v_i| and B_i = |u₂v_i|.

### 3.1 Reduction to books

*Passing to a price space.* Start from a price d on the five parties. By Prop. C.3, d is the pull-back of the
metric of a price space Y, which is CAT(0). The pull-back may identify points, which is harmless. From now on,
u₁, …, v₃ denote the image points in Y, so the segment [u₁,u₂] and its points c_t exist. For an abstract
five-point price they need not.

If D = 0, then u₁ = u₂ in Y, so B_i = A_i and Σ_T = Σ_{i<j}|v_iv_j| ≤ Σ_{i<j}(A_i + A_j) = 2ΣA_i = Σ_S. Hence
R ≥ 1. Let D > 0, and let c_t ∈ Y be the point at fraction t of [u₁,u₂]. By C.4(a) with z = v_i, x = u₁ and
v = u₂,

    |v_i c_t|² ≤ (1−t)A_i² + tB_i² − t(1−t)D² =: h_i(t)²,

where h_i(t) is the apex-to-base distance in the Euclidean triangle with sides D, A_i, B_i (Stewart's theorem).
The triangle inequality in Y through the same point c_t, used for both i and j, gives

    |v_iv_j| ≤ min_{t∈[0,1]} (h_i(t) + h_j(t)) =: d^Z_ij.                                              (3.1)

This inequality is the only thing used below. Put Σ_T(Z) := D + Σ_{i<j} d^Z_ij. Since Σ_S and D are unchanged and
Σ_T ≤ Σ_T(Z), it suffices to prove Σ_S − κ Σ_T(Z) ≥ 0. This quantity depends only on the six numbers A_i, B_i and
on D. Degenerate pages (ρ_i = 0, or v_i = u_k) need no special treatment.

*Remark (not used).* Let Z, the **book**, be three Euclidean comparison triangles (ū₁, ū₂, v̄_i) glued along the
common side, the spine. Then d^Z_ij is the distance of v̄_i and v̄_j in Z. We use this only as language.

### 3.2 Calibration (complete computation)

*Coordinates.* In page i use (ρ,a): ρ ≥ 0 is the distance from the line of the spine and a is the height along it.
- u₁ = (0,0), u₂ = (0,D), v_i = (ρ_i, a_i).
- The foot a_i may lie outside [0,D].
- Spine points are c(y) = (0,y), y ∈ [0,D].
- Then A_i = |(ρ_i, a_i)|, B_i = |(ρ_i, a_i − D)|, and f_i(y) := |v_i − c(y)| = h_i(y/D).

*Hubs and exit vectors.* For i ≠ j let y_ij = y_ji ∈ [0,D] minimise the convex function g_ij = f_i + f_j, so that
d^Z_ij = f_i(y_ij) + f_j(y_ij). Let e_ij = (cos ψ_ij, sin ψ_ij) =: (c_ij, σ_ij), with ψ_ij ∈ [−π/2, π/2], be the
unit vector of v_i − c(y_ij) in page i. Its first coordinate ρ_i/f_i is ≥ 0.
- Where f_i(y_ij) > 0, f_i′(y_ij) = −σ_ij.
- If v_i = c(y_ij), the subdifferential of f_i there is [−1,1]. Choose σ_ij ∈ [−1,1] so that the optimality
  condition below holds, and put c_ij = √(1−σ_ij²). (The ρ_i c_ij term then vanishes.)

With ε_ij := σ_ij + σ_ji, so that −ε_ij is a (sub)gradient of g_ij, first-order optimality reads:

    y_ij ∈ (0,D):  ε_ij = 0;      y_ij = D:  ε_ij ≥ 0;      y_ij = 0:  ε_ij ≤ 0.                        (3.2)

In each case f_i(y_ij) = ⟨e_ij, v_i − c(y_ij)⟩ = ρ_i c_ij + (a_i − y_ij) σ_ij, and y_ij ε_ij = D ε_ij·[y_ij = D].
Put E₂ = Σ_{pairs with y_ij = D} ε_ij ≥ 0 and E₁ = Σ_{pairs with y_ij = 0} |ε_ij| ≥ 0. Then Σ_{i<j} ε_ij = E₂ − E₁
and Σ_{i<j} |ε_ij| = E₁ + E₂. Summing over the three pairs, with {j,k} the two indices other than i,

    Σ_{i<j} d^Z_ij = Σ_i (ρ_i P_i + a_i Q_i) − D E₂,     (P_i, Q_i) := e_ij + e_ik,     Σ_i Q_i = E₂ − E₁.     (3.3)

*Calibrating the supply.* By Cauchy–Schwarz, for any angles α_i and β_i,

    A_i ≥ ρ_i cos α_i + a_i sin α_i,        B_i ≥ ρ_i cos β_i + (D − a_i) sin β_i,                          (3.4)

where the second uses the unit vector (cos β_i, −sin β_i).

*Choice of angles.* Put μ_i = (ψ_ij + ψ_ik)/2 and δ_i = (ψ_ij − ψ_ik)/2, both in [−π/2, π/2]. Then

    (P_i, Q_i) = 2 cos δ_i (cos μ_i, sin μ_i),   with t_i := cos δ_i ∈ [0,1].

Put ν_i = arccos(κ t_i) ∈ (0, π/2], so ν_i ≥ 0 (note κ t_i ∈ [0, κ] ⊂ [0,1)). Set α_i = ν_i + μ_i and
β_i = ν_i − μ_i. The identities below hold for either sign of ν_i; the choice ν_i ≥ 0 makes M_i ≥ 0, which is the
better bound. The sum-to-product formulas give

    cos α_i + cos β_i = 2 cos ν_i cos μ_i = κ P_i,
    sin α_i − sin β_i = 2 cos ν_i sin μ_i = κ Q_i,
    sin β_i = sin ν_i cos μ_i − cos ν_i sin μ_i = M_i − κQ_i/2,     M_i := cos μ_i √(1 − κ² cos² δ_i) ≥ 0.

*Sum.* Add (3.4) over i and insert these identities and (3.3):

    Σ_S ≥ Σ_i [ρ_i(cos α_i + cos β_i) + a_i(sin α_i − sin β_i) + D sin β_i]
        = κ Σ_i (ρ_i P_i + a_i Q_i) + D Σ_i (M_i − κQ_i/2)
        = κ (Σ_{i<j} d^Z_ij + D E₂) + D Σ_i M_i − (κD/2)(E₂ − E₁).

Subtracting κ Σ_T(Z) = κ(D + Σ d^Z_ij):

    Σ_S − κ Σ_T(Z) ≥ D (Σ_i M_i − κ + (κ/2)(E₁ + E₂)).

Finally √10·κ = 3 and √10·M_i = cos μ_i √(10 − 9cos²δ_i) = cos μ_i √(1 + 9 sin²δ_i).

> **Proposition 3.2.** For every book, Σ_S − κ Σ_T(Z) ≥ (D/√10)·Φ(ψ), where
> ψ = (ψ₁₂, ψ₁₃, ψ₂₁, ψ₂₃, ψ₃₁, ψ₃₂) and
>
>     Φ(ψ) = Σ_{i=1}^{3} cos μ_i √(1 + 9 sin² δ_i) − 3 + (3/2) Σ_{i<j} |sin ψ_ij + sin ψ_ji|,
>
> with μ_i, δ_i the half-sum and half-difference of the two exit angles at v_i.

No relation between the six angles is used, except that each lies in [−π/2, π/2]. So Φ ≥ 0 on the whole cube
[−π/2, π/2]⁶ suffices for every hub pattern: interior hubs, and paths through u₁ or u₂.

Nothing in the computation requires v_i to be off the spine. If f_i(y_ij) = 0, the choice σ_ij = −σ_ji (or 0
if both vanish) satisfies (3.2), and the identity f_i(y_ij) = ρ_i c_ij + (a_i − y_ij)σ_ij still holds.

Checks:
- **Referee [P-ref].** The referee recomputed every line (review-fivepoint §2) and confirmed that all ρ_i and
  a_i terms cancel.
- **Referee's numerics [N].** 200 000 random books, about 200 000 pairs of each hub type, including ρ = 0, v_i = u_k
  and near-W5 books. Minimum slack [Σ_S − κΣ_T(Z)] − (D/√10)Φ = +1.5·10⁻⁵, with no violation. Minimum R(book) =
  0.948687.
- **Further numerics [N].**
  - The author's 20 000 books had minimum excess 0.0058·D.
  - A re-implementation for this note ran 20 000 books with minimum excess 0.020·D.
  - A careless subgradient at a hub on the spine (σ_ij = 0 instead of the choice above) produces apparent
    violations. So the choice in (3.2) is necessary, not cosmetic.

### 3.3 Inequality (CL*) and its certificate

> **(CL*)** Φ(ψ) ≥ 0 for all ψ ∈ [−π/2, π/2]⁶.

*Algebraic form [P].* Substitute σ = sin ψ ∈ [−1,1] and c = cos ψ = √(1−σ²) ≥ 0. Since cos μ_i ≥ 0,

    (c_ij + c_ik)² + 10(σ_ij − σ_ik)² = 4 cos² μ_i (cos² δ_i + 10 sin² δ_i) = 4 cos² μ_i (1 + 9 sin² δ_i),

so (CL*) is exactly equivalent to

    Φ(σ) = ½ Σ_i √((c_ij + c_ik)² + 10(σ_ij − σ_ik)²) − 3 + (3/2) Σ_{i<j} |σ_ij + σ_ji| ≥ 0   on [−1,1]⁶.   (3.5)

No transcendental function and no enclosure of π are involved, and the domain box is exact in binary64.

*The slice (I).* Put ψ_ji = −ψ_ij (all hubs interior), with θ₁ = ψ₁₂, θ₂ = −ψ₁₃ and θ₃ = ψ₂₃. Then (CL*)
becomes the three-angle inequality

    F(θ) = Σ_{i<j} cos((θ_i−θ_j)/2)·√(1 + 9 sin²((θ_i+θ_j)/2)) ≥ 3   on [−π/2, π/2]³.                    (I)

Equivalently: for three points z_i = (cos θ_i, √10 sin θ_i) on the half-ellipse x² + y²/10 = 1, x ≥ 0,
|z₁+z₂| + |z₁+z₃| + |z₂+z₃| ≥ 6. Near 0, F(θ) = 3 + θᵀQθ + O(|θ|⁴) with Q = (3/4)·Id + (5/4)·J, which has
eigenvalues 3/4, 3/4, 9/2 [P]. (I) has its own certificate (`hull3`) and is also implied by (CL*).

*Covering of [−1,1]⁶ used by the certificate.* The source is `tools/ivcert/src/problems/clstar.rs`.

1. **Main certificate `clstar:rho=0.5`** on [−1,1]⁶ in the σ-coordinates (3.5). Each leaf box is closed by one of
   the following tests:
   - natural interval extension;
   - mean-value form;
   - second-order Taylor form;
   - certified convexity, with an anchor point and a positive-definiteness certificate for the Hessian enclosure;
   - **excluded** (X), meaning closed by item 2 or item 3 below.

   The certificate exists in two versions:
   - with pruning by the symmetry group S₃ × {±1}: 92 195 leaves;
   - without any symmetry pruning: 528 970 leaves.

   The version without pruning suffices on its own, so the symmetry reduction is not part of the trust base.

2. **Central cube.** X-leaves inside [−½, ½]⁶ are covered by eight certificates `clnear:rho=0.5:s=±±±`. Their
   coordinates are a_k = (σ_ij − σ_ji)/2 and e_k = (σ_ij + σ_ji)/2, for k ∈ {12, 13, 23}, on the orthant boxes
   a ∈ [−½, ½]³, s_k e_k ∈ [0, ½].
   - Every point of the σ-cube [−½, ½]⁶ has (a,e) ∈ [−½, ½]⁶. So it lies in one of the eight orthant boxes, and
     σ = (a+e, e−a) ∈ [−1,1]⁶ [P].
   - On an orthant box, |σ_ij + σ_ji| = 2 s_k e_k, so Φ is smooth there.
   - The equality point 0 is a corner of every orthant box. It is closed by a **gain test**. In the e-block,
     Φ − Φ(0) is bounded below by the linear term 3 Σ_k s_k e_k = 3|e|₁ minus certified second-order terms. In the
     a-block, the Hessian is certified positive definite (it is the Hessian of (I) up to a linear change of
     variables). The bracket inequality behind the test is stated and derived in the header of `lb_gain_h`,
     `src/bnb.rs` [P].
   - Leaf counts: 8 608 to 11 685 per orthant.

3. **Six corner regions (analytic lemma) [P].** These are the boxes with s·σ_jk ≥ 15/16 and s·σ_kj ≥ 15/16 for a
   pair {j,k} and a sign s.
   - Put d₁ = 1 − sσ_jk and d₂ = 1 − sσ_kj, both in [0, 1/16].
   - Each vertex term is ≥ 0. The vertex term at j is ≥ c_jk/2 = √(d₁(2−d₁))/2 ≥ √d₁/2, and similarly at k.
   - |σ_jk + σ_kj| = 2 − d₁ − d₂, and the other two |ε| are ≥ 0.
   - Hence Φ ≥ (√d₁ + √d₂)/2 − 3 + (3/2)(2 − d₁ − d₂) = (√d₁ + √d₂)/2 − (3/2)(d₁ + d₂) ≥ 0, because 3d ≤ √d for
     d ≤ 1/9 and 1/16 < 1/9.

**Covering argument (outside the checker) [P-ref].**
- `clstar` is a bisection tree on [−1,1]⁶. The checker rebuilds every leaf box from the tree, so the leaves
  cover [−1,1]⁶ structurally. Each leaf is of one of three kinds:
  - closed by an interval test, so Φ ≥ 0 on the box;
  - an X-leaf, lying wholly in [−½, ½]⁶ or wholly in one of the six corner regions. The region tests are exact in
    floating point, since ½ and 15/16 are dyadic;
  - (only in the symmetric version) a P-leaf, lying wholly outside the closed fundamental domain
    {w₁ ≥ w₂ ≥ w₃, w₁ + w₂ + w₃ ≥ 0}, where w_i = σ_ij + σ_ik. Pruning uses only certain strict violations.
- Points of [−½, ½]⁶ are covered by the eight `clnear` certificates, which cover more than the central cube.
- Points of the corner regions are covered by the corner lemma.
- The symmetry, in the symmetric version only:
  - Φ is invariant under S₃ acting by σ_ij ↦ σ_{π(i)π(j)} and under σ ↦ −σ.
  - Every orbit meets the fundamental domain: sort the w_i, and if their sum is < 0, flip and sort again.
  - The excluded regions need not be invariant, because `clnear` and the corner lemma cover their regions
    entirely.
- The version without symmetry pruning also verifies. So the symmetry argument is not needed.

Every certificate is re-checked by the separate binary `ivcheck`, which performs no search. The lead re-ran
`run_proofs.sh` (regenerate and check). For this note, `ivcheck` was re-run on all twelve certificate files in
`tools/ivcert/certs/`, and all report VERIFIED.

*Trust base of item 1, as listed by the referee (review-fivepoint §8).*
1. [AN] Theorem C.1 (`thm_cn`) and Prop. C.3, with Lemma C.4(a). The direction used is price ⇒ CAT(0)
   embedding. C.4(a) is a standard CAT(0) fact.
2. Strassen's spectral theorem for the semiring of five-party tensors over k [Str88]. Alternatively, [AN]
   Theorem A.6 with the cover-to-restriction step of §1.1.
3. §3.1 and Prop. 3.2. These are elementary; the referee recomputed them line by line and tested them on 200 000
   books.
4. (CL*): the ten certificates checked by `ivcheck`, plus the corner lemma and the covering argument written out
   above.
5. Not needed: Reshetnyak gluing, Toyoda's theorem, uniqueness of the minimiser, anything from OpenAI.

**The weakest point is item 4.** The prover and the checker share one Rust implementation. `ivcheck` is
independent of the search but not of the implementation. The referee verified the encoding of Φ by hand and only
spot-checked the rounding and gain-test code. An independent second checker, using a different arithmetic
library, is being built. It is not finished, and nothing in this note relies on it.

The shared implementation in detail:
- **Floating point.** IEEE-754 binary64 round-to-nearest for + − × ÷ √, and a correctly rounded fused
  multiply-add, on the machine used. Outward rounding is done by error-sign tests (TwoSum, and fma residuals), with
  unconditional widening below 10⁻²⁸⁰.
- **The Rust source of `ivcert`**, and the Rust compiler and standard library. The source comprises:
  - interval arithmetic (`interval.rs`);
  - forward-mode first- and second-order automatic differentiation (`ad.rs`);
  - positive-definiteness certification (`linalg.rs`);
  - the leaf tests and the gain test (`bnb.rs`);
  - certificate parsing and structural box reconstruction (`cert.rs`);
  - the problem definitions (`clstar.rs`), including the predicates `excluded` and `outside_fundamental`.
- **What "independent" means for the checker.** `ivcheck` shares all of this code with the prover. It is
  independent of the search, not of the arithmetic. Coverage of the domain is structural: boxes are rebuilt from
  the bisection tree, and the domain recorded in the header is compared with the problem definition.
- **The hand steps:** the sine substitution (3.5); the orthant covering of the central cube; the corner lemma; and
  the derivation of the gain-test bound.
- **Review status.** Beyond the referee's hand check of the encoding and spot checks, and the unit tests
  (`tests/known.rs`), the code has not been reviewed.

### 3.4 Equality cases

- At W5(ℓ,ℓ/3), in book coordinates D = 2ℓ/3, ρ_i = 3D/2 and a_i = D/2:
  - all hubs are at D/2 and all ψ = 0;
  - the calibrating vectors (cos α_i, sin α_i) = (3,1)/√10 and (cos β_i, −sin β_i) = (3,−1)/√10 are the true
    directions u₁→v_i and u₂→v_i;
  - every inequality in §3.1–3.2 is an equality;
  - Σ_S = 3√10·D and Σ_T = 10·D.
- The six cube corners also give Φ = 0: for one vertex i and one sign s, ψ_ij = ψ_ik = −sπ/2 and the other four
  angles equal +sπ/2, so the pair {j,k} carries |ε| = 2.
  - These are collinear books, where R ≥ 1 and the slack is (1 − κ)Σ_T > 0.
  - They are equality cases of the relaxation Φ ≥ 0, not of Theorem 5.
- No other zeros of Φ were found [N]:
  - 2·10⁷ random points, 800 local searches and 2 differential-evolution runs (referee);
  - 3 000 + 6 000 local searches and 2·10⁶ random points (author).

  Near 0, Φ grows quadratically; near the corners it grows linearly, with slope about ½. Searches over books
  found the minimum only at W5.
- **Uniqueness** of the minimiser in Theorem 5 is not proved. If Φ has no other zeros, equality in Theorem 5
  forces ψ = 0 together with equality in (3.1) and (3.4). But that hypothesis is numerical, so uniqueness remains
  a conjecture ([C], §8).

### 3.5 Remark: what kind of inequality this is

The quadrilateral (Reshetnyak) inequalities of C.4(b), together with the triangle inequalities, give only
min R = 0.944606… [N]. This is a root of 58x³ − 14x² − 29x − 9, found by PSLQ at 60 digits. So Theorem 5 genuinely
uses C.4(a) at t ≠ ½, in the book reduction.

### 3.6 Independent numerical cross-checks [N]

These come from `research/ports/e3/notebook.md`.
- **Toyoda's five-point criterion.** Toyoda (arXiv:1907.09074, Thm 1.3): a metric space with at most five points
  embeds isometrically in a CAT(0) space iff it satisfies the Gromov–Sturm box inequalities. Minimising R under
  these as a semi-infinite program gave 0.948683298050505 at W5 in 1000 of 1000 multistarts, with KKT residual
  10⁻¹⁵. The active constraints are the three box inequalities for the cycles (u₁, v_i, u₂, v_j) at (t,s) = (½,½).
- **Model spaces.** Minimising R over products of two or three trees, and over the Euclidean cone over the Heawood
  graph, gave 3/√10 at W5. Single trees and Euclidean spaces give 1.
- **Protocol searches.** Alternating least squares and Levenberg–Marquardt searches looked for restrictions.
  - They were run single-shot at uniform supply wire dimension 2 to 5 (2 → 2, 4 → 3 over ℝ and ℂ, 5 → 4 over ℝ with
    fewer starts) and on non-uniform demand vectors at dimension ≤ 4. Several supply copies, dimension ≥ 6 and
    structured constructions were not tried.
  - They found no protocol of rate above 3/4. The best relative residual at a rate above 3/4 was 0.64 (4 → 3).
  - The smallest uniform single-shot sizes above 3/√10 are 10 → 9 (rate log 9/log 10 ≈ 0.954) and 11 → 10. These
    were out of reach of the dense code.
  - So the protocols whose existence §1.1 guarantees for every rate below 3/√10 are **not known explicitly** at any
    rate above 3/4.

---

## 4. Proof of Theorem K, items 1–2

**Item 1.** For F ∈ 𝒳 with F(T) > 1:
- d_F is an AN price (§1.2(a));
- by Prop. C.3 it is the restriction to five points of the metric of a CAT(0) space;
- by Theorem 5 (§3.1 + §3.2 + (CL*)), R(d_F) ≥ κ.

By (1.1), f*(k) ≥ κ, as an infimum over 𝒳. This holds over every field. [AN] l. 564–567 says that "the field only
supplies the scalars", and Strassen's theorem holds over every field.

**Item 2.** Corollary H gives f*(k) ≤ κ, with border protocols as in §1.2(c). Item 1 gives equality. ∎

---

## 5. Consequences and the falsifiable prediction

**(i)** By Corollary H, a protocol over k of rate > 3/√10 shows that W5, and hence N5, ρ₂ and ρ₃, are not prices
over k. So Contracting(k) holds [P-ref]. A protocol over ℚ also counts over ℝ, ℂ and ℚ̄.

**(ii)** If char k = 0, Contracting(k) implies 3-SAT in 2^{O(n^{1−δ})}·poly, by [CE]. Two routes:
- **Theorem R** uses [AN] only. In the non-uniform form (advice of size poly(n)) it is refereed
  (review-theoremR.md). The uniform form rests on a one-reader audit of [AN]'s Lean proof terms
  (review-uniformity.md), not on a Lean theorem.
- **Theorem A** (contracting ⇒ ports; refereed, review-theoremAB.md) uses [AN] F.6 and OpenAI's HC Thm 4.2. The
  step from ports to 3-SAT then uses OpenAI's IM Thm 7.1, which we have not reviewed.

**(iii) Prediction.** Under the non-uniform weak exponential-time hypothesis, the following holds via Theorem R in
its refereed form. Under the uniform Weak ETH it holds via the audit or via Theorem A + IM 7.1.

> For every field k of characteristic 0, no asymptotic restriction protocol from the six binary wires of K_{2,3}
> to the four demand wires has rate above 3/√10 = 0.948683…. The same holds for border protocols of
> approximation degree 2^{o(n)}. Rates arbitrarily close to 3/√10 are attained (unconditionally, by item 1).

The prediction can be refuted by an explicit object. For example, a single restriction over ℚ from wires of
dimension 10 on the six edges to wires of dimension 9 on the four demand pairs (rate ≈ 0.954) would refute it. So
would any power or tensor combination with rate > 3/√10. Such a restriction would imply Contracting(ℚ), and with
[CE] a 2^{O(n^{1−δ})} algorithm for 3-SAT.

**(iv) Product closure.** If f*(k) > 3/√10, then tripod × segment is not a price space over k, although tripod and
segment are. So ℓ₂ products of spectral spaces are then not always spectral [P].

---

## 6. Small exact facts (Theorem K.4)

**(a) Rate 1 single-shot is impossible [P] (from the e3 notebook, re-derived here).** Suppose
(⊗_p A_p) S_D = T_D, where every supply and demand wire has dimension D ≥ 2, over any field.
1. Each cut {v_i} has flattening rank D² on both sides, so each A_{v_i} is invertible.
2. Then (A_{u₁} ⊗ A_{u₂}) S_D = (⊗_i A_{v_i}⁻¹) T_D. The left side is M₁ ⊗ M₂, where M_k is A_{u_k} applied to the
   three wires at u_k.
3. For M₁ ⊗ M₂ (with M₂ ≠ 0), the flattening rank across {u₁} equals rk_{u₁}(M₁). The rank across {u₁,u₂} equals
   rk_{u₁}(M₁)·rk_{u₂}(M₂) ≥ rk_{u₁}(M₁).
4. Invertible maps at the v's preserve both ranks. For T_D they are D and 1.

So D ≤ 1, a contradiction. The same argument excludes every instance in which the v-cuts are tight and the
u₁u₂ wire has dimension ≥ 2.

**(b) Bond dimension 2, border, over ℂ [P].** Suppose S₂ degenerates to a tensor with v₁v₂ = v₂v₃ = v₁v₃ = 2 (any
dimension on u₁u₂).
1. Compose with the functional e₁* at u₁ and at u₂. The target becomes the 2×2 matrix multiplication tensor
   ⟨2,2,2⟩ on v₁, v₂, v₃.
2. The source becomes (⊗A_v(ε))(X(ε) ⊗ Y(ε)), with X, Y ∈ (ℂ²)^{⊗3}. Its border rank is ≤ 2·2 = 4.
3. The set of tensors of border rank ≤ 4 is closed, but the border rank of ⟨2,2,2⟩ is 7 [Lan06].

**(c) ℓ₁ metrics [P; L].** For a cut metric δ_X, let a = |X ∩ {u₁,u₂}| and b = |X ∩ {v₁,v₂,v₃}|. The cut crosses
a(3−b) + (2−a)b supply pairs and [a = 1] + b(3−b) demand pairs.
- a = 0: 2b supply against b(3−b) demand.
- a = 1: 3 supply against 1 + b(3−b) ≤ 3 demand.
- a = 2: by complementation, as for a = 0.

So each cut has Σ_S ≥ Σ_T, and so does every nonnegative combination. Hence R ≥ 1 on the cut cone. This is [L]
(`W5.lean`: `cut_ineq`, all 32 cuts; `w5_not_cut_combination`). The cut {v₁} attains 1 (`cut_v1`), and so
f* ≤ 1, since a flattening rank is a spectral point.

Which explicit spectral points have ℓ₁ wire metrics [K] (`ideas-ports.md` §4.1):
- flattening ranks give cut pseudometrics;
- Strassen's support functionals (every field) give star metrics d(x,y) = θ_x + θ_y = Σ_z θ_z δ_{{z}}(x,y);
- the quantum functionals of Christandl–Vrana–Zuiddam (over ℂ) give star metrics.

Products of spectral points add their metrics. None of these certifies an upper bound below 1.

**(d) Routing [P; L].**
- *Routing achieves 3/4.* Send each v_iv_j half through u₁ and half through u₂, and send u₁u₂ through v₁, v₂, v₃, a
  third through each. Edge loads are f(½ + ½ + ⅓) = 4f/3, so f = 3/4. The matching dual inequality,
  3Σ_T d ≤ 4Σ_S d for every pseudometric, is [L] (`flow_bound`).
- *Routing does no better.* The path metric of K_{2,3} has R = 6/8 = 3/4.

---

## 7. Status table

| Step | By hand | Referee | Lean | Interval | Numerical |
|---|---|---|---|---|---|
| (1.1) rate formula from Strassen 1988 | [cl] | — | — | — | — |
| §1.2(a) 𝒳 ⊂ AN spectral points; (b) prices bound protocols; (c) border over infinite k, degree 2^{o(n)} | [P] | review-hull §6 (b, c) | — | — | — |
| Prop. C.3, C.4(a),(f), thm_cn, thm_alt_rank_price | [AN] | not refereed by people; Lean by [AN], not built by us | [AN] | — | — |
| Rank table of the five matrices | [P] | review-hull §1 | `ranks_one`, `ranks_two` | — | yes |
| Lemma H (flat squares, triangles, gluing) | [P] | review-hull §§3–5: correct | **no** (a hypothesis `lemmaH` in `Hull.lean`; Mathlib has no CAT(0) theory) | — | model check |
| tripod × ℝ model of N5, W5 ⊂ diamond | [P] | review-hull §5 | `model_n5`, `w5_in_diamond` | — | yes |
| Glue: ρ₂ price ⇒ W5 price, from explicit hypotheses (prop_space, pull-back, Lemma H) | [P] | review-hull §2 | `w5_price_of_rho_price` | — | — |
| R(W5(ℓ,h)) ≥ 3/√10, minimum only at h = ℓ/3 | [P] | review-hull §5 | `ratio_lower`, `ratio_at_third`, `ratio_strict`, `w5_ratio` | — | yes |
| Corollary H (¬Contracting ⇒ f* ≤ 3/√10) | [P] | review-hull: "no fatal gap" | glue only | — | — |
| §3.1 book reduction (after C.3) | [P] | review-fivepoint §1: correct | no | — | yes |
| §3.2 calibration, Prop. 3.2 | [P] | review-fivepoint §2: correct, recomputed | no | — | 200 000 books (referee), 2 × 20 000 (author, this note) |
| (3.5) sine substitution; orthant cover; corner lemma; symmetry | [P] | review-fivepoint §6: correct | no | — | — |
| Gain-test derivation; interval and AD code | [P] (bnb.rs header) | encoding checked by hand; rounding and gain logic spot-checked | no | shared prover/checker code | — |
| (CL*) on [−1,1]⁶ | — | review-fivepoint §6: re-ran `ivcheck` | no | `clstar` (with and without symmetry) + 8 × `clnear`; second independent checker in progress, not used | 2·10⁷ random points, 800 local + 2 DE runs (referee); 9 000 local searches (author) |
| (I) three-angle inequality | — | — | no | `hull3` (401 / 1 014 leaves) | 121³ grid |
| Theorem 5 and Theorem K.1 | = §§3.1–3.3 + C.3 + duality | review-fivepoint: no gap; computer-assisted | no | via (CL*) | Toyoda SIP: 1000/1000 at W5 |
| Uniqueness of the minimiser | — | — | — | — | [N] only; [C] |
| K.3: Contracting ⇒ 3-SAT in 2^{O(n^{1−δ})} | [CE] | Theorem R non-uniform: refereed; uniform: audit; Theorem A: refereed; IM 7.1: not reviewed | arithmetic only (`ThmR.lean`, `ThmA.lean`) | — | — |
| K.4(a) rate 1 single-shot impossible | [P] | — | no | — | ALS floor √(5/8) at D = 2 |
| K.4(b) bond 2 border over ℂ | [P], uses [Lan06] | — | no | — | ALS floor 0.6695 |
| K.4(c) ℓ₁ ⇒ R ≥ 1; cut {v₁} gives 1 | [P] | — | `cut_ineq`, `w5_not_cut_combination`, `cut_v1` | — | — |
| Flow 3/4 | [P] | — | `flow_bound` | — | — |
| Explicit protocols above 3/4 | none known | — | — | — | none found single-shot at D_s ≤ 5 |

---

## 8. Open problems

1. **Explicit protocols above 3/4.** Item 1 guarantees restrictions T^{⊗m} ≤ S^{⊗(n+o(n))} for every rate below
   3/√10, but none is known above 3/4. A search for an exact or border protocol at a rate in (3/4, 3/√10) (for
   example 16 → 13) is the natural first target. Existence is guaranteed there only asymptotically. Above 3/√10, a
   protocol over a field of characteristic 0 would imply Contracting there (§5).
2. **An analytic proof of (I).** Show that three points z_i on the half-ellipse x² + y²/10 = 1, x ≥ 0 satisfy
   |z₁+z₂| + |z₁+z₃| + |z₂+z₃| ≥ 6. Facts and failed attempts:
   - The constant 9 = 10 − 1 is sharp for the interval method: with 8 the certificate does not close, at
     (π/2, π/2, −π/2).
   - Term-by-term bounds fail for mixed signs.
   - The chord bound √(1+9x) ≥ 1 + (√10 − 1)x and decoupled quadratic bounds fail (hull notes §3.5).

   An analytic proof of the full six-angle (CL*) would remove the computer from item 1.
3. **Uniqueness of the minimiser.** Is W5(ℓ,ℓ/3) the only five-point CAT(0) configuration with R = 3/√10, up to
   scale? If so, then f*(k) = 3/√10 ⇔ W5 is an AN price over k ⇔ tripod × ℝ is a price space over k. This uses the
   fact that the minimum over AN prices is attained (§1.2). It does not say that some point of Strassen's spectrum
   𝒳 has R = 3/√10; for 𝒳 only the infimum is known to equal f*. The route is an equality analysis of §3.2,
   which must force ψ = 0, ρ_i = 3D/2 and a_i = D/2.
4. **K_{2,m} and m-pods.** For K_{2,m}, take as demand all pairs on the m-side plus the pair on the 2-side. Then
   (m-pod) × segment gives R = 2m/√(m²(m−1)² + 4), which is 3/√10 at m = 3 (hull notes §7.6; not checked
   beyond m = 3). Mat₂(F_q) ⊂ Mat_{2r}(F₂) supplies the m-pods for m ≤ 2^r + 1 under ¬Contracting [D].
   Open: the matching lower bound, i.e. the analogue of Theorem 5 for m + 2 points, and which instance gives the
   largest forced gap between the tensor rate and the cut bound.
5. **Lean formalisation.**
   - Lemma H needs a CAT(0) library, or at least C.4(a),(f) as axioms in the style of `HullHyps`.
   - The book reduction and the calibration are elementary real analysis and look within reach.
   - The certificate would need a verified checker, or a reflection of the leaf tests into Lean.
   - Connecting to [AN]'s own `prop_space` and `thm_alt_rank_price` requires building their development.
6. **Whether contracting decides the rate.** If contracting holds over k, is f*(k) > 3/√10? Given uniqueness,
   this is equivalent to N5 not being an AN price over k. Contracting alone does not obviously decide it.

---

## References

- [AN] Anthropic, "VP ≠ VNP over every field", November 2026, with Lean development (`vp-vnp`). Machine-generated;
  not refereed by people.
- [CE] "The contracting case of the tensor-price dichotomy contradicts the weak exponential-time hypothesis",
  companion note, `research/ports/note-contracting-eth.md`, draft of 26 November 2026. Contains Theorems A, B, R
  and their status table (§7 there).
- [BH99] M. Bridson, A. Haefliger, *Metric spaces of non-positive curvature*, Springer 1999.
- [Lan06] J. M. Landsberg, "The border rank of the multiplication of 2×2 matrices is seven", J. Amer. Math. Soc. 19
  (2006).
- [Str88] V. Strassen, "The asymptotic spectrum of tensors", J. reine angew. Math. 384 (1988).
- [Toy] T. Toyoda, "Five-point CAT(0) spaces" (title as on arXiv), arXiv:1907.09074.
- Working files:
  - `research/ports/hull/notes.md` (§§1–3);
  - `research/ports/review-hull.md`;
  - `research/ports/e3/notebook.md`;
  - `research/ports/lean/` (`W5.lean`, `Hull.lean`, `NOTES.md`);
  - `tools/ivcert/` (`run_proofs.sh`, `src/problems/clstar.rs`, `certs/`).
