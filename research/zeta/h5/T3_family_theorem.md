# Theorem F: Dirichlet-family average beyond Fourier support 1, without zero-density estimates   [h5, T3c]

Status: **[C] complete proof sketch at referee level; all inputs listed with sources.** The steps marked [R] are proved
here. Each [K] input has a source. One input, the weighted large sieve constant 3/2, is quoted from a secondary source
and not read in the original (see K4). The numbers are [N] (scripts in this folder). I make no claim to [R] for the
theorem as a whole until h1 has refereed it.
Scripts: `family_opt.py` (window QP), `family_window_poly.py` (explicit analytic window + exact quadrature),
`family_ls_test.py` + `family_ls_test_Q400.log` (numerical test of the large-sieve step with real characters).

## 0. Statement

Notation. 𝔖 := Π_p(1 − p^{-2} − p^{-3}) = 0.4791453…; φ*(q) = #primitive χ mod q.
Family: ℱ_Q := {χ primitive mod q : Q₀ < q ≤ Q}, Q₀ := Q/log Q, weight ω_χ := 1/φ(q).
Heights: I := [T, 2T), T := (log Q)^{12}. N_χ(I) counts zeros ρ of L(s,χ), 0<β<1, with γ ∈ I, with multiplicity; N^s_{0,χ}(I) counts
simple zeros on β = 1/2; N_{d,χ}(I) counts distinct zeros.
Window class: λ ∈ (1,2). Ψ: [−λ/2, λ/2] → (0,∞) even, of the form Ψ = p², where p is a polynomial with p > 0 on [−λ/2, λ/2].
(Units: α is measured in units of log Q.)
Form-factor majorant with parameter K ≥ 1: F̃_K(a) := a for 0 ≤ a ≤ 1 and F̃_K(a) := K·a for a > 1. Define
  R_K(Ψ) := [ ∫Ψ² + ∬ F̃_K(|α−β|) Ψ(α)Ψ(β) dα dβ ] / (∫Ψ)².

**Theorem F.** Let K_MV := 3/(2𝔖) = 3.13058. For every λ ∈ (1,2), every admissible Ψ and every ε > 0 there is Q₁ such that for Q ≥ Q₁
  Σ_{χ∈ℱ_Q} ω_χ N^s_{0,χ}(I) ≥ (2 − R_{K_MV}(Ψ) − ε) Σ_{χ∈ℱ_Q} ω_χ N_χ(I),
  Σ_{χ∈ℱ_Q} ω_χ N_{d,χ}(I) ≥ ((3 − R_{K_MV}(Ψ))/2 − ε) Σ_{χ∈ℱ_Q} ω_χ N_χ(I).
More generally, the theorem holds with any K for which Lemma 6 (the family large sieve) holds with ratio K.

**Corollary F′ [N].** λ = 1.4, Ψ(α) = p(α)², p(α) = Σ_{i=0}^{5} c_i α^{2i},
c = (1.000832, −0.662584, 5.032586, −48.641263, 131.651741, −127.498598), min_{[−0.7,0.7]} p = 0.1498 > 0
(`family_window_poly.py`; Gauss–Legendre split at the kinks, converged to 1e-7): R = 1.2476270. Hence, unconditionally,
at least **0.7523** of the zeros in the family are simple and on the critical line, and at least **0.8761** are distinct
(both weighted family proportions). Check: the same code at λ = 1 reproduces 2 − 1/c₁* = 0.672500. Under GRH
(F̃ = min(a,1), λ → 2) it gives 0.9315, close to Sono's 0.9323, and the flat window gives CLLR's 11/12.

## 1. Inputs

- **K1** (explicit formula). Weil's explicit formula for a primitive χ mod q and complex F ∈ C_c^∞(ℝ): IK Thm 5.12 (Lean
  `ThmE.EF_lit_chi_L` transcribes it). In density form, for supp F ⊂ [−L, L] and X = e^L,
  Σ_ρ m_ρ F̂(γ_ρ) = ∫ F̂(τ) ν_χ(τ) dτ, with ν_χ = μ_χ + P_χ,
  μ_χ(τ) = (1/2π)[log(q/π) + Re Γ′/Γ((1/2+κ_χ)/2 + iτ/2)],  P_χ(τ) = −(1/π) Re Σ_{n≤X} Λ(n)χ(n) n^{−1/2−iτ}.
  There is no pole term (χ ≠ χ₀). ν_χ is real (A–F proof of Thm L; Lean ThmE/Hypotheses.lean).
- **K2** (zero counting, uniform in q). N_χ(t, t+1) ≪ log(q(|t|+2)), and N_χ(T,2T) = ∫_T^{2T} μ_χ + O(log qT)
  (Davenport, *Multiplicative Number Theory*, ch. 16; IK Thm 5.24). The zeros are symmetric under ρ ↔ 1 − ρ̄ with
  multiplicity (Lean ThmE/SeamL.lean: `L_reflect_zero`, `L_mult_reflect`).
- **K3** (Stirling, uniform in q). μ_χ(τ) = (1/2π) log(q|τ|/2π) + O(τ^{−2}) and μ_χ′(τ) ≪ 1/|τ| for |τ| ≥ 1, with absolute constants
  (Lean `ThmE.GammaFactsChiBounded` is exactly this uniform package).
- **K4** (Montgomery–Vaughan weighted Hilbert inequality). For real λ_r with δ_r := min_{s≠r}|λ_r − λ_s|,
  |Σ_{r≠s} z_r z̄_s/(λ_r − λ_s)| ≤ (3π/2) Σ_r |z_r|²/δ_r.
  [Montgomery–Vaughan, J. London Math. Soc. (2) 8 (1974) 73–82, Thm 1. I could not open the original (the publisher pages return
  HTML only). The statement and the constant 3π/2 are as quoted in arXiv:2203.14950, §1, eq. (MV2). Preissmann improved the
  constant to π(1 + (2/3)√(6/5))^{1/2}.]
- **K5** (Brun–Titchmarsh). π(x; d, 1) ≤ 2x/(φ(d) log(x/d)) for d < x (Montgomery–Vaughan, Mathematika 20 (1973), Thm 2).
  Only "≪" is used.
- **K6** (Mertens / PNT). Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x), and Σ_{x<p≤xe^η} log p/p = η + O(e^{−c√log x}).
- **K7** (arithmetic-free zero side). The Poisson–Gabor identity, inertia under pull-back, rank–trace (Lemma R) and block
  structure: A–F Lemmas 2.1, 3.1, 3.2 and Prop 4.1, valid for any locally finite ρ↔1−ρ̄-symmetric configuration (Lean
  `ZeroSide/*` over an abstract `ZeroConfig`).
- **K8** (Gevrey bump). There is ϱ₂ ∈ C^∞ with ϱ₂ = 0 on (−∞,0], ϱ₂ = 1 on [1,∞), nondecreasing, and
  sup|ϱ₂^{(k)}| ≤ B A^k k^{2k} (Lean `Taper/Gevrey.lean`: `gevreyProfile_rhoTwo`, items P1–P4; Leibniz rule P2).
- **K9** (mean value). Σ_{q≤x} φ*(q)/φ(q) = 𝔖x + O(x^{ε}) [R, elementary]. The Dirichlet series is ζ(s)g(s) with g absolutely
  convergent for Re s > 0 and g(1) = 𝔖 (CLLR eq. (2.2); CIS (2.15)), and the claim follows by convolution.
- **K10** (A–F Props "reduction" and "mumu" with ν replaced by the deterministic μ_χ). The proofs use only |μ_χ| ≤ B on
  [−4T, 4T], the growth of μ_χ at infinity, |μ_χ′| ≪ 1/T on I, and the bounds |φ̂|, |Φ| ≤ ϑ (A–F eq. thetadef).
  All of these hold uniformly here, with B ≪ log Q, by K3 and §2.

## 2. Set-up (per χ ∈ ℱ_Q)

- **Parameters.** ℓ := log Q, L := λℓ, X := e^L = Q^λ. Grid step h := 2π/L, α_k := T + kh, d := ⌊LT/2π⌋.
  D₀ := ℓ³, D := ℓ⁵, η := ℓ^{−2}, Y := Q^{1−2ε}.
- **Test function.** ψ(s) := Ψ(λs) on [−1/2, 1/2] (paper units), so ψ = p̃² with p̃(s) = p(λs).
  φ(u) := ϱ₂(L/2 + u) ϱ₂(L/2 − u) p̃(u/L).
  - φ is even, smooth, supported in [−L/2, L/2], and φ² = ψ(u/L) except on |u| ∈ [L/2 − 1, L/2].
  - a := ‖φ‖₂²/L = ∫ψ + O(1/L) and b := ‖φ‖₄⁴/L = ∫ψ² + O(1/L).
- **Lemma 1 (Gevrey decay) [R].** ‖φ^{(k)}‖₁ ≤ L B′ A′^k k^{2k}. The factor p̃(u/L) is entire, so its derivatives are
  ≤ C k! (rL)^{−k}; combine with K8 and the Leibniz rule. Hence for z ∈ ℂ,
  |φ̂(z)| ≤ C L e^{(L/2)|Im z|} exp(−c|Re z|^{1/2}).
  Proof: integrate by parts k times and take k ≍ (|z|/A′)^{1/2}/e.
  The cruder paper bounds |φ̂(r)| ≤ ϑ(r) = min(L, 2/|r|, C/r²) also hold.
- **Matrices.** v_ρ := (φ̂(γ_ρ − α_k))_{k<d} with γ_ρ = (ρ − 1/2)/i, and I′ := [T − D₀, 2T + D₀).
  - Ĝ_χ := (aL²)^{−1} Σ_{Re γ∈I′} m_ρ v_ρ v_ρᵀ and E_χ := the same sum over Re γ ∉ I′.
  - By K1, (Ĝ+E)_{kl} = (aL²)^{−1} ∫ f_{kl} ν_χ, where f_{kl}(τ) := φ̂(τ−α_k) φ̂(τ−α_l).
  - Split Ĝ + E = A_χ + B_χ, where A_χ uses μ_χ and B_χ uses P_χ.

## 3. Zero side

- **Lemma 2 (per-χ chain) [K7, R].** For every χ,
  N^s_{0,χ}(I′) ≥ 4 tr Ĝ_χ − 2N_χ(I′) − ‖Ĝ_χ‖_F²  and  2N_{d,χ}(I′) ≥ 4 tr Ĝ_χ − N_χ(I′) − ‖Ĝ_χ‖_F².
  This is A–F §6 verbatim. It uses only: v_ρ ∈ ℝ^d for β = 1/2 (φ̂ is real on ℝ); ‖v_ρ‖² ≤ aL² (Poisson, truncated sum);
  v_{1−ρ̄} = conj(v_ρ); inertia; Lemma R with (P₁, Q′); and N(I′) ≥ s₁ + 2s₂ + 2p.
- **Lemma 3 (tail) [R].** ‖E_χ‖₁ ≤ Q^{−10} for Q ≥ Q₁, uniformly in χ ∈ ℱ_Q.
  Proof:
  - ‖E‖₁ ≤ (aL²)^{−1} Σ_{Re γ∉I′} m_ρ Σ_{k<d} |φ̂(γ−α_k)|².
  - Since |Im γ| < 1/2, Lemma 1 gives each term ≤ C²L² X^{1/2} exp(−2c·dist(Re γ, I)^{1/2}).
  - By K2, Σ_{dist ≥ D₀} m_ρ e^{−2c·dist^{1/2}} ≪ ∫_{D₀}^∞ log(Q(T+s)) e^{−2c√s} ds ≪ e^{−c√D₀}.
  - Hence ‖E‖₁ ≪ X^{1/2} d e^{−c ℓ^{3/2}} ≤ Q^{−10}.
- **Corollary 3′.** N_χ(I′) − N_χ(I) ≪ D₀ log(QT) = o(N_χ(I)), since N_χ(I) = (T/2π)(ℓ_q + O(1)) with ℓ_q := log(qT/2π) (K2).
  Also tr Ĝ ≥ tr(Ĝ+E) − ‖E‖₁ and ‖Ĝ‖_F ≤ ‖Ĝ+E‖_F + ‖E‖₁.

## 4. Arithmetic lemmas (family)

- **Lemma 4 (first moment) [R].** For an integer k ≥ 2,
  |Σ_{χ∈ℱ_Q} ω_χ χ(k)| ≤ C τ(k−1) log Q.
  The same bound holds with χ̄(k), and for the restriction to a fixed parity it holds with τ(k−1) + τ(k+1).
  Proof:
  - For (k,q) = 1, Σ*_{χ mod q} χ(k) = Σ_{d|q} μ(q/d) φ(d) 1_{d|k−1}, so its absolute value is ≤ Σ_{d|(q,k−1)} φ(d).
  - Sum over q with weight 1/φ(q), using φ(dj) ≥ φ(d)φ(j) and Σ_{j≤Q} 1/φ(j) ≪ log Q.
  - Parity restriction: (1/2)(χ(k) ± χ(−k)).
- **Lemma 5 (Gauss sums and the Farey gap) [R].**
  - For primitive χ mod q, q Σ*_χ |Σ_n c_n χ(n)|² ≤ φ(q) Σ*_{a mod q} |S(a/q)|², where S(x) = Σ c_n e(nx).
    Proof: τ(χ̄)χ(n) = Σ_a χ̄(a) e(an/q) for every n; then apply orthogonality over all χ mod q.
  - The points {a/q : Q₀ < q ≤ Q, (a,q) = 1} are distinct mod 1, and δ_{a/q} ≥ 1/(qQ), because |a/q − a′/q′| ≥ 1/(qq′).
- **Lemma 6 (family large sieve) [R given K4].** For c_n supported on 1 ≤ n ≤ N,
  Σ_{χ∈ℱ_Q} ω_χ |Σ_n c_n χ(n)|² ≤ (N/Q₀ + (3/2)Q) Σ|c_n|².
  If N ≤ Q^λ with λ < 2, the right side is (K_MV + o(1)) H Σ|c_n|², where H := Σ_{Q₀<q≤Q} φ*(q)/φ(q) = 𝔖Q(1 + O(1/log Q)) by K9.
  Proof:
  - (i) Sine form of K4. Lift each point x_r to x_r + k (|k| ≤ M) with weights (−1)^k z_r, and apply K4. The lifted gaps are
    still δ_r. Average over M → ∞: the Cesàro means of Σ_j (−1)^j/(x+j) converge to π/sin(πx), and the diagonal terms vanish by
    symmetry. This gives |Σ_{r≠s} z_r z̄_s / sin π(x_r − x_s)| ≤ (3/2) Σ |z_r|²/δ_r.
  - (ii) Duality. Σ_n |Σ_r b_r e(n x_r)|² = N Σ|b_r|² + Σ_{r≠s} b_r b̄_s [e((N+½)θ) − e(½θ)]/(2i sin πθ), with θ = x_r − x_s.
    By (i) this is ≤ Σ_r |b_r|² (N + (3/2)δ_r^{−1}), i.e. Σ_r |S(x_r)|² (N + (3/2)δ_r^{−1})^{−1} ≤ Σ|c_n|².
  - (iii) Combine with Lemma 5: (1/q)(N + (3/2)δ^{−1}) ≤ N/Q₀ + (3/2)Q.
  - Note: this K is a ratio to the *family diagonal*. The diagonal term of Σ_χ ω|Σ c_nχ(n)|² is Σ_n |c_n|² Σ_q φ*(q)/φ(q)·1_{(n,q)=1}
    ≤ H Σ|c_n|².
- **Lemma 7 (elementary diagonal below Q) [R].** For c_n supported on n ≤ Y = Q^{1−2ε} and any weight W ≥ 0 with ∫W ≤ 2T,
  Σ_χ ω ∫W|Σ c_nχ(n)n^{it}|² dt ≤ H (∫W) Σ|c_n|² + O(T log Q · Y^{1+ε} max_n |c_n √n|²).
  Proof:
  - The diagonal terms give the first term.
  - Off-diagonal terms: |Δ(n,m)| ≤ C τ(|n−m|) log Q, as in Lemma 4 (Σ*χ(n)χ̄(m) = Σ_{d|q} μ(q/d) φ(d) 1_{d | n−m}), and |Ŵ| ≤ ∫W.

## 5. Prime side

Write c^{(j)}_n := b_n h_{y_n}(x_j), with b_n := Λ(n)/√n, y_n := log n, x_j := 2πj/L, and h_y(x) := ∫ φ(u)φ(y−u) e^{iux} du.

- **Lemma 8 (structure of B) [R].** ∫ f_{kl}(τ) e^{iτy} dτ = 2π e^{iyα_l} h_y(α_k − α_l). Consequently
  B_{kl} = −(2/aL²) Re Z_{k−l}(α_l), where Z_j(t) := Σ_n c^{(j)}_n χ̄(n) n^{it}.
  Moreover Σ_{j∈ℤ} |h_y(x_j)|² = L g(y) with g := φ²⋆φ². This is Parseval on an interval of length L containing
  supp φ(·)φ(y−·). Also |h_y| ≤ (L − y)_+.
- **Lemma 9 (μ-part, per χ) [K10, R].**
  ‖A_χ‖_F² = (2πb/(a²L)) ∫_I μ_χ² + O(N log L/L²) = (b/a²)(ℓ_q/L) N_χ(I)(1 + o(1)).
  And tr A_χ ≥ N_χ(I) − O(log Q). Proof of the trace bound:
  - K(τ,τ) := Σ_{k<d} φ̂(τ−α_k)² ∈ [0, aL²] (Poisson).
  - On [T+1, 2T−1], K(τ,τ) ≥ aL²(1 − O(L^{−2})), using ϑ ≤ C/r².
  - μ_χ > 0 because q ≥ Q₀ is large.
  - Then apply K2.
- **Lemma 10 (P-trace, family) [R].** |Σ_χ ω tr B_χ| ≪ √X (log Q)². Proof:
  - ∫ K(τ,τ) n^{−iτ} dτ = 2π A_φ(y) Σ_{k<d} e^{−iyα_k}, where A_φ := φ⋆φ ≤ (L−y)_+, and |Σ_k| ≤ L/(2 min(y, L−y)).
    So each term is ≤ πL²/log 2.
  - Then use Lemma 4, and Σ_{n≤X} Λ(n)τ(n−1)/√n ≪ √X log X (K5: τ(m) ≤ 2#{d | m : d ≤ √m}, then BT and partial summation).
  - Relative size: o(ΣωN), because ΣωN ≍ QTℓ and √X/Q → 0 (λ < 2).
- **Proposition 11 (P-part, family; the main estimate) [R given Lemma 6].**
  Σ_χ ω ‖B_χ‖_F² ≤ (1+o(1)) (2/(a²L⁴)) (L²T/2π) H Σ_n b_n² κ_n g(y_n),
  where κ_n := 1 for n ≤ Y and κ_n := K_MV for n > Y.
  Proof:
  - (a) Majorise the sum over l. Σ_{k,l<d} B_{kl}² = (4/a²L⁴) Σ_j Σ_{l∈J_j} (Re Z_j(α_l))², with J_j ⊂ [0,d).
    Bound it by Σ_{l∈ℤ} W(α_l)(·)², where W := 1_{[T−D, 2T+D]} ⋆ ρ_D, ρ_D(s) = D^{−1}ρ(s/D), and ρ is a Gevrey-2 bump on [−1,1]
    with ∫ρ = 1. Then W ≥ 1 on I, ∫W = T + 2D, and |Ŵ(ξ)| ≤ (2/|ξ|) C e^{−c(D|ξ|)^{1/2}}.
  - (b) Split off the edge. Z = Z_< + Z_e, where Z_e collects n > Xe^{−3η}. Use (Re Z)² ≤ (1+θ)(Re Z_<)² + (1+θ^{−1})|Z_e|²
    with θ = η^{1/2}. Since |h_y| ≤ 3η on the edge and the edge carries prime mass ≪ ηL (K6), the edge part is
    ≪ θ^{−1}η² L² of the main term, which is o(1).
  - (c) (Re Z_<)² = ½|Z_<|² + ½ Re Z_<².
  - (d) Poisson in l: Σ_l W(α_l) e^{iα_l u} = (L/2π) Σ_r Ŵ(rL − u) e^{irLT}.
    - For |Z_<|², u = y_n − y_m with |u| ≤ L − log 2. So the terms r ≠ 0 are ≤ e^{−c(D log 2)^{1/2}}·…, which is negligible against
      the trivial bound H L²(Σ b_n)² ≪ QL²X. The term r = 0 gives (L/2π) ∫ W |Z_<(t)|² dt.
    - For Re Z_<², u = y_n + y_m ∈ [2 log 2, 2L − 6η]. Only r = 1 with |L − u| < η is non-negligible.
      There |Ŵ| ≤ 3T, and Lemma 4 at k = nm gives a family bound ≪ L³ T log Q X^{ε′} Σ_{nm ∈ X e^{±η}} b_n b_m ≪ T ℓ^{O(1)} X^{1/2+ε′} = o(QTℓ).
      Here Σ_j |c^{(j)}_n||c^{(j)}_m| ≤ L² b_n b_m by Cauchy–Schwarz and Lemma 8.
  - (e) Family mean value with t frozen. For each t, apply Lemma 6 to the coefficients c_n n^{it} on n ∈ (Ye^{η}, X]
    (pointwise in t: |n^{it}| = 1), and Lemma 7 on n ≤ Ye^{−η}.
    - Cross terms between these two ranges: |y_m − y_n| ≥ 2η, so |Ŵ| ≤ e^{−c(Dη)^{1/2}} = e^{−cℓ^{3/2}}, which is negligible.
    - The middle range Ye^{±η} is handled by the (1+θ, 1+θ^{−1}) splitting again. Its mass is ≪ η of the total by K6.
  - (f) Sum over j with Lemma 8: Σ_j |c^{(j)}_n|² = b_n² L g(y_n). Collect the factors: 2·(L/2π)(T+2D)·L/(a²L⁴) = (1+o(1)) 2L²T/(2π a²L⁴).
- **Lemma 12 (cross term) [R].** |Σ_χ ω ⟨A_χ, B_χ⟩_F| ≪ T √X ℓ³ = o(ΣωN). Proof:
  - A_χ depends on χ only through (q, κ_χ). Group the family by (q, κ) and apply Lemma 4 (parity form) to the n-sum of B.
  - Bound Σ_{k,l} |A_{kl}| |h| ≤ L Σ_{k,l} |A_{kl}| ≪ L (log L)² T log Q. This uses |A_{kl}| ≤ (aL²)^{−1} ∫ ϑ_k ϑ_l |μ| and
    Σ_k ϑ(τ−α_k) ≪ L log L (A–F proof of Prop reduction).

## 6. Assembly

1. Sum Lemma 2 over ℱ_Q with weights ω. Use Lemma 3 and Corollary 3′.
2. Trace: Σω tr Ĝ ≥ Σω N(I)(1 − o(1)), from Lemmas 9 and 10.
3. Second moment, from ‖A+B‖² = ‖A‖² + 2⟨A,B⟩ + ‖B‖²:
   Σω‖Ĝ‖² ≤ Σω[ (b/a²)(ℓ_q/L) N_χ(I) ] + (2/(a²L⁴))(L²T/2π) H Σ b_n² κ_n g(y_n) + o(ΣωN).
4. By K6 and partial summation (g is Lipschitz and g(y) = L(ψ⋆ψ)(y/L) + O(1)),
   Σ b_n² κ_n g(y_n) = L³ ∫_0^1 κ̃(x) x (ψ⋆ψ)(x) dx + O(L²), with κ̃ = 1 for λx ≤ 1 − 2ε and κ̃ = K_MV otherwise.
5. Normalise by ΣωN = H(Tℓ/2π)(1+o(1)), using log q = ℓ + O(log ℓ) on the family.
   The right side becomes (R_{K_MV,ε}(Ψ) + o(1)) ΣωN, where R_{·,ε} uses F̃ with the jump at 1 − 2ε.
   R_{K,ε} → R_K as ε → 0, since the change is supported on |α−β| ∈ [1−2ε, 1]. This gives Theorem F.
6. Distinct zeros: the same argument with the second inequality of Lemma 2.

## 7. What is new, what is fragile

- The mechanism is entirely the A–F zero side (Lemma 2, per χ, unconditional) plus an *upper* bound for the family second
  moment. No asymptotic for the family pair correlation and no zero-density estimate are used.
  - The sharp form factor f = 1 on (1,2) needs GRH in CLLR, and only for small-conductor characters; see `T3_families.md` §2.
  - The upper bound loses a factor K on (1,λ]. That loss is second order at α = 1, so it still pays.
- Two per-χ estimates of the ζ proof fail in the family:
  - the zero-side trace (Prop trace: off-line zeros near the edges cost X^{1/2} ≫ T);
  - the sup-norm reduction errors (|P_χ| ≈ √X).
  Both are replaced by family-averaged arguments: Lemmas 4 and 10, Poisson in l, and the pointwise-in-t large sieve.
- **Fragile points for the referee.**
  - (1) K4: constant 3π/2 taken from a secondary source.
  - (2) Step (e) of Proposition 11 applies Lemma 6 for every t and then integrates against W. This is legitimate because W ≥ 0.
  - (3) The O₂ (Re Z²) aliasing analysis in step (d).
  - (4) Lemma 9 relies on A–F's reduction proof with ν = μ_χ; the error terms must be uniform in q. K3 gives this.
  - (5) Excluding q ≤ Q₀ is essential: for small moduli the term N/q dominates.
- **Numerical test of Lemma 6/7** (`family_ls_test.py`, real primitive characters via a DFT on the unit group; the count of
  primitive characters was checked against φ*). Ratio ρ := family Σ|Σ c_nχ(n)|² / (H Σ|c_n|²) for prime blocks [Q^a, 1.25Q^a]:

  | Q | a | ρ at t = 0 | ρ at t ≍ ℓ² |
  |---|---|---|---|
  | 400 | 0.5 | 0.95 | 0.95 |
  | 400 | 0.8 | 1.00 | 0.99 |
  | 400 | 1.1 | 0.90 | 1.00 |
  | 400 | 1.3 | 0.71 | 1.02 |
  | 400 | 1.5 | 0.59 | 1.06 |
  | 400 | 1.7 | 0.53 | 1.00 |

  For comparison, the rigorous finite-Q bound (N/Q₀ + 1.5Q)/H is 3.75–6.9, and K_MV = 3.13.
  - So the true ratio is ≈ 1. At t = 0 it falls below 1 for a > 1, which is the CLLR off-diagonal main term. The large sieve is the
    lossy step: improving K (h4, T3b) is worth up to 0.888 (K = 1, diagonal only) and 0.9315 (GRH).
- **Comparison.** CIS 14/25 = 0.56 (Levinson); D'Souza 0.7235 (no hypothesis) and 0.9059 (with the Jutila and Montgomery
  density theorems); A–F Remark rem:Davg 0.811 (proof omitted). Theorem F's 0.7523 needs no density estimate.

## 8. Plug-in values for a sharper family large sieve [N] (`family_opt.py`, grid n=300, about 5e-4 optimistic)
If Lemma 6 holds with ratio K, then Theorem F gives:

| K | source | simple on line | distinct |
|---|---|---|---|
| 3.1306 | MV weighted LS (this note) | 0.7523 | 0.8761 |
| 2.087 = 1/𝔖 | h4's claimed sharp constant for the sharp q-cutoff | ≈ 0.786 (λ ≈ 1.6) | ≈ 0.893 |
| 1.269 = (6/π²)/𝔖 | h4's claimed constant for weights vanishing at q = Q; A–F's 1.263 | ≈ 0.848 (λ → 2) | ≈ 0.924 |

The last row changes the family weights. Lemma 7 and the normalisation H must then be redone with W(q/Q)/φ(q); the structure of
the proof does not change.
