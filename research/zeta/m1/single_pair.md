# T1d: certified proof of the single-pair inequality (*) for an explicit kernel of value 0.6776105 (m1)

Builds on h3/T1b_depth_lemma.md §6–9 (Lemma T, Lemma C, cell criterion R4), h3/T1f_lemmaZ.md §2–5 (Lemma Z, corrected target
2N − s₁, packing lemma, the explicit 5-term kernel) and h5/T1g_mixture.md. All scripts are in this folder. They use ball arithmetic
(Arb through python-flint 0.9.0, 160-bit working precision): every number that enters a decision is an enclosure.

**Result.** Theorem A below is **[R]**, given the correctness of Arb/python-flint. It is the inequality (*) for every real background
and every depth y > 0, for the kernel of §1. That kernel is h3's kernel with one coefficient corrected (see §1). Its value is
**0.6776104694 > 0.67364**. Hence, through Lemmas T and C, the full configuration inequality holds for **every conjugation-symmetric
configuration with at most one off-line pair** (any multiplicities), for the limiting kernels (K, K₁). Not covered: the T-dependent
kernels K·W_T of Lemma Z, uniformly in T (§9), and configurations with two or more pairs (T1e).

No region is left uncertified. The depth axis is covered as (0, 0.02] by Lemma 6, [0.02, 8.5] by the grid (Lemma 8), and [8, ∞) by Lemma 9.
The x-axis is covered by explicit cells on [0, 15.5] and by tail Lemma 5 for |x| > 15.5.

How to check: `python3 run_all.py` (about 2 min). It re-runs the closed-form cross-check, the kernel certificate, Lemma 6 and Lemma 9,
and it verifies that the grid logs `grid_*.log` cover [0.02, 8.5] with every y-box certified. `python3 run_all.py --regrid` also recomputes
the grid (about 1.5 h on 3 cores).

---------------------------------------------------------------------------------------------------------------------------
## 0. Notation and the statement
For a CGdL-type r (real, even, supported in [−3/2, 3/2], with r ≥ 0 on [−1,1], r ≤ 0 on 1 ≤ |α| ≤ 3/2, K := r̂ ≥ 0, K(0) = 1), put
r₁ = r·1_{[−1,1]}, K₁ = r̂₁ (entire), and r₂ = −r·1_{|α|>1} ≥ 0. For real x and y ≥ 0 define
- β_y(x) := Re K₁(x+iy) − K₁(x) = ∫_{−1}^{1} r(α)(cosh 2παy − 1) cos 2παx dα,
- G_y(x) := K(x) + β_y(x),
- Δ(y) := K₁(2iy) − K₁(0) = ∫_{−1}^{1} r(α)(cosh 4παy − 1) dα ≥ 0,
- c(m) := (m² − 2m)₊ for integers m ≥ 1 (so c(1) = c(2) = 0).

A *real background* B is a finite set of distinct real points x_b, with integer multiplicities m_b ≥ 1. The pair sits at t ± iy, and
x_b = t_b − t.

**(*)** LHS(B, y) := 2Δ(y) + 4Σ_b m_b G_y(x_b) + Σ_{b≠b′} m_b m_b′ K(x_b − x_b′) + Σ_b c(m_b) ≥ 0.

**Theorem A [R].** For the kernel of §1, (*) holds for every real background B and every y > 0. Moreover, for an off-line pair of any
multiplicity m_p ≥ 1, 2m_p²Δ(y) + 4m_pΣ_b m_b G_y(x_b) + Σ_{b≠b′} m m′ K + Σ c(m_b) ≥ 0. The cell charges satisfy
Σ h ≤ 0.951 · 2Δ(y) for all y > 0, so the margin is at least 4.9%. The worst case is y ∈ [0.165, 0.174] (§8).

**Corollary B [R].** Let X be any finite multiset that is symmetric under conjugation, with real points of any multiplicities and at most one
non-real conjugate pair {t ± iy} (of any multiplicity m_p). Then Σ_{z,z′∈X} m m′ K₁(z − z′) ≥ 2N(X) − s₁(X), where s₁ is the number
of real points of multiplicity one.

---------------------------------------------------------------------------------------------------------------------------
## 1. The kernel, and a correction to h3's coefficients
**Correction [R].** h3's printed kernel (a₁ = 0.53044, with a₂ fixed by r(1) = 0) has f(±3/4) = 2/3 − a₁ + a₂ = −1.08·10⁻⁶ ≠ 0.
Near α = 3/2, with ε = 3/2 − α,
  r(3/2 − ε) = ∫₀^ε f(−3/4+s) f(3/4−ε+s) ds = f(−3/4)f(3/4)·ε − (ε³/6) f′(−3/4) f′(3/4) + O(ε⁴) ≈ 1.17·10⁻¹² ε − 1.45 ε³.
So **r > 0 on (3/2 − 9·10⁻⁷, 3/2)**. This violates r ≤ 0 off [−1,1], and with it Lemma T: the error would be about 10⁻²⁴ N², which is not o(N).
The 2001-point check in h3 could not see it.

The fix imposes f(±3/4) = 0 exactly. The value is unchanged to 9 digits.

**Definition.** μ_n := 4πn/3. On [−3/4, 3/4],
  f(u) = 2/3 + a₁ cos μ₁u + a₂ cos μ₂u + b₁ sin μ₁u + b₂ sin μ₂u,  b₁ = 0.347412,  b₂ = −0.178443  (exact decimals),
  a₁ := 2/3 + a₂  (⇔ f(±3/4) = 0),  a₂ := the root near −0.13623 of the quadratic equation r(1) = 0.
Numerically a₂ = −0.13622604401150720395…, a₁ = 0.53044062265515946272… (`kern.solve_a2`: r(1) is an exact quadratic in a₂; it is
interpolated at a₂ = −1, 0, 1 and solved in ball arithmetic). Then r := f ⋆ f (autocorrelation), r(α) = ∫ f(u)f(u+α)du, and K = |f̂|².

**Lemma 1 (closed forms) [R].** Write f(u) = Σ_{n=−2}^{2} c_n e^{iμ_n u}, with c₀ = 2/3, c_{±1} = (a₁ ∓ ib₁)/2, c_{±2} = (a₂ ∓ ib₂)/2. For 0 ≤ α ≤ 3/2,
  r(α) = Σ_{n} c_n c_{−n} (3/2 − α) e^{−iμ_nα} + Σ_{n+m≠0} c_n c_m (−1)^{n+m} (e^{−iμ_nα} − e^{iμ_mα}) / (iμ_{n+m})
       = Σ_{k=−2}^{2} (P_k + Q_k α) e^{iμ_kα}.
*Proof.* On [−3/4, 3/4 − α], ∫ e^{iμ_j u} du = (−1)^j (e^{−iμ_jα} − 1)/(iμ_j) for j ≠ 0, since e^{±iμ_j·3/4} = (−1)^j; for j = 0 it equals 3/2 − α. ∎
So K(x) = 2 Re ∫₀^{3/2} r e^{2πiαx}dα and Re K₁(x+iy) = Re ∫₀¹ r(α)(e^{2πα(ix+y)} + e^{2πα(ix−y)})dα. Every derivative ∂_x^a∂_y^b of
K, K₁ and G is a finite sum of terms P_k M_j + Q_k M_{j+1}, with M_j = ∫₀^L α^j e^{wα} dα = L^{j+1} E_j(wL) and E_j(w) = ∫₀¹ t^j e^{wt} dt.
E_j is evaluated by its power series with an explicit tail bound when |w| < 2, and by the exact recurrence E_j = (e^w − jE_{j−1})/w otherwise
(`kern.E_all`). Independent check (`check_closed_form.py`, PASS): r, K = |f̂|² and Re K₁(x+iy) agree with 30-digit mpmath quadrature
to 1.2·10⁻³⁰, and the derivative formulas agree with finite differences.

**Lemma 2 (kernel facts) [R]** (`cert_kernel.py`, ALL PASS).
(a) f(±3/4) = 0 and ∫f = 1, so K(0) = 1 and K = |f̂|² ≥ 0.
(b) r > 0 on [0, 0.98] (Taylor boxes); r′ < 0 on [0.98, 1.02] and r(1) = 0, so r > 0 on [0,1) and r < 0 on (1, 1.02]; r < 0 on [1.02, 1.48].
  On (1.46, 3/2): f′ < 0 on [−3/4, −0.71] and on [0.71, 3/4]. With f(±3/4) = 0 this gives f(−3/4+s) < 0 < f(3/4−ε+s) for 0 < s < ε ≤ 0.04,
  hence r(3/2−ε) = ∫₀^ε f(−3/4+s)f(3/4−ε+s)ds < 0. So r is CGdL-admissible, and r₁ ≥ 0.
(c) **Value** 2 − r(0) − 2∫₀¹ α r(α) dα = 0.677610469385828… (ball radius 7·10⁻⁴⁶) **> 0.67364**. τ = ∫_{|α|>1}|r| = 0.0112180,
  K₁(0) = 1.0112180.
(d) r′(0) = −(f(3/4)² + f(−3/4)²)/2 = 0, and r is an exponential polynomial (hence C^∞) on [0, 3/2]. Certified constants
  (upper bounds unless stated): |r′(1)| = 0.3934509, |r″(1)| = 3.611657, R_d := sup_{[0,1]} |r^{(d)}| ≤ 1.00640, 1.29653, 7.94697, 32.1779
  (d = 0..3), |K₁″(0)| = 4π²∫_{−1}^{1} α² r = 5.861923 (two-sided), ∫_{−1}^{1} α⁴ r = 0.0534008, and r′ ≤ −ρ on [0.75, 1] with ρ = 0.392539.
(e) K″ < 0 on [0, 0.25] and K′ < 0 on [0.25, 0.75], so K is decreasing on [0, 0.75]. Hence κ(d) := min_{|u|≤d} K(u) = K(d) for d ≤ 0.75.
  (Values: K(0.25) ≈ 0.85, K(0.4) = 0.6331, K(0.5) ≈ 0.473.)
(f) [N, structure] K has **exact double zeros at x = 2k/3 for all |k| ≥ 3**, because f̂(2k/3) = Σ c_n ∫ e^{2πiu(2n−2k)/3} du = 0. It has
  one further near-zero, K(1.0498) ≈ 8·10⁻¹⁰. So K is not bounded below by a positive constant near these points. This is why y → 0 needs the
  cell argument of Lemma 6, and not "K > 0 off common zeros" as in h5's mixture plan. With the cell argument, mixing in MT is not needed.

---------------------------------------------------------------------------------------------------------------------------
## 2. Reduction to (*)  [R]
**Lemma T (tail positivity; h3 §6).** For every finite conjugation-symmetric multiset X,
Σ_{z,z′} m m′ K₁(z−z′) = Σ m m′ K(z−z′) + ∫ r₂(α)|S_X(α)|²dα, where S_X(α) = Σ m e^{2πiαz} satisfies S_X(−α) = conj S_X(α).
*Proof.* K₁ − K = r̂₂. Expand ∫ r₂ |S|² and use the symmetry of X. ∎ (r₂ ≥ 0 by Lemma 2(b).)

**Lemma C (comparison with a double, general multiplicities).** Let X = B ∪ {t ± iy}, where the pair has multiplicity m_p, y > 0, and B is
real. Let X₀ = B ∪ {t with multiplicity 2m_p}. Then
  Σ_X K₁ − (2N(X) − s₁(X)) ≥ 2m_p²Δ(y) + 4m_pΣ_b m_b G_y(x_b) + Σ_{b≠b′} m_b m_b′ K(x_b−x_b′) + Σ_b c(m_b) + 4(m_p² − m_p).
*Proof.* Directly, Σ_X K₁ − Σ_{X₀} K₁ = m_p²(2K₁(0) + 2K₁(2iy) − 4K₁(0)) + 4m_pΣ m_b β_y(x_b). This uses K₁(z̄) = conj K₁(z) and evenness.
By Lemma T applied to X₀ (real points), Σ_{X₀}K₁ ≥ Σ_{X₀}K = Σ_{b,b′} m m′ K(x_b − x_b′) + 4m_pΣ m_b K(x_b) + 4m_p². The diagonal gives
Σ m_b², and m_b² = (2m_b − 1_{m_b=1}) + c(m_b). The target is 2N − s₁ = 4m_p + Σ_b(2m_b − 1_{m_b=1}). ∎
With m_p = 1 the right side is LHS(B, y) of (*). **So Theorem A implies Corollary B.** The case m_p ≥ 2 is covered by Lemma 4(c).

---------------------------------------------------------------------------------------------------------------------------
## 3. The cell criterion  [R]
**Lemma 4 (packing).** Fix y > 0. Let {P} be a family of disjoint sets that covers {x : G_y(x) < 0}, with diam P = ℓ_P ≤ 0.75. Put
g_P := sup_P (−G_y)₊ and κ_P := K(ℓ_P), and define h(g, κ) := 8g if 2g ≤ κ, and h(g, κ) := (2g+κ)²/κ otherwise.
(a) LHS(B, y) ≥ 2Δ(y) − Σ_P h(g_P, κ_P) for every real background B.
(b) h(λg, κ) ≤ λ² h(g, κ) for λ ≥ 1, and h(g, κ) ≤ 8g + 4g²/κ.
(c) For an m_p-fold pair, the left side of Theorem A is ≥ m_p²(2Δ − Σ_P h).
*Proof.* (a) Drop the cross terms K ≥ 0 between different pieces, and between a piece and the points where G_y ≥ 0; those points contribute
≥ 0. Let the points of B in P have total mass M. Their contribution is
≥ −4g_P M + max(0, κ_P(M² − Σm_b²) + Σc(m_b)) ≥ −4g_P M + κ_P(M² − 2M)₊. The last step uses c(m) ≥ κ(m² − 2m) for κ ≤ 1, and that this
expression is ≥ 0. Maximising over real M ≥ 0 gives h: for M ≤ 2 the value is 8g; for M ≥ 2 the maximum is at M = 1 + 2g/κ.
(b) h(g)/g² = 8/g or (2 + κ/g)²/κ, which is non-increasing in g. Also (2g+κ)²/κ = 4g²/κ + 4g + κ ≤ 4g²/κ + 6g when 2g > κ.
(c) The m_p-fold version replaces 4g by 4m_p g, so the piece charge is h(m_p g, κ) ≤ m_p² h(g, κ) by (b). ∎
The partition need not be connected components. Below, pieces are unions of consecutive x-boxes, chosen by dynamic programming to
minimise Σ h. This is the main improvement over h3's R4: at moderate and large y, splitting a long cell into pieces of length ≈ 0.3–0.4 raises κ.
By evenness of G_y in x, pieces are taken on x > 0 and mirrored.

---------------------------------------------------------------------------------------------------------------------------
## 4. Bounds for β  [R]
**Lemma 5.** For real x and y ≥ 0:
(a) |β_y(x)| ≤ Δ(y/2), since r₁ ≥ 0.
(b) (small y, two integrations by parts in α.) Put φ_y(α) = r(α)(cosh 2παy − 1), which is even, C³ on [0,1], with φ_y(1) = 0 and φ_y′(0) = 0.
With ω = 2πx, β_y(x) = 2φ′(1)cos ω/ω² − 2φ″(1)sin ω/ω³ + (2/ω³)∫₀¹φ‴ sin(ωα)dα. Hence
|β_y(x)| ≤ a(y)/x² + b(y)/x³, with a = 2|φ′(1)|/(4π²) and b = 2(|φ″(1)| + ∫₀¹|φ‴|)/(8π³). Here φ′(1) = r′(1)(ch−1),
φ″(1) = r″(1)(ch−1) + 2r′(1)·t·sh, and ∫₀¹|φ‴| ≤ R₃(sh/t − 1) + 3R₂(ch−1) + 3R₁·t·sh + R₀t²(ch−1), with t = 2πy, ch = cosh t, sh = sinh t.
a(y)/y² and b(y)/y² are non-decreasing (power series with non-negative coefficients).
(c) (complex z.) For z ≠ 0 and ω = 2πz, K₁(z) = 2r′(1)cos ω/ω² − 2r″(1)sin ω/ω³ + (2/ω³)∫₀¹ r‴ sin(ωα)dα. This uses r(1) = 0 and
r′(0) = 0. Since |cos ω|, |sin ωα| ≤ cosh 2π Im z,
|K₁(x+iy)| ≤ cosh(2πy)[2|r′(1)|/|ω|² + 2(|r″(1)| + R₃)/|ω|³], and the same bound with y = 0 holds for K₁(x). So
|β_y(x)| ≤ (cosh 2πy + 1)[2|r′(1)|/(2πx)² + 2(|r″(1)|+R₃)/(2πx)³].
(d) (tail sum.) If g_k ≤ a/x_k² + b/x_k³ on pieces [x_k, x_k + ℓ] with x_k = X + kℓ, then
Σ_k (8g_k + 4g_k²/κ) ≤ 8S₁ + 4S₂/κ, where S₁ = γ(X) + (a/X + b/(2X²))/ℓ, S₂ = γ(X)² + (a²/(3X³) + ab/(2X⁴) + b²/(5X⁵))/ℓ, and
γ = a/x² + b/x³ (monotone comparison with the integral).
*Proof.* (a) |cos| ≤ 1. (b), (c): integrate by parts three times on [0,1]. The boundary terms at 0 vanish because φ′(0) = r′(0) = 0 and
sin 0 = 0; those at 1 vanish because φ(1) = r(1) = 0. (d) Standard. ∎
These are `common.tail_coef_small`, `common.tail_coef_large` and `common.tail_charge`. The grid takes, per y-box, the smaller of the
(b) and (c) bounds, evaluated at the top of the y-box (all coefficients are increasing in y), with ℓ = 0.5 and κ = K(0.5).

---------------------------------------------------------------------------------------------------------------------------
## 5. Lemma 6: small depth 0 < y ≤ Y₁ = 0.02  [R]  (`small_y.py 0.02 15.5`: PASS, ratio ≤ 0.9158)
For y ≤ Y₁, write cosh t − 1 = t²/2 + ρ(t), with 0 ≤ ρ(t) ≤ (t⁴/24)cosh t. Then
β_y(x) ≥ −(y²/2)K₁″(x) − y⁴E₄, where E₄ = (2π)⁴cosh(2πY₁)/24 · ∫_{−1}^{1} α⁴ r. Hence **G_y(x) ≥ K(x) − y²W(x)**, with
W := K₁″/2 + Y₁²E₄.
(i) On [0, 15.5], x-boxes are certified to satisfy either W < 0 or K − Y₁²W > 0; either way G_y > 0 there for every y ≤ Y₁. The remaining
boxes lie in 16 pieces of length ≤ 0.5: around the near-zero 1.0498 and the zeros 2, 4, …, 8 of K (where K₁″ > 0), and, for x ≳ 9, wider pieces where K is so small (≲ 10⁻⁷) that Y₁²W dominates. (The zeros 2k/3 with K₁″(2k/3) < 0
need no cell: there G_y ≥ y²|K₁″|/2 − y⁴E₄ > 0.) On a piece P, g_P ≤ y² sup_P W ≤ Y₁² sup W ≪ κ, so h = 8g_P.
(ii) For x > 15.5, Lemma 5(b)+(d) with ℓ = 0.5 gives coefficients ≤ (y/Y₁)²·(a, b)(Y₁).
(iii) Δ(y) ≥ ∫ r₁(4παy)²/2 = 2y²|K₁″(0)|.
So Σh/(2Δ) ≤ [16 Σ_P sup_P W + 2 Tail(Y₁)/Y₁²]/(4|K₁″(0)|) = 0.8571 (cells) + 0.0587 (tail) = **0.9158 < 1**, uniformly in y ∈ (0, Y₁].
At Y₁ = 0.01 the same lemma gives 0.860. The y → 0 limit of the cell part is
Σ_{x₀ ∈ Z(K)\{0}} K₁″(x₀)₊ / |K₁″(0)| ≈ 0.775. This is h3's difference-set quantity, but with no difference-set lemma needed: the crude cell
sum is already below 1.

---------------------------------------------------------------------------------------------------------------------------
## 6. Lemma 8: intermediate depths 0.02 ≤ y ≤ 8.5, a certified grid  [R]  (`grid.py`; logs `grid_*.log`)
The interval [0.02, 8.5] is cut into y-boxes Y = [y_a, y_b] with decimal end points. The steps are geometric (5%) on [0.02, 1] and of
length 0.05 on [1, 8.5]. A box is halved on failure. For each box:
1. **Scaling.** Fix s ≥ 0 (s = Δ′(y_a)/2Δ(y_a), rounded; any s ≥ 0 is valid). Put G^s(x,y) := e^{−s(y−y_a)}G_y(x) and
   D̂(y) := e^{−2s(y−y_a)}Δ(y). If ĝ_P ≥ sup_{P×Y}(−G^s)₊, then g_P(y) ≤ e^{s(y−y_a)}ĝ_P, and by Lemma 4(b)
   Σ_P h(g_P(y)) ≤ e^{2s(y−y_a)} Σ_P h(ĝ_P). So it suffices that **Σ_P h(ĝ_P, κ_P) + Tail(y_b) < min_Y D̂** (both sides ×2 for the
   mirror). This removes the mismatch between the growth of charges and self term across a y-box. Without it, a 5% box at y = 0.75 loses a
   factor ≈ 1.45.
2. **x-boxes.** [0, 15.5] is cut into boxes of width 0.05, bisected adaptively down to 2·10⁻⁴. On a box with centre (x_c, y_c) and half-widths
   (h_x, h_y), the code uses the Taylor expansion of order 8 with exact ball coefficients ∂^{a,b}G^s(x_c, y_c), computed in closed form
   by Lemma 1. The Lagrange remainder Σ_{a+b=9} S_{ab}h_x^a h_y^b/(a!b!) uses the a-priori bounds
   |∂_x^a∂_y^bG| ≤ (2π)^{a+b}[1_{b=0}(∫_{−3/2}^{3/2}|r||α|^a + ∫_{−1}^1 r|α|^a) + ∫_{−1}^{1} r|α|^{a+b}cosh 2παy_b]. These moments are
   exact closed forms, by Lemma 2(b), and are combined with the binomial expansion for the factor e^{−s(y−y_a)} ≤ 1.
   The certified bound is G^s ≥ ∂^{0,0} − Σ_{1≤a+b≤8}|∂^{a,b}|h_x^a h_y^b/(a!b!) − remainder. A box with positive lower bound is clear.
   Otherwise u = −(lower bound) ≥ sup(−G^s)₊ on the box. (The order-8 model is essential. Ball evaluation of G″ on a box of width 0.05 gives
   |G″| ≲ 1.6 where the true value is 10⁻⁵, because of cancellation between O(1) exponential terms.)
3. **Pieces.** Each maximal run of non-clear boxes is split by dynamic programming into pieces of length ≤ 0.75. The choice is made in
   floating point, and the chosen partition is then charged in ball arithmetic with κ_P = lower bound of K(⌈ℓ_P⌉_{0.01}).
4. **Tail** x > 15.5: Lemma 5(b)/(c)/(d) at y = y_b.
5. **Self term.** min_Y D̂ comes from an order-8 Taylor model of D̂ at the midpoint, with a remainder from the same moment bounds.
6. PASS iff (2Σ_P h + 2·Tail)/(2 min D̂) < 1. A factor e^{2s·(rounding radius)} is included.

Floating point is used only for heuristic choices (s, refinement, DP). Every inequality that is concluded is checked in Arb.

Results: see §7.

---------------------------------------------------------------------------------------------------------------------------
## 7. Lemma 9: large depth y ≥ 8  [R]  (`large_y.py 8`: PASS, ratio ≤ 0.7783; at Y₂ = 10: 0.5674)
Take pieces [kℓ, (k+1)ℓ], ℓ = 0.4, κ = K(0.4) ≥ 0.63312. By Lemma 5(c) with |ω| ≥ 2π√(x²+y²) and J₃ = ∫₀¹|r‴|cosh 2παy ≤ R₃ cosh(2πy)/(2πy),
g_k ≤ λ cosh(2πy)/(2π²(k²ℓ² + y²)) + v_k, with λ = |r′(1)| + (|r″(1)| + R₃/(2πY₂))/(2πY₂) and
v_k = min(K₁(0), (|r′(1)| + (|r″(1)|+R₃)/(2πkℓ))/(2π²k²ℓ²)).
Δ(y) ≥ 2ρ∫_{0.75}^{1}(1−α)(cosh 4παy − 1)dα ≥ ρθ e^{4πy}/(16π²y²), where θ = 1 − 2e^{−c/4} − (c/4)e^{−c/4} − (c²/16)e^{−c} at c = 4πY₂.
θ is increasing in c, so this bound holds for all y ≥ Y₂.
With h ≤ 8g + 4g²/κ, (a+b)² ≤ 2a² + 2b², Σ_k(k²ℓ²+y²)⁻¹ ≤ y⁻² + π/(2ℓy) and Σ_k(k²ℓ²+y²)⁻² ≤ y⁻⁴ + π/(4ℓy³):
Σh/(2Δ) ≤ (32λ²/(π²ρθκ))(y⁻² + π/(4ℓy)) + (64λ/ρθ)e^{−2πy}(1 + πy/(2ℓ)) + 16(V₁ + V₂/κ)·16π²y²e^{−4πy}/(2ρθ),
with V₁ = Σv_k, V₂ = Σv_k². Each term is non-increasing for y ≥ 1, so the value at Y₂ = 8, which is 0.7783, bounds it for all y ≥ 8.

---------------------------------------------------------------------------------------------------------------------------
## 8. Proof of Theorem A and summary of margins
Combine Lemma 6 (y ≤ 0.02), Lemma 8 (0.02 ≤ y ≤ 8.5) and Lemma 9 (y ≥ 8) with Lemma 4(a),(c). ∎

| region | certificate | worst ratio Σh/(2Δ) |
|---|---|---|
| 0 < y ≤ 0.02 | Lemma 6 | 0.9158 |
| 0.02 ≤ y ≤ 8.5 | grid, Lemma 8 (232 y-boxes) | 0.9507 (at y ∈ [0.165, 0.174]) |
| y ≥ 8 | Lemma 9 | 0.7783 |

The grid has 232 certified y-boxes; none needed splitting. By range (worst certified Σh/(2Δ)):
[0.02, 0.06]: 0.908; [0.06, 0.15]: 0.949; [0.15, 0.5]: 0.951; [0.5, 1]: 0.869; [1, 8.5]: 0.502, falling to 0.056 at y = 8.5.
The logs are `grid_0.02_0.15.log` (run stopped after 0.0614), `grid_0.06_0.15.log`, `grid_0.15_1.0.log` (stopped after 0.508),
`grid_0.5_1.0.log` and `grid_1.0_8.5.log`. `run_all.py` checks that their union covers [0.02, 8.5] and that every box is ok.
The tightest region is 0.1 ≤ y ≤ 0.3. There the cells at the zeros 2, 4, 6, … of K and at the near-zero 1.05 dominate, as y → 0, and the tail
x > 15.5 costs 0.06. Floating-point exploration of the same criterion gives about 0.81–0.83 at those depths, so the certification overhead
is ≈ 0.12. A larger X or a finer tail would buy margin if it is ever needed (e.g. for T-uniformity).

Floating-point sanity check, not part of the proof (`sanity_adversary.py`): local minimisation of LHS/(2Δ) over random backgrounds of up to
12 points with multiplicities 1–4, started in the negative cells, found nothing below 0.69.

---------------------------------------------------------------------------------------------------------------------------
## 9. What is not covered, precisely
1. **T-uniformity (CI_T).** Lemma Z needs (*) for the Montgomery-weighted kernels K^{(T)} = K·W_T, K₁^{(T)} = K₁·W_T, with
   W_T(z) = 4/(4 + (2πz/log T)²), uniformly in T. Lemma T and Lemma C hold verbatim for the T-kernels (h3 T1f §3), and K^{(T)}(0) = 1.
   What is known [R]:
   - The self term only improves: W_T(2iy) = 1/(1 − (2πy/L)²) ≥ 1, with L = log T.
   - Packing still works: K^{(T)}(u) ≥ K(u)(1 − (πu/L)²).
   - G^{(T)}_y = W_T(x)G_y(x) + E(x,y), with E := Re[K₁(x+iy)(W_T(x+iy) − W_T(x))].
   - E(x,0) = ∂_yE(x,0) = 0, because K₁ and W_T are real on R. Hence |E| ≤ (y²/2)·sup_{0≤s≤y}|K₁″(z)(W_T(z) − W_T(x)) + 2K₁′W_T′ + K₁W_T″|,
     with z = x + is. Every term carries a factor (π/L)².
   Sketch [C]: so for bounded y the extra charge over all of R is O(y² log L/L²) relative to Δ(y) ≍ y², which tends to 0 uniformly.
   For raw-deep zeros (y up to L/4π) the relative perturbation is O((2πy/L)²), and (2πy/L)² ≤ 1/4 since 0 ≤ y ≤ L/4π. There the certified ratios are ≤ 0.5 (y ≥ 1, grid)
   and ≤ 0.78 (y ≥ 8), so the margins should absorb it.
   **This is not certified here.** Needed: an explicit perturbation lemma, i.e. (*) for K^{(T)} for all T ≥ T₀, with margin. The 2–5% margin of
   Theorem A at small y is the binding constraint.
2. **Two or more off-line pairs (T1e).** Not addressed. h3 T1f §6 shows that a pairwise position-space argument cannot close it.
3. **Prime side and Lemma Z** are taken from h3/T1f ([K] BGST Lemma 5 + [R] Lemma Z), not re-checked here.
4. **Trust base.** Correctness of Arb (python-flint 0.9.0). The scripts implement the lemmas literally. The closed forms are cross-checked
   against independent quadrature.

## 10. Files
- `kern.py`: kernel definition, exact a₂, closed forms (Lemma 1), ball evaluation of G and all derivatives.
- `check_closed_form.py`: independent mpmath quadrature check (PASS).
- `cert_kernel.py`: Lemma 2 (ALL PASS); writes `kernel_constants.json`.
- `certlib.py`, `common.py`: Taylor-box sign certification, constants, Lemma 4/5 bounds.
- `small_y.py`: Lemma 6. `grid.py`: Lemma 8 (logs `grid_*.log`, run outputs `run_grid_*.out`). `large_y.py`: Lemma 9.
- `run_all.py`: driver. `fastnum.py`, `explore_R.py`, `sanity_adversary.py`: floating-point exploration only (not proof).
