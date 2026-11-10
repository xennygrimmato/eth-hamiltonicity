# T3 — Dirichlet families on average via the rank–trace device  [h5]

Scripts: `h5/family_opt.py` (window QP, active set), `h5/family_check.py` (re-evaluates the explicit optimal step window
on finer grids), window saved in `h5/family_window_lam1.5.txt`.
Prior art (h2 notes 6, 11): A–F Remark rem:Davg claims 0.811/0.905 (proof omitted, weighted LS constant 1.263 unproved);
D'Souza repo: 0.7235 clean, 0.9059 using Jutila + Montgomery density theorems; CLLR (GRH) 11/12; Sono (GRH) 0.9323.

## 1. What transfers verbatim  [R] (trivial)
For each primitive χ the per-χ chain of the paper (Lemma R with P₁ = simple on-line part) is an inequality between
real numbers: N₀ˢ_χ(I′) ≥ 4 tr Ĝ_χ − 2N_χ(I′) − ‖Ĝ_χ‖²_F (and 2N_{d,χ} ≥ 4tr − ‖‖² − N for distinct).
Summing with any weights ω_χ ≥ 0:  Σω N₀ˢ_χ ≥ 4Σω trĜ_χ − 2Σω N_χ − Σω‖Ĝ_χ‖².
So a family theorem needs ONLY the family averages of tr and ‖·‖²_F — i.e. an upper bound for the family pair
correlation — and the rank–trace device removes GRH from the zero side exactly as for ζ. With
F̃(α) := any upper bound for the off-δ family form factor on |α| ≤ λ, the family constant is
2 − R(ψ),  R(ψ) = [∫ψ² + ∬F̃(|u−v|)ψ(u)ψ(v)]/(∫ψ)², ψ ≥ 0 even on [−λ/2, λ/2] (units of log Q).
Distinct: (3 − R)/2. (Lean: Assembly/Certificate.count_certificate is already κ-abstract; see T5.)

## 2. Where GRH enters CLLR, and why an asymptotic for 1<α<2 is out of reach  [C, with precise obstruction]
CLLR (arXiv 1211.6725) Prop. 1: the prime-side asymptotic Σ_q W(q/Q)/φ(q) Σ*_χ |Σ_p a_pχ(p)|² ~ f(α)N, f = min(|α|,1),
for |α| < 2. GRH is used (Lemmas 2.4 'sumnonprincChar', 3.1 'sumUerror', bound in S_{L_E}) only to bound
Σ_p Ψ(p)log p Φ(p/X)/√p ≪ Q^ε for NON-principal Ψ of SMALL modulus d (d ≤ Q/C in U_E, ae ≤ CX/Q in L_E).
Large sieve handles d ≳ X/Q = Q^{α−1}; moduli d ≤ Q^{α−1} need square-root cancellation for primes ≤ Q^α in
progressions mod d with power saving — beyond Siegel–Walfisz/BDH (unconditional error X²(log X)^{−A} in
Montgomery–Hooley). CIS Thm 2.2 (arXiv 1105.1176) gives the asymptotic for ARBITRARY coefficients only for N ≤ Q^{1−ε};
their N ≤ Q^{2−ε} theorems need L-function-structured coefficients, which Λ is not.
(Observation: in the exact identity S = Σ_d M(d)Σ_{Ψ mod d}|Σ a_pΨ(p)|², M(d) = Σ_c μ(c)W(cd/Q)/φ(cd), the full
contribution of a fixed small-conductor Ψ* telescopes, Σ_k M(d*k) = W(d*/Q)/φ(d*) = 0, up to coprimality corrections —
so the GRH need is an artefact of splitting by modulus; but I have no proof that avoids it.)
BUT: the device needs only an UPPER bound for ‖G‖², not an asymptotic. Hence §3.

## 3. Unconditional family theorem with the classical (Montgomery–Vaughan) large sieve  [C: proof sketch; constant N]
Family: primitive χ mod q, q ∈ (Q^{1−ε}, Q], weight ω_χ = 1/φ(q); heights (T,2T], T = (log Q)^B (B large);
Gevrey taper (Lean Taper/Gevrey.lean profile) so the tail E is O(X^{1/2}e^{−c(D₀w)^{1/2}}) = o(1) with D₀ = (log Q)^3.
Claim: for every λ < 2,
  Σω N₀ˢ_χ(T,2T) ≥ (2 − R_K(ψ) − o(1)) Σω N_χ(T,2T),  F̃(α) = α (α ≤ 1), Kα (1 < α ≤ λ),  K = 3/(2𝔖) = 3.1306,
𝔖 = Π_p(1 − p^{−2} − p^{−3}) = 0.479145. Optimised window [N]: **≥ 0.7523 simple and on the line, ≥ 0.8761
distinct** (λ ≥ 1.4; the curve is flat for λ ∈ [1.4, 2), e.g. λ=1.15: 0.7345; λ=1.3: 0.7512). No zero-density estimate.
Proof skeleton (each item replaces a per-χ sup bound of the ζ proof by a family-averaged bound):
 (a) Zero side per χ: verbatim (only Poisson identity + functional equation pairing).
 (b) Trace from the PRIME side, not Prop trace: tr(Ĝ+E) = ∫_I μ_χ + O(prime part); prime part averaged with
     |Σ*_χ χ(n)| ≤ Σ_{d|(q,n−1)}φ(d) and Brun–Titchmarsh: ≪ √X log Q/L = o(QTL) for λ<2. Then trĜ = tr(Ĝ+E) − tr E.
     (The zero-side Prop trace would fail: off-line zeros near the edges cost X^{1/2} ≫ T each.)
 (c) 𝓜[P,P] family: write it as (1/2π)∫ g(y)Σ_χ ω|Σ_n b_nχ(n)Î(y−log n)|²dy, g = ψ⋆ψ ≥ 0, Î(u)=∫_I e^{iτu}.
     Per scale y: localise to |log n − y| ≤ δ (tails have relative L²-mass O(1/(Tδ))). For e^y ≤ Q^{1−ε}: elementary
     diagonal dominance (off-diagonal ≪ N polylog ≪ Q). For e^y ∈ (Q^{1−ε}, Q^λ]: Gauss sums give
     Σ*_χ|Σc_nχ(n)|² ≤ (φ(q)/q)Σ*_a|S(a/q)|²; MV weighted large sieve [K: Montgomery–Vaughan, "The large sieve", Mathematika 20 (1973) 119–134, ineq. (1.6)/Thm 1 (scan OCR reads "(N + 3/2 δ_r^{-1})"; Selberg independently):
     Σ_r|S(x_r)|²(N + (3/2)δ_r^{−1})^{−1} ≤ Σ|c_n|² — constant to be re-checked] with δ_{a/q} ≥ 1/(qQ), N/q ≤ Q^{λ−1+ε} = o(Q):
     Σ_q φ(q)^{−1}Σ*_χ|…|² ≤ (3/2)Q(1+o(1))Σ|c_n|², vs harmonics Σ_q φ*(q)/φ(q) = 𝔖Q(1+o(1)) ⇒ factor K.
 (d) Sum-frequency terms O₂: integrate in τ′ exactly (boundary values at T, 2T), 1/log k = ∫₀^∞ k^{−u}du, then
     POINTWISE large sieve: O₂/main ≪ 1/(TL). 𝓜[μ,P]: first-moment bound as in (b): ≪ √X l log Q = o(QTL³).
 (e) Prop reduction errors E₁, E₂: replace B² = sup|ν_χ|² by the family average of |P_χ(τ)|² (pointwise LS: ≪ L²),
     giving ≪ L⁵ log L per unit family weight vs main TL³: needs T ≫ L² log L.
Gaps to close before [R]: write (c)'s localisation with explicit error terms; check MV constant 3/2 and the
Farey-gap bound for the restricted set; uniformity of the explicit formula in q (Lean ThmE has q-uniform pieces:
GammaFactsChiBounded, prop_PP_chi_uniform); the Gevrey tail lemma for L(s,χ).

## 4. Constants table  [N]  (family_opt.py; λ = sup of Fourier support, units log Q)
| F̃ on (1,λ] | input | best simple-on-line | distinct |
|---|---|---|---|
| Kα, K=3.1306 | MV weighted LS (this note) | 0.7523 | 0.8761 |
| Kα, K=4.1741 | classical (Q²+N) LS, weights q/φ(q) | 0.7348 | 0.8674 |
| Kα, K=1.263 | A–F's unproved weighted LS | 0.849 (λ→2), 0.834 at λ=1.5 | 0.925 |
| α (diagonal only) | hypothetical | 0.888 | 0.944 |
| min(α,1) | GRH (CLLR/Sono) | 0.9315 (λ→2; flat = 11/12 ✓) | 0.9657 |
Sanity: λ=1 reproduces 2 − 1/c₁* = 0.672500; GRH flat at λ→2 reproduces CLLR 11/12; GRH optimum ≈ Sono 0.9323.
Remark: with K=1.263 at λ=3/2 I get 0.834, not A–F's 0.811 — their weight (1−q/Q)² or where they apply K differs;
unresolved.

## 5. Assessment
* If §3 holds, 0.7523 beats D'Souza's hypothesis-free 0.7235 with a simpler mechanism (per-scale large sieve, no killed
  kernel), but is below the density-theorem route 0.9059. Main lever: the large-sieve ratio K (the window penalty
  for α>1 is second order at α=1, so ANY finite K gives a gain over 0.6725; 0.70 already at λ=1.05).
* Improving K: sharp weighted Farey large sieve (A–F's 1.263) is the obvious target: a weight vanishing at q=Q kills the
  spoke {1/q} near 1/Q. That is a clean, checkable extremal problem (max local density of weighted Farey points).
* Combining with density theorems (D'Souza's 'shell') can only raise K-type bounds toward f=min(α,1).
