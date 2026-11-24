# Referee report: the price-method link (b2, two-proofs, x6, x5, x3)

24 Nov 2026. Adversarial review against the paper's text (`scratchpad/vpvnp/paper.txt`: Def. 2.1/D.1, Thm 2.2/D.2, Lemmas
A.2–A.3, Def. A.4, Props A.5/A.7, B.2–B.3, C.3, Lemmas E.7–E.8, Prop. E.9, Thm K.7) and our engine accounting
(`engine3-open-door.md` §1.6–1.7, `engine3-delta3-proof.md` Theorem 1). Scripts I re-ran: `vpvnp/b2/verify_flat.py` (all
values reproduced) and `next/x6/code/ladder.py` (`ladder.out` reproduced). New check: `scratchpad/ref/planar.py`. It confirms
the planar Δ₃ assignment exactly: b = (3√3, 3√3, 3√3). It also shows 3√3 is the best min over all hub labelings on one triangle.

## Verdicts

| # | claim | verdict |
|---|---|---|
| 1a | multi-hub routing (Lemma 1) and (★) with one spectral point for all merges | CORRECT |
| 1b | flat floor Eλ/√p [FH]; Δ₃ three merges 1/√3 [PH]; crossing 2‖λ‖₂ [PH] | CORRECT (fix the quantifiers, below) |
| 1c | win-win (Prop. 4) | CORRECT WITH FIXES (it is sharper than stated, and the field must be stated) |
| 1d | Theorem 1 over every field via Strassen's ζ^θ | CORRECT |
| 2 | two-proofs Prop. 1 and Cor. 1′ | CORRECT WITH FIXES (needs E.7′ written out; the c1 detour is not needed) |
| 3a | x6 Prop. 1 (ρ_× = ¼ sup(t+σ)) | CORRECT WITH FIXES (limsup/liminf; monotonicity) |
| 3b | x6 ladder theorem | CORRECT WITH FIXES (hypothesis (T4) is literally false; the conclusion survives) |
| 4a | x5 §2 (α, β) | CORRECT WITH FIXES (one broken inequality chain; the "iff" holds only for α ≤ 1) |
| 4b | x3 §2 item 2 ("on the threshold") | CORRECT WITH FIXES (the "i.e." is wrong; only the middle piece is on the threshold) |

Nothing is BROKEN.

## What I checked, and why it holds

**Hubs and one spectral point.**
- A K_r tensor network on the groups is a restriction of the graph tensor with one hub per group. Each hub applies its
  node tensor as a functional, which is the proof of Lemma A.3 verbatim.
- Hubs of other merges are extra parties of dimension one, so they cost nothing.
- The paper itself does exactly this in the proof of B.3: one φ, four hubs (o, o′ for cut (c) and w, w′ for cut (b)), one
  selected Ψ_N, and both bounds applied to that same Ψ_N. So "one piece, every merge at once" is legitimate.

**Prices.**
- FH is applied directly to the finite set of legs and hubs. No closure operation is needed.
- Hubs that coincide are handled by pull-back.
- Star metrics are prices over every field: take p = ζ^θ∘(push-forward to the groups), which is an upper functional, and
  apply A.5 with the triple trick of A.7. Here C is oblique, so ζ^θ(C^m) = ζ^θ(C)^m.
- Line prices are prices over every field: by C.3 the geodesic in the CAT(0) completion of the cut metric is an interval.

**Engine accounting.**
- (★) lower-bounds the D1 cost Σ log₂(bond dimensions), minimised over all network representations of the grouped piece A_n.
  Every charge in Def. 7 / §1.7, including the naming term ν·t·log₂T, is an upper bound on that quantity.
- So "accounted cost below the floor" implies "D1 cost below the floor". The direction is right.
- The requirement |I| = 2^{o(λ)} matches Def. 7(c).

**The o(λ) terms.**
- The scale c = c(M, ε) does not depend on λ. So c·log T = o(λ) for fixed (M, ε).
- One then takes M → ∞ and ε → 0 slowly as λ → ∞. Write this as a liminf statement (below).

**Theorem 1 over every field.**
- ζ^θ is monotone under restriction and subadditive (s = Σ s_j is a restriction of ⊕ s_j).
- ζ^θ ≤ Π_x rk_x^{θ_x} ≤ 2^{2c/3}, and ζ^θ = N^{2E/3} on f_C, which is oblique.
- Strassen 1991 works over any field. The flag can be removed.

**two-proofs Prop. 1.**
- Rescaling E.9 by 2 gives c·g_φ({±e_i}) ≤ 2√D + ε.
- E.7 as stated allows functionals only *outside* P. The terminal maps of N_a act *at* P. The extension is valid: in the proof
  of E.7 each party of P holds the word number and can apply the word-dependent product of its maps. It must be stated as a
  lemma (E.7′), not as an aside.
- The closure step is [O]'s and is cited, not checked.
- Cor. 1′ follows directly: a √D-shortening gives ¬FH, and Thm D.2 then gives contracting. The detour through c1 Prop. 1 is
  correct but unnecessary.

**x3 §2 item 2: hub cost.** I re-derived g(ℓ) = √2(ℓ + √(4m² − ℓ²)) for ℓ ≤ √2m, which matches x3 and x5. For general D I
re-derived the half/half hub cut cost m[2√(1−1/D)·√(D²−β²) + 2β/√D], with break-even at β = √D. The optimal hub stays inside
the ball exactly when β ≤ √D.

**Direction of the win-win.** thm_alt says that at least one hypothesis holds, so ¬FH ⇒ contracting. That is used correctly.
FH ⇒ PH, so ¬PH ⇒ contracting as well.

## Issues by severity

**Moderate.**
1. **x3 §2 item 2 and b2 Prop. 4: the wrong criterion is called sharp.**
   - The sharp refutation of FH/PH is: *every piece has min_k c_k(A_i) ≤ (E/√p − η)λ.*
   - This is strictly weaker than ρ_× < 1/√2 or V < (E/√p)λ.
   - Counterexample to x3's "i.e.": on the crossing, take a family whose pieces have costs (1.3λ, 2λ) or (2λ, 1.3λ). It refutes
     PH, yet ρ_× = 0.825 > 1/√2. Flattening and Lemma′ allow it, since 1.3 + 1.3 ≥ 2.
   - Consequence for the win-win: the two directions are asymmetric. An engine improvement implies contracting, but
     refuting FH is a cheaper target than improving the engine.
2. **x5 §2, "General F".**
   - The step F(4E)/(4F(E)) ≥ ½ needs F(4E) ≥ 2F(E). Flattening gives only F(4E) ≥ 2λ, and λ ≤ F(E) points the wrong way.
   - Corrected chain: ρ_cert ≥ F(2E)/(2λ), and F(2E)² ≥ F(E)F(4E) ≥ λ·2λ, so ρ_cert ≥ 1/√2.
3. **x6 ladder theorem, hypothesis (T4).**
   - N(ε)/ε is never non-decreasing for a discrete spectrum: it falls between level jumps. A single ladder already gives
     N(1.5) = 1 < 1.5·N(1).
   - Replace (T4) with N(su) ≥ s·N(u) − (s+1)f for f ladders. The scaling lemma then holds up to an additive O(f), which is
     negligible at the saddle point.
   - F = Ŝ(1 − o(1)) needs a citation (a Meinardus-type result) or a proof.
   - The "two-band sharpness" values 0.65–0.69 come from bounded spectra, whose symbol counts saturate. They are not
     asymptotic families and are not evidence.

**Minor.**
- **x6 Prop. 1.**
  - The (≤) direction needs σ defined with limsup, or both sides taken along one common sequence of Q. As written (liminf),
    different t_k may be good on different subsequences.
  - State that σ is non-increasing, and that σ(0) = 2 (from Lemma′). This justifies R₀ = 0.
- **x6 consequence 3.** The crossover "n ≈ 11" ignores the poly(Θ) factors, which converge very slowly (x5 gets 0.80 at
  E = 4000). The asymptotic refutation of ⌈n²/4⌉ stands. x3 §2.4 and §6 should be updated to match.
- **x5 §3b.** The "iff" region holds only for α ≤ 1. For α > 1 the end pieces dominate, ρ_cert = β^α/4, and the region is
  2 ≤ β^α < 2√2. The phrase "equivalent to the open problem" is overstated: such an identity is only *sufficient* for
  contracting.
- **x3 §2 item 2, details.**
  - The saving near β = √2 is (√2 − β)²·m. The figure 0.875 is a secant value at β ≈ 1.2.
  - Only the middle piece N = Θ/2 sits on the threshold. All other pieces are below it.
  - "b2's 1/√p again" is an analogy, not a theorem.
- **Rhetoric.** b2's "curvature can never produce a bound" is not a theorem. Drop it.

## Corrected statements (ready for a paper)

**Theorem (flat floor).**
- *Setting.* Let k be a field and C a configuration with E edges, each crossing each of the merges P_1, …, P_p (r_k groups).
  For a sequence λ → ∞, let Σ_{i∈I_λ} A_i = d_λ·f_C with d_λ ≠ 0 and |I_λ| = 2^{o(λ)}.
- *Hypothesis.* FH holds over k.
- *Conclusion.* liminf_λ max_i min_k c_k(A_i)/λ ≥ E/√p.
- *Planar cases.* If p = 2 and r_1 = r_2 = 2, FH may be replaced by PH. The same holds for Δ₃ with rows, columns and diagonals
  (bound 3√3).

**Theorem (win-win).**
- *Hypothesis.* There are η > 0 and families as above in which every piece has min_k c_k(A_i) ≤ (E/√p − η)λ.
- *Conclusion.* FH fails over k and over every extension field. Hence the contracting hypothesis holds over k̄ (Thm D.2), and
  Thm K.7 gives PERM_m (HC_m in characteristic 2) circuits over k of size at least 2^{c(log m)²/log log m}.
- *Sufficient conditions.* V < (E/√p − η)λ, or, for two merges, Def. 7 with ρ < 1/√2.

**Prop. 1′ (two-proofs).**
- *Hypothesis.* FH holds over K, and C_{D,m} = Σ_{a≤A} N_a exactly over K, with every N_a a network in the unit ball of cost
  ≤ w.
- *Conclusion.* 2Dm ≤ w + 2√D·log₂A.
- *Corollary.* Any such identity over any field with w + 2√D·log₂A < 2Dm proves contracting over the algebraic closure of
  that field.
