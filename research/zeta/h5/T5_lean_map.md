# T5 — Map of the Lean artifact (zeta23)  [h5]

Root: `$S/anth-fm/formal-math/zeta23/` ($S = scratchpad of the lead). ~103k lines, sorry-free, no axioms
(README, AUDIT.md). Read-only survey; nothing built.

## 1. Trusted statements (`Challenge.lean`, 17 theorems, Mathlib-only definitions inlined from `ChallengeDeps.lean`)
Counting functions: `Ncount` (with multiplicity, `analyticOrderAt` of `riemannZeta`), `Ndist`, `N0star`, `N0simple`;
`…L χ` analogues for `DirichletCharacter.LFunction χ`. "liminf ≥ c" is the ε-form
`∀ ε>0, ∃T₀, ∀T≥T₀, (c−ε)·N(T,2T) ≤ X(T,2T)`.

| name | constant | window |
|---|---|---|
| two_thirds_on_critical_line(_cumulative) | N0star ≥ 2/3 | flat ψ0 |
| two_thirds_simple_on_critical_line(_cumulative) | N0simple ≥ 2/3 | flat |
| five_sixths_distinct(_cumulative) | Ndist ≥ 5/6 | flat |
| montgomery_taylor_on_critical_line | N0star ≥ 2 − 1/cMT (0.67250) | ψ_MT |
| montgomery_taylor_simple_on_critical_line_mult(_cumulative) | N0simple ≥ 2 − 1/cMT | ψ_MT |
| montgomery_taylor_distinct_mult(_cumulative) | Ndist ≥ 3/2 − cMT⁻¹/2 (0.83625) | ψ_MT |
| dirichlet_* (6 theorems) | same constants, for each FIXED primitive χ mod q>1, dyadic only | both |

`cMT := √2·tan(1/√2)/(1+tan(1/√2)/√2)`. Extra, outside the Palomar set: ξ′ (Challenge/XiPrime.lean: 0.85838/0.92919,
quartic 0.86864/0.93432) and the PairCeiling (bandwidth-one ceiling 0.6818287, conditional on `EnclOK` enclosures).
NOT in Lean: the family-average result of Remark `rem:Davg` (0.811 / 0.905) — the paper says so explicitly.

## 2. Pipeline and exactly where each constant enters
The development is split into an arithmetic-free zero side, an abstract certificate, and a prime side that only
produces two numbers (tr, ‖·‖_F²).

1. **Linear algebra** (`LinAlg/*`, `ZeroSide/RankTraceMult.lean`). General multiplicity-aware Lemma R, any real c>0
   (`rank_trace_mult_k_le`):  `2c·tr(P+Q) − ‖P+Q‖_F² ≤ Σ_j k_c(m_j) + c²·b`, `k_c(p)=c²−((c−p)_+)²`, for
   P = Σ m_j v_j v_j* with ‖v_j‖² ≤ 1 and n₊(Q) ≤ b. Integer bookkeeping: c=2 → 3·#{m=1}+4·#{m≥2} (`sum_kc_two_nat`);
   c=3 → 5,8,9 (`sum_kc_three_nat`). Tightness: `ZeroSide/TightMult.lemmaR_tight`.
   **The parameter c (2 for simple, 3 for distinct) enters here** (`ZeroSide/Mult.lean: mult_two, mult_three`).
2. **Zero side** (`ZeroSide.lean`, `ZeroSide/Mult.lean`, `Tail*`, `Assembly/Inputs.lean`): over an ABSTRACT
   `ZeroConfig` (set of points in strip, multiplicities, ρ↦1−ρ̄ symmetric, locally finite). Produces
   `BlockInputs`, `TailInputs θ₀`, and the "seam" inequality (`Assembly/SeamMult.lean: seamA_mult2/3`):
   `4·tr Ĝ − ‖Ĝ‖² − 2N − 3·N_II − (tail) ≤ N0simple`  and the c=3 analogue `6tr − ‖‖² − 3N − 5N_II … ≤ 2·Ndist`.
   No arithmetic. Window enters only via Poisson identity (`PoissonSq`, `PhiHatConj/Real`).
3. **Certificate** (`Assembly/Certificate.lean: count_certificate`, `CertificateC3.lean: count_certificate_c3`):
   **κ is an abstract real.** Hypotheses: seam (h0), tail→0, N_II = o(N), `tr Ĝ ≥ (1−δ)N`, `‖Ĝ‖_F² ≤ (κ+δ)N`
   eventually for all δ. Conclusion: `(2−κ−ε)N ≤ lower` (resp. `(3/2−κ/2−ε)N ≤ Ndist`). No prime side consumed.
4. **Prime side** produces κ:
   * flat: `PrimeSideB.lean` `Data/Facts → TracesBounds`; κ = 1/F(λ₁) = 1/λ₁ + λ₁/3 (→ 4/3 at λ=1).
   * window-general: `ThmD/Traces.lean` `DataD/FactsD → ThmD/AssemblyD.lean: TracesBoundsD`, κ = 1/cRatio,
     `cRatio(λ₁;a,b,J) = λ₁a²/(b+λ₁²J)`, a=∫ψ, b=∫ψ², J from Σ a_n² g(log n) = (L³/2)J + O(L²) (`ThmD/PP.lean`).
     Variational problem & closed form c*_λ: `ThmD/Functional.lean` (pure calculus). Window admissibility:
     `ThmD/WindowCore.lean: AdmWindow v L w c` (even, 0≤v≤1, C², supp ⊆ [−L/2,L/2], L¹ derivative bounds) +
     requirement 1/2 ≤ b ≤ a ≤ 1.
   * **The bandwidth restriction λ ≤ 1 is hard-coded**: `Params.Valid.lam_le_one`, `Facts.lam_le_one`, and the
     off-diagonal input `prop_PP : 𝓜[P_X,P_X] = (T/π)Σ Λ²/n·g(log n) + O(L²X)` proved via Montgomery–Vaughan
     (`MV/Final.lean: mv_hilbert`, constant 13 — any constant suffices) in `PrimeSideB/PPOffDiag.lean`.
     For X = T^λ, λ>1 the O(L²X) error exceeds the main term T·L³.
5. Endgames: `Assembly.lean`, `FinalMult.lean` (flat; λ→1⁻ limit `eps_form_twoThirds`), `ThmD/Endgame,Limit,Mult`
   (cRatio → c*_λ, λ → 1⁻), `ThmE/*` (fixed q: `AssemblyQ.lean` with ℓ_{1,χ}=log(qT/2π)+2log2−1, all errors O_q),
   `ThmDE/*` (MT window for L(s,χ)).

## 3. Reusable for a strengthened theorem
* **Any improvement that is "a better upper bound for ‖Ĝ‖_F² at trace ≈ N" plugs into `count_certificate` unchanged**
  (zero side, tail, seam, certificate all reusable). Needed: a new `TracesBounds`-type package with smaller κ.
  But within Fourier support [−1,1] and window-type certificates, κ ≥ 1/c₁* (CCLM17 Cor.14; `Functional.lean`), so
  improvement for ζ requires either support > 1 (no unconditional input; would replace `prop_PP` for λ>1) or a
  *different certificate*.
* A different certificate (e.g. several windows / general form-factor functional, the class bounded by the
  PairCeiling 0.6818) needs a NEW linear-algebra lemma: Lemma R uses only (tr, ‖·‖_F²). The PairCeiling files
  (`PairCeiling/Stability.lean`) formalize the *upper* bound for such certificates, not a lower-bound mechanism.
* General-c Lemma R is already there; [C]/quick check: for the simple-zero count with κ=4/3 the ratio
  (2c−κ−c²/2)/(2c−1−c²/2) is maximized at c=2 (0.660 at c=1.8 and 2.2) — no gain from non-integer c.
* q-uniform pieces already exist for families: `ThmE/Hypotheses.lean` `GammaFactsChiBounded`,
  `ChebyshevMertensCoprimeBounded`; `ThmE/PPChi.lean: prop_PP_chi_uniform` (constants uniform in (q, unimodular c),
  but still λ ≤ 1 and MV). Gevrey taper profile exists (`Taper/Gevrey.lean`, `GevreyPhi.lean`: profile ϱ₂ with
  Gevrey-2 bounds), whose stated purpose is the q-aspect tail; the Gevrey *tail lemma* itself is only used in XiPrime
  (`XiPrime/FamilyFlat.lean`), not for a Dirichlet family.
* The ξ′ development abstracts the prime side over a coefficient family (`XiPrime/Statement.lean: CoeffFamily`,
  hypotheses H1–H3 with diagonal density D): a template for running the device with non-Λ coefficients.

## 4. What a Lean proof of an improved constant would need
(a) ζ, beyond 0.6725: a new unconditional second-moment input with support >1 or a new certificate lemma — neither
    exists mathematically yet; Lean infrastructure is ready on the zero side (abstract κ).
(b) Dirichlet family average (Remark rem:Davg, 0.811/0.905): (i) family Gram matrix = block-diagonal over χ (zero side
    applies per block; rank/trace/‖‖² are additive — Lemma R applies to the direct sum verbatim, so the zero side is
    reusable with a `Fin`-indexed sum of ZeroConfigs); (ii) λ up to 3/2: replace MV in prop_PP by a weighted large
    sieve over Farey fractions with an explicit asymptotic constant (not in Mathlib; Mathlib has no analytic large
    sieve as far as I know); (iii) all O_q constants uniform with T a power of log Q (Gevrey tail lemma for the
    Dirichlet setting, explicit formula uniform in q); (iv) the cRatio functional at λ=3/2 (the flat-window formula
    κ = 1/λ + λ/3 is generic in λ in `PrimeSideB`, only the `lam_le_one` field blocks it).
(c) The PairCeiling's `EnclOK` is the only non-kernel-checked numerical input anywhere in the repository.
