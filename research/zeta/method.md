# The Alpöge–Furman 2/3 theorem: method digest, where the constants come from, and routes past 0.6725

Author: helper h1. Sources read in full: the paper LaTeX `paper-v5-draft18.tex` (cited below as [AF] with its own numbering:
Lemma 2.1 = Poisson–Gabor, Lemma 2.2 = Montgomery–Vaughan, Lemmas 3.1–3.4 = linear algebra, Props 4.1–4.3 + Cor 4.5 = zero side,
Props 5.2–5.6, Lemma 5.7, Thm 5.8 = prime side, §6 proofs, §7 sharpness/extensions), the Lean project `zeta23/` (README, `Zeta23/PairCeiling/*`,
`Zeta23/ZeroSide/*`, `Zeta23/LinAlg/*`), and the cited literature via web (CGdL arXiv:1810.08843, CLLR arXiv:1211.6725, BGST Acta Arith. 214,
BHB arXiv:1302.5018, Cheer–Goldston PAMS 118, Rudnick–Sarnak).
Tags: [K] known/sourced, [R] proved here (proof given), [N] computed here (script in `h1/`), [C] conjecture / assessment.

Scripts: `h1/support_curve.py` (proportion as a function of bandwidth), `h1/refined_ranktrace.py` (identity check, 3-point energy),
`h1/window_scan.py`.

---------------------------------------------------------------------------------------------------------------------

## 0. One-paragraph summary

[K] The proof is Montgomery's 1973 argument with one replacement. Montgomery (RH): `N* := Σ_γ m_γ ≤ Σ_{γ,γ'} g((γ-γ')logT/2π)` for `g ≥ 0`,
`g(0)=1`, `supp ĝ ⊂ [-1,1]`; the right side is evaluated by primes (`F(α)=|α|+δ`-mass on `[-1,1]`), giving `N* ≤ R·N` and
`N_s ≥ 2N − N*`. RH is used only to make every term `g(γ-γ')` real and nonnegative. [AF] write the same pair sum as `‖G̃‖²_HS` of a real
symmetric `d×d` matrix `G̃` (`d ≈ N(T,2T)`), a finite compression of Weil's Hermitian form with `tr G̃ ≈ N`, and replace "drop the
nonnegative off-diagonal terms" by a spectral inequality (rank–trace, Lemma 3.2) together with Sylvester's law of inertia: on-line
zeros contribute rank-one positive pieces, an off-line pair `{ρ,1−ρ̄}` contributes a block of signature (1,1), i.e. at most ONE positive
square for TWO zeros. Result: `N_0^s ≥ (2 − R(ψ))N`, `N_d ≥ ½(3 − R(ψ))N`, with `R(ψ_0)=4/3` (2/3, 5/6) and
`R(ψ_MT)=½+2^{-1/2}cot 2^{-1/2}=1.32750` (0.67250, 0.83625).

Headline findings of this note:
* [K] 0.6725 is the optimum over *windows* (CCLM17 Cor. 14, as cited in [AF] Thm A) and any certificate using only two trace moments at
  bandwidth one is ≤ 0.68183 ([AF] §7.2, Lean `PairCeiling.ceiling_law256`, modulo the non-kernel-checked `EnclOK`). So within the
  framework the total headroom for ζ is **< 0.0094**.
* [R] (§3, Route A) The rank–trace lemma is an *identity with an explicit nonnegative remainder*, and the remainder contains the
  spectrum of the Gram matrix of the simple on-line zeros, which off-line zeros cannot cancel:
  `N_0^s ≥ (2−R(ψ))N + Σ_{λ∈spec Γ} φ(λ−1) − o(N)`. This is the unconditional home of Cheer–Goldston's RH-improvement
  0.6725 → 0.672753. [N] A first crude evaluation gives `δ ≈ 2.5·10⁻⁵`, i.e. **0.67253 > 0.67250** unconditionally (to be checked
  independently). **See §0a: this mechanism is already in the literature (Knausgård arXiv:2610.08965, 0.67353) and my number is
  below the current record; it is a rediscovery, not a new result.**
* [R] The device's kernel is always `K = κ²` with `κ` positive-definite, so `K̂ ≥ 0`; hence the Chirre–Gonçalves–de Laat gain
  (0.6792 on RH, uses `ĝ ≤ 0` outside `[-1,1]` and `F ≥ 0`) cannot be imported, although `F ≥ 0` itself is true unconditionally.
* [C] Longer support for ζ in the t-aspect is out of reach (needs power-saving prime-pair information); in the q-aspect only large-sieve
  *upper* bounds on the form factor are unconditional, which is what [AF] Remark 7.2 ("0.811 / 0.905 on average") uses.
  [N] `proportion(c) = 1 − 1/(3c²)` (flat window, truth `F=min(|α|,1)`), 0.9323 at `c=2` with the optimal window.


## 0a. STATUS CORRECTION after reading the board (h2/novelty.md, h4 notes) — read this before §3

Written from the paper alone, §3 Route A presents the spectral-remainder idea as new. **It is not.** I confirmed through the arXiv API:
* [K] Knausgård, arXiv:2610.08965 (Oct 2026): `N_0^s/N ≥ 0.67353…`, `N_d/N ≥ 1645064/1960733 = 0.83900…`, by exactly this mechanism
  (the pair "energy" is known; nearby zeros contribute extra) and its abstract cites unverified reports of 0.673492.
* [K] Lamzouri, arXiv:2609.02882: Hilbert-space reproof of 0.6725/0.8362 plus 88.76% "simple or on the line".
* [K] Aryan, arXiv:2610.12853: odd (imaginary-part) companion of the Fejér identity; matrix exposition.
* Reported by h2/h4, not verified by me: a Lean leaderboard value 0.6736389, a repo ("stability refinement of rank–trace", 3/7
  consecutive zeros) at 0.67300853, and a ceiling ≈ 0.67383 for k-point local-interaction refinements.
Consequences for this note:
1. The record to beat is **≈ 0.67354–0.67364, not 0.6725**. My Theorem A.1 / δ ≈ 2.55·10⁻⁵ (0.672526) is an independent
   rediscovery of the weakest form of that line and is **below the current record**; it is useful only as a short self-contained
   proof of the mechanism (Prop 1.5 is, as far as I know from the sources I read, a cleaner statement than "stability refinement";
   I have not compared with the cited papers' lemmas).
2. If the reported ceiling 0.67383 for local-interaction refinements is right, Route A has < 3·10⁻⁴ left: **not worth more effort**.
   The remaining gap to the two-moment bandwidth-one ceiling 0.6818 needs a non-local certificate (Route F) or new data.
3. Route B: h2 reports D'Souza's unrefereed family paper (0.7235 unconditional; 0.9059 using Jutila/Montgomery hybrid zero-density
   theorems, bandwidth 5/3). That contradicts my [C] in Route B that the prime side beyond `α=1` needs quasi-GRH: my argument only
   shows that *term-by-term* bounds for small-conductor characters need a power saving; a density-estimate treatment of the
   explicit formula for the small moduli evidently avoids it. Treat my Route B obstruction as **withdrawn pending a read of that
   paper**; my table (0.9323 at `c=2`, 0.8657 at `c=1.5`, and 0.906 at `c ≈ 1.74`) is consistent with their numbers
   (my model, optimal window, truth `F`: `c = 5/3` → 0.8950, `c = 1.74` → 0.9052; so their reported 0.9059 corresponds to `c ≈ 1.75` in my normalisation, or to a stronger certificate at 5/3 — unresolved).
What I still stand behind: §1 (proof account), §2 (constants, Prop 2.1), Route C verdict for ζ in the t-aspect, the rank ceiling,
Route D/E assessments, and the table `proportion(c)`.

---------------------------------------------------------------------------------------------------------------------

## 1. The proof, self-contained

### 1.1 Explicit formula ([AF] §2.1) [K]
`γ_ρ := (ρ−½)/i ∈ ℂ` (real iff ρ on the line; `|Im γ_ρ|<½`), `f̂(ξ)=∫f(u)e^{-iuξ}du`. For even `F ∈ C_c²(ℝ)`:

    Σ_ρ m_ρ F̂(γ_ρ) = F̂(i/2)+F̂(−i/2) + ∫ F̂(τ) μ(τ) dτ − 2 Σ_n Λ(n) n^{-1/2} F(log n),          (EF)
    μ(τ) = (1/2π) Re Γ'/Γ(¼+iτ/2) − (log π)/2π  ≈ (1/2π) log(|τ|/2π).

If `supp F ⊂ [−log X, log X]` this is `Σ_ρ m_ρ F̂(γ_ρ) = ∫ F̂(τ) ν_X(τ) dτ`, `ν_X = μ + Π_X + P_X`,
`P_X(τ) = −(1/π) Σ_{n≤X} Λ(n) n^{-1/2} cos(τ log n)`, `Π_X` the pole term (`≪ √X/(1+|τ|)`).

### 1.2 Weil's Hermitian form [K]
`W(f,g) := Σ_ρ m_ρ f̂(γ_ρ) \overline{ĝ(\overline{γ_ρ})}` on `C_c²(ℝ)`; by (EF) with `F = f * g̃` it is computed from primes and Γ.
Positivity of `W` on all test functions ⇔ RH (Weil 1952; Bombieri 2000). For real `f,g`: `W(f,g)=Σ_ρ m_ρ f̂(γ_ρ) ĝ(γ_ρ)` (bilinear, no
conjugate), which is real because the functional equation pairs `γ ↔ γ̄` with equal multiplicity.

### 1.3 The finite compression ([AF] §2.2–2.3) [K]
Parameters: `l = log(T/2π)`, `L = l`, `X = e^L = T/2π`. Window `ψ ∈ C²[−½,½]`, even, `ψ>0`; `φ(u) = (C² taper)·ψ(u/L)^{1/2}`,
`supp φ = [−L/2, L/2]`, so `supp(φ*φ) ⊂ [−log X, log X]`. Grid `α_k = T + 2πk/L`, `0 ≤ k < d := ⌊LT/2π⌋ = N(T,2T)+O(L)`
(critical Gabor density). Test family `f_k(u) = φ(u)e^{iα_k u}`, `f̂_k(γ) = φ̂(γ−α_k)`. For each zero the vector
`v_ρ := (φ̂(γ_ρ−α_k))_{0≤k<d} ∈ ℂ^d` (real iff ρ on the line; `v_{1−ρ̄} = \overline{v_ρ}`). With `a := ‖φ‖²₂/L ≈ ∫ψ`:

    G̃ := (aL²)^{-1} Σ_{Re γ_ρ ∈ I'} m_ρ v_ρ v_ρ^T   (real symmetric d×d),   I' = [T−√T, 2T+√T),
    P := on-line part,  Q := G̃ − P (off-line part),  Ẽ := the same sum over Re γ_ρ ∉ I' (tail).

`G̃+Ẽ` is the Gram matrix `(W(f_k,f_{k'}))/(aL²)` of Weil's form, hence by (EF)
`(G̃+Ẽ)_{kk'} = (aL²)^{-1} ∫ φ̂(τ−α_k) φ̂(τ−α_{k'}) ν_X(τ) dτ`  ([AF] (2.9)).

Poisson–Gabor identity ([AF] Lemma 2.1) [K]: for all complex `z,z'`: `Σ_{k∈ℤ} φ̂(z−α_k)φ̂(z'−α_k) = L·\widehat{φ²}(z−z')` (no aliasing
because `supp φ` has length `L` and the grid step is `2π/L`). Consequences: (i) `v_ρ·v_ρ = aL²` up to edge truncation, so every zero
contributes 1 to `tr G̃`; (ii) for two zeros, `(aL²)^{-1} v_ρ·v_{ρ'} = κ(γ_ρ−γ_{ρ'})` with

    κ(x) := \widehat{φ²}(x)/‖φ‖²₂ = ψ̂(Lx)/ψ̂(0) · (1+O(1/L)),   κ(0)=1,  κ real even on ℝ, entire of exponential type L/2;

(iii) `‖G̃‖²_HS = Σ_{ρ,ρ'} m_ρ m_{ρ'} κ(γ_ρ−γ_{ρ'})²` (up to edge terms): the bilinear pair-correlation sum over **all complex zeros** with
kernel `K = κ²`, `K̂ ∝ ψ*ψ` supported in `[−L, L] = [−log X, log X]`, i.e. Montgomery's `|α| ≤ 1`.

### 1.4 Zero side: where Sylvester replaces RH ([AF] Props 4.1–4.3, Cor 4.5) [K]
* On-line zero: `v_ρ ∈ ℝ^d`, `m_ρ v_ρv_ρ^T ⪰ 0` of rank 1, trace `≤ m_ρ aL²`. So `P ⪰ 0`, `rank P ≤ N_0^*` (distinct on-line), `tr P ≤ N_0`.
* Off-line pair `{ρ, 1−ρ̄}`: `v_ρ = a+ib`, `m(v v^T + v̄ v̄^T) = 2m(aa^T − bb^T)` = pull-back of `m·diag(1,−1)` under `x ↦ (a·x, b·x)`.
  Sylvester's law of inertia in the form `n_+(A^*Q_0A) ≤ n_+(Q_0)` (Lemma 3.1) gives `n_+(Q) ≤ p := #off-line pairs`.
* Trace: `tr G̃ = N(I') + O(T^{1/2}L²)` (Prop 4.2; the `C²` taper is what makes the tail summable, Remark 4.4).
* Tail: `‖Ẽ‖_1 ≪ T^{-1/2}` (Prop 4.3).
* For simple zeros regroup: `P_1 :=` simple on-line part, `Q' := G̃ − P_1`; `Q'` is a pull-back of
  `⊕_{multiple on-line} m|x|² ⊕ ⊕_{pairs} [[0,m],[m,0]]`, so `n_+(Q') ≤ b := s_2 + p` (multiple on-line points + off-line pairs).
  Counting: `N ≥ s_1 + 2s_2 + 2p = s_1 + 2b`.

**What exactly replaces RH.** Under RH one uses `κ(γ−γ')² ≥ 0` termwise to discard `γ ≠ γ'`. Off the line `κ(γ−γ')²` is complex and
the termwise positivity fails (Goldston–Suriajaya). The replacement is: (i) inertia `n_+(Q') ≤ b` — a statement about the *signature*
of the off-line/multiple part, insensitive to how far off the line the zeros are; (ii) the rank–trace inequality, which never discards
off-diagonal terms but bounds `rank P_1` from `tr` and `‖·‖_HS` of the whole matrix. No zero-density estimate, mollifier or zero-free
region enters.

### 1.5 Rank–trace inequality ([AF] Lemma 3.2) [K], with the exact remainder [R]
Lemma 3.2: `P ⪰ 0`, `rank P ≤ r`, `n_+(Q) ≤ b` ⇒ `r ≥ 2 tr P + 4 tr Q − 4b − ‖P+Q‖²_HS`. Equality for `P = Π_1`, `Q = 2Π_2`,
`Π_1 ⊥ Π_2` projections. Scalar shadow: `m² ≥ 2m−1`; with simple zeros on the rank side and everything else charged 4: `m² ≥ 3m−2`.

**Proposition 1.5 [R] (identity).** Let `P ⪰ 0` with range projection `Π` (rank `r`), `Q = Q_+ − Q_-` the Jordan decomposition,
`Π_+` the range projection of `Q_+`, `b_+ = rank Q_+`. Then

    r = 2 tr P + 4 tr Q − 4 b_+ − ‖P+Q‖² + D,
    D = ‖P − Q_- − Π‖² + ‖Q_+ − 2Π_+‖² + 2 tr(P Q_+) + 4 tr Q_- − 2 tr(Π Q_-)  ≥ 0.

*Proof.* `‖P+Q‖² = ‖M‖² + ‖Q_+‖² + 2tr(MQ_+)` with `M := P − Q_-`, and `tr(MQ_+) = tr(PQ_+)` since `Q_+Q_- = 0`.
`‖M‖² = ‖M−Π‖² + 2tr(MΠ) − r` and `tr(MΠ) = tr P − tr(ΠQ_-)`. `‖Q_+‖² = ‖Q_+−2Π_+‖² + 4 tr Q_+ − 4b_+`. Substitute
`tr Q_+ = tr Q + tr Q_-`. Each term of `D` is `≥ 0` (`tr(ΠQ_-) ≤ tr Q_-`, `tr(PQ_+) ≥ 0`). ∎ (Checked numerically on 2000 random
instances, max error 3·10⁻¹², `h1/refined_ranktrace.py`.) This also reproves Lemma 3.2 without von Neumann's trace inequality.

**Corollary 1.6 [R].** With `φ(a) := a²` for `a ≤ 1`, `φ(a) := 2a−1` for `a > 1` (convex, C¹), and `p_1,…,p_r` the nonzero
eigenvalues of `P`: `D ≥ Σ_{i≤r} φ(p_i − 1)`.
*Proof.* `D ≥ ‖A − Q_-‖² + 2 tr Q_-` with `A := P − Π` (eigenvalues `p_i−1` on `ran P`, 0 elsewhere). By the Hoffman–Wielandt
inequality `‖A−Q_-‖² ≥ Σ_i (a_i^↓ − q_i^↓)²`, so `‖A−Q_-‖²+2trQ_- ≥ Σ_i min_{q≥0}[(a_i−q)²+2q] = Σ_i φ(a_i)`. ∎
The point: the remainder coming from the spectrum of `P` *cannot be cancelled by `Q`* (off-line or multiple zeros).

### 1.6 Prime side ([AF] §5, Thm 5.8) [K]
`‖G̃+Ẽ‖²_HS = (a²L²)^{-1} ∬_{I×I} \widehat{φ²}(τ−τ')² ν_X(τ)ν_X(τ') dτdτ' + O(N log L / L²)` (Prop 5.2). Split `ν_X = μ+Π_X+P_X`:
* `μ×μ` (Prop 5.3): `2π b L ∫_T^{2T} μ²` — Montgomery's `T^{-2|α|} log T` spike (the "δ-mass at α=0"); contributes `∫ψ²/(∫ψ)²·N`.
* `P_X×P_X` (Prop 5.4): diagonal `n=m`: `(T/π) Σ_{n≤X} Λ(n)² n^{-1} g(log n)`, `g = φ²⋆φ²`; off-diagonal bounded by the
  Montgomery–Vaughan generalised Hilbert inequality by `≪ L² X`. **This is the only place `X ≤ T` is needed** (diagonal `≍ T L³` must
  dominate `L² X`); it is Montgomery's `|α| ≤ 1`. Contributes `∬|u−v|ψ(u)ψ(v)/(∫ψ)²·N` (= `∫ K̂(α)|α| dα`).
* cross terms `≪ L²√X` (Prop 5.5).
Theorem 5.8: `‖G̃‖²_HS = (R(ψ)+O(1/L)) N(T,2T)`, with ([AF] Lemma 5.7)

    R(ψ) = [ ∫ψ² + ∬ |u−v| ψ(u)ψ(v) du dv ] / (∫ψ)²,    integrals over [−½,½].

This is Aryan (JNT 233, Cor. 1.4) / BGST (Acta Arith. 214, Thm 1) for the Fejér kernel, here for a general window.

### 1.7 Assembly ([AF] §6) [K]
`rank P_1 ≥ 2trP_1 + 4(trG̃ − trP_1) − 4b − ‖G̃‖² = 4 tr G̃ − 2 tr P_1 − 4b − ‖G̃‖²`, and `tr P_1 + 2b ≤ s_1 + 2b ≤ N`, so

    N_0^s + o(N) ≥ rank P_1 ≥ 4 tr G̃ − 2N − ‖G̃‖² = (2 − R(ψ) − o(1)) N.                       (chain)

Distinct zeros: the same line reads `3s_1 + 4b ≥ (4−R)N`; subtract `s_1+2b ≤ N`: `N_d ≥ s_1 + b ≥ ½(3−R)N`.
Dirichlet `L(s,χ)`, χ primitive fixed: identical (Thm B). Lean: `Challenge.lean` 17 statements, no hypotheses.

### 1.8 The extremal problem, stated cleanly [K]
**Problem W (window problem).** Minimise over even `ψ ≥ 0` on `[−½,½]`

    R(ψ) = ( ∫ψ² + ∬|u−v|ψ(u)ψ(v) ) / (∫ψ)².

Equivalently (Montgomery–Taylor): minimise `ĝ(0) + ∫_{-1}^{1} ĝ(α)|α| dα` over `g ≥ 0`, `g(0)=1`, `supp ĝ ⊂ [−1,1]`; here
`g = κ²`, `ĝ = ψ*ψ/(∫ψ)²`. Euler–Lagrange: `ψ(u) + ∫|u−v|ψ(v)dv = const` ⇒ `ψ''+2ψ=0` ⇒ `ψ_MT = cos(√2 s)`,
`R = ½ + 2^{-1/2}cot 2^{-1/2} = 1.3274993`. Certificate: `N_0^s/N ≥ 2−R`, `N_d/N ≥ (3−R)/2`.
[N] discretised QP (`h1/support_curve.py`) reproduces `1.327499`.
The only device-specific constraint beyond Montgomery–Taylor is `ψ ≥ 0` (needed for `φ=√ψ`); the MT optimum satisfies it, so nothing is lost.

**Problem C (general bandwidth-one certificate, [AF] §7.2 / Lean `PairCeiling`).** A pair `(c_0, r)`, `r` on `[0,1]`, is *valid* if
for every admissible marked configuration `c_0 + ∫ r dμ_conf ≤ p_1(conf)` (`μ_conf` its form-factor measure on `[0,1]`, `p_1` its
fraction of simple on-line points); its *value* is `c_0 + ∫_0^1 r(x) x dx`. Problem W is the sub-class `r = −ψ*ψ/(∫ψ)²`, `c_0 = 2 − ∫ψ²/(∫ψ)²`.
`sup(value) ∈ [0.67250, 0.68183]`.

---------------------------------------------------------------------------------------------------------------------

## 2. Where the constants come from; what is lossy; optimality

| constant | origin |
|---|---|
| 2/3 | `2 − R(ψ_0)`, `R(ψ_0) = 1 + 1/3`: 1 = δ-mass (`∫ψ_0²`), 1/3 = `∫_{-1}^{1}(1−|α|)|α|dα` (Fejér kernel against `F=|α|`) |
| 0.67250 | `2 − R(ψ_MT)`, `R(ψ_MT) = ½+2^{-1/2}cot 2^{-1/2}`; optimum of Problem W [K: CCLM17 Cor. 14 via AF Thm A; N: QP] |
| 5/6, 0.83625 | `(3−R)/2`: from `3s_1+4b ≥ (4−R)N` and `s_1+2b ≤ N` |
| `H(λ)=2−1/λ−λ/3` | flat window at bandwidth `λ ≤ 1` (`X=T^λ`), AF Remark 6.1; increasing on (0,1] |

Lossy steps, in order of importance:
1. **Bandwidth.** [K] `F(α)` is known only for `|α| ≤ 1` (`X ≤ T`). With the truth `F=1` on `1<|α|≤c` the flat-window certificate would
   be `1 − 1/(3c²)` (§3 Route C). This is the dominant loss (2/3 vs 1).
2. **Flat charge.** [K] Lemma 3.2 is sharp given only `tr`, `‖·‖_HS`, the block structure and `tr P_1 ≤ s_1`
   (Lean `ZeroSide.TightMult.lemmaR_tight`; AF §7.2(b)): extremal configuration = `⅔N` mutually orthogonal simple on-line zeros +
   `N/6` doubles (or off-line pairs of depth → 0), all spectrally orthogonal. [R] By Prop. 1.5 "sharp" means `D = 0`, which forces
   the Gram matrix `Γ` of the simple on-line zeros to be a projection, i.e. `κ(γ−γ')=0` for all pairs — impossible on a line at
   positive density unless the zero set of κ contains the difference set. This is the slack Route A harvests.
3. **Window.** Flat → MT gains 0.0058.

Is 0.6725 the optimum at support `[−1,1]`?
* [K] Among windows: yes (CCLM17 Cor. 14).
* [K] Among all two-moment bandwidth-one certificates: ≤ `0.6818287 + 2.55·10⁻⁶(|r'(1)|+∫|r''|)` (Lean, given `EnclOK`; the dual object
  is an explicit 256-periodic law of marked configurations with CUE form factor on the grid `j/256`, `j<256`, and simple fraction
  0.681828…).
* [K] Under RH, Cheer–Goldston (PAMS 118 (1993) 365–372) already exceed MT using only Montgomery's theorem: 0.672753, by keeping part
  of the dropped off-diagonal sum via "an elementary combinatorial argument"; they state that the best constant obtainable from
  Montgomery's theorem is an open problem in harmonic analysis. So the true bandwidth-one optimum lies in `[0.672753, 0.68183]` on
  RH, and [AF]'s 0.6725 is *not* the RH state of the art at bandwidth one.
* Comparison with Chirre–Gonçalves–de Laat [K, arXiv:1810.08843 Thm 1, Cor 2, Lemma 8]: on RH `N* ≤ 1.3208N`, `N_s ≥ 0.6792N`
  (GRH: 1.3155 / 0.6845); the MT value 1.3275/0.6725 is what they *improve*. (The task statement's "CGdL got 0.6725" is not accurate:
  0.6725 is Montgomery–Taylor; CGdL is 0.6792.) Their class: `g ≥ 0`, `g(0)=1`, `ĝ(x) ≤ 0` for `|x| ≥ 1` (Cohn–Elkies class), using
  `F ≥ 0` outside `[−1,1]`. It is not a bandwidth-one certificate in the sense of Problem C (the ceiling theorem does not apply to it)
  and 0.6792 < 0.6818 anyway.

**Proposition 2.1 [R] (why CGdL does not transfer).**
(a) *`F ≥ 0` is unconditional.* Let `w` be entire with `\overline{w(\bar z)} = w(z)`. For the zero multiset (symmetric under
`γ ↦ γ̄`) put `S(t) := Σ_ρ m_ρ w(γ_ρ)e^{itγ_ρ}`. Re-indexing `ρ ↦ 1−ρ̄` gives `\overline{S(t)} = Σ_ρ m_ρ w(γ_ρ)e^{-itγ_ρ}`, hence
`Σ_{ρ,ρ'} m m' w(γ)w(γ') e^{it(γ−γ')} = |S(t)|² ≥ 0`.
(b) *The device cannot use it.* In any compression of the above type the on-line part must be PSD for every real configuration, so
`κ` is a positive-definite function, `κ = μ̂` with `μ ≥ 0` (Bochner), and the pair kernel is `K=κ²`, `K̂ = μ*μ ≥ 0`. Positivity of
`F` outside `[−1,1]` enters `‖G̃‖²` with the wrong sign (it *increases* the upper bound one needs).
(c) *The pointwise inequality fails for CGdL kernels.* The device proves, for `g = κ²`, the configuration inequality
`s_1 ≥ 2N − Σ_{ρ,ρ'} m m' g(γ−γ') − o(N)` for all conjugation-symmetric configurations. For a periodic configuration consisting of
far-separated off-line pairs at depth `y` (`s_1=0`, two zeros per period) this forces `g(2iy) = ∫ ĝ(t)cosh(2yt)dt ≥ 1` for all
admissible `y`. If `ĝ ≥ 0` this holds (`≥ ĝ`-mass `= g(0)`); if `ĝ ≤ 0` on the outer part of its support (CGdL), `g(2iy) → −∞`. ∎
[C] Density theorems do not rescue (c): Selberg's `N(σ,T) ≪ T^{1−(σ−½)/4} log T` gives a proportion `≪ e^{-y/4}` of zeros at depth
`≥ y/log T`, against growth `e^{2cy}`.

---------------------------------------------------------------------------------------------------------------------

## 3. Routes past 0.6725, ranked

### Route A (rank 1) — keep the spectral remainder: the Cheer–Goldston improvement made unconditional
**Theorem A.1 [R, modulo the routine edge estimate (ii) below].** For every admissible window ψ, with
`Γ := (κ(γ_ρ−γ_{ρ'}))_{ρ,ρ' simple on-line, Re γ ∈ I'}` (an `s_1×s_1` PSD matrix with unit diagonal) and `φ` as in Cor. 1.6,

    N_0^s(T,2T) ≥ (2 − R(ψ)) N(T,2T) + Σ_{λ ∈ spec Γ} φ(λ − 1) − o(N),
    N_d(T,2T)   ≥ ½(3 − R(ψ)) N(T,2T) + ½ Σ_{λ ∈ spec Γ} φ(λ − 1) − o(N).

*Proof.* (i) Apply Prop. 1.5 + Cor. 1.6 to `(P_1, Q')`: `rank P_1 ≥ 2trP_1+4trQ'−4b−‖G̃‖² + Σ_{i≤r}φ(p_i−1)` (`b_+ ≤ b` by inertia).
The nonzero eigenvalues of `P_1 = UU^T` (columns `u_ρ = v_ρ/(aL²)^{1/2}`) are those of the Gram matrix `Γ̃ = U^TU`; zero eigenvalues of
`Γ̃` number `s_1 − rank P_1` and each has `φ(0−1)=1`, so `s_1 ≥ 2trP_1+4trQ'−4b−‖G̃‖²+Σ_{λ∈spec Γ̃}φ(λ−1)`. Now proceed exactly as in
[AF] §6 (`tr P_1 ≤ s_1`, `s_1+2b ≤ N`, Prop 4.2, Thm 5.8). (ii) `Γ − Γ̃` is the Gram matrix of the out-of-window tails
`(φ̂(γ−α_k))_{k∉[0,d)}`, PSD with trace `≪ T^{1/2}L²/L² ` by the computation in [AF] Prop 4.2 (real γ, so no `X^{1/2}` factor);
`A ↦ Σφ(λ(A)−1)` is 2-Lipschitz in trace norm on PSD matrices, so replacing `Γ̃` by `Γ` costs `o(N)`. ∎
Under RH with all zeros simple, `Σφ(λ−1) = ‖Γ−I‖² = Σ_{γ≠γ'}κ(γ−γ')²` when `spec Γ ⊂ [0,2]`: exactly Montgomery's dropped term.

**Lemma A.2 [K+R] (pinching).** `B ↦ tr φ(B−I)` is a convex trace function, so for any partition of the index set into blocks,
`Σ_{λ∈spec Γ}φ(λ−1) ≥ Σ_{blocks β} Σ_{λ∈spec Γ_β}φ(λ−1)` (eigenvalues of a pinching are majorised by those of Γ). For a block of two
points `{γ,γ'}`: `2κ(γ−γ')²`; for three points with small κ's: `2(κ_{12}²+κ_{23}²+κ_{13}²)`.

**Lemma A.3 [R] (pigeonhole).** In units of the mean spacing the `s_1` simple on-line zeros lie in an interval of length `N(1+o(1))`.
The consecutive triples `(γ_i,γ_{i+1},γ_{i+2})` have diameters summing to `≤ 2N`, so at least `s_1 − 2N/U` of them have diameter
`≤ U`, and at least one third of those are pairwise disjoint. Hence

    Σ_{λ∈spec Γ} φ(λ−1) ≥ ⅓ (s_1 − 2N/U) · μ_3(ψ,U),   μ_3 := min over 3 points of diameter ≤ U of Σ_{λ∈spec Γ_3} φ(λ−1).

`μ_3(ψ,U) > 0` iff the real zero set `Z_κ` of κ contains no triple `{a, b, a+b}` with `a+b ≤ U`.
[N] For `ψ_MT`: `tan(πx) = (√2/2πx)tan(1/√2)`, zeros `x_k = 1.0572, 2.0300, 3.0202, 4.0152, …` (`≈ k + 0.061/k`): never additively
closed. `μ_3(ψ_MT, 4) = 4.44·10⁻⁴` (attained near gaps (1.053, 2.012)); with `s_1 ≥ 0.6725N`, `U = 4`:

    δ ≥ ⅓(0.6725 − 0.5)·4.44·10⁻⁴ = 2.55·10⁻⁵,   i.e.  N_0^s ≥ 0.672526·N,  N_d ≥ 0.836263·N   [N, conditional on A.1–A.3].

(`h1/refined_ranktrace.py`; local minimisation by Nelder–Mead from a 0.1-grid — a rigorous interval-arithmetic minimisation is still
to be done.) Window scan over `cos(as)`: the optimum stays near `a=√2` (`h1/window_scan.py`).

Status and honesty: A.1 is a complete short proof modulo the standard edge estimate; A.2 is textbook; A.3 is elementary; the number
`2.55·10⁻⁵` is numerical. The gain is tiny, but it is a strict improvement of the record constant and of the paper's claim
"optimal among windows" (which remains true for the certificate `2−R(ψ)` but not for the method). It must be checked independently
before being called a theorem. Upper limit of anything of this kind: 0.6818 (ceiling theorem).
How far can it go? Under RH Cheer–Goldston reached `+2.5·10⁻⁴`. The real question is **Problem E (energy problem)**: for given ψ,

    E(ψ, σ) := liminf over real point sets of density σ of (1/#points)·Σ_{λ∈spec Γ}φ(λ−1),

and then maximise `2 − R(ψ) + σE(ψ,σ)` self-consistently in `σ = s_1/N`. Blocks larger than 3, pairs with a κ without small real
zeros (windows `ψ_MT + ε·τ`, `τ̂>0`; `R` is stationary at `ψ_MT` so the loss is `O(ε²)`), and using the multiple/off-line sites as well
(they also sit on the line `Re γ`) are all unexplored. [C] Realistic target `10⁻⁴`–`10⁻³`; reaching 0.68 this way is not plausible.

### Route B (rank 2 as a *new clean theorem*, not for ζ) — families, [AF] Remark 7.2
[K] CLLR (arXiv:1211.6725, Thm 2, Prop 1; GRH throughout): for primitive χ mod q, `q ~ Q` with smooth weights, the q-analogue form factor
is `f(α) = min(|α|,1)` uniformly for `|α| ≤ 2−ε`; Thm 1: `≥ 11/12` simple. GRH is used (Lemma 4) to bound
`Σ_p Ψ(p)Φ(p/X)log p/√p ≪ Q^ε` for the characters Ψ of the *complementary* moduli `e ≤ X/Q` in the asymptotic large sieve, and to
write the zero side as a positive sum.
[R/N] With the device and the *truth* `f`, flat window of width `c`: `R = 1 + 1/(3c²)` for `c ≥ 1`; optimal window at `c=2` gives
`R=1.0677`, i.e. 0.9323 simple-on-line and 0.9661 distinct (this reproduces Sono's 93.22% on GRH — a check of the script).
[C] **The device removes GRH from the zero side, but not from the prime side.** For `1<α<2` the off-diagonal is a variance of primes
in progressions to moduli `e ≤ X/Q` over intervals of length `eQ`; an *upper* bound of the true order needs a power saving for
`ψ(y+h,Ψ)−ψ(y,Ψ)` for characters of *small* conductor, i.e. quasi-GRH; unconditionally only *lower* bounds of Barban–Davenport–
Halberstam type are known in this range (Liu, Perelli, Friedlander–Goldston) — the wrong direction, since `K̂ ≥ 0` (Prop. 2.1(b)).
What is unconditional is the large-sieve *upper* bound `f(α) ≤ κ·|α|` on `1<|α|<2`; this is what [AF] Remark 7.2 uses
("constant 1.263 × number of harmonics", bandwidth 3/2, 0.811 simple / 0.905 distinct on average; details omitted, not in Lean).
[N] In the simplest model (`f ≤ κ|α|` on `1<|α|≤c`, exact `|α|` inside), `h1/support_curve.py` gives: κ=1.263: 0.834 at `c=1.5`,
0.849 at `c=2`; κ=1: 0.854 at `c=1.5`, 0.888 at `c=2`. I could not reproduce 0.811 from the remark's one-paragraph description, so
either the remark's accounting is more conservative or my model is too optimistic (e.g. the large-sieve constant may have to be applied
to the whole prime side); **a full proof of Remark 7.2 with the sharp weighted large-sieve constant is a clean, open, checkable
target** (already announced by [AF], so the novelty is the proof and possibly a better constant).

### Route C (rank 3) — longer support for ζ itself (subtask T4)
[R] Proportion as a function of the support `c` (truth `F=min(|α|,1)` on `[−c,c]`, flat window):

    proportion_simple(c) = 2 − 1/c − c/3  (c ≤ 1);   = 1 − 1/(3c²)  (c ≥ 1);   distinct = (1+simple)/2.

(`∫ĝ F` with `ĝ = c^{-1}(1−|α|/c)_+`: `1/c + (2/c)[∫_0^1 α(1−α/c) + ∫_1^c (1−α/c)] = 1 + 1/(3c²)`.) [N] optimal windows:

| c | 1 | 1.1 | 1.2 | 1.3 | 1.5 | 1.732 | 2 |
|---|---|---|---|---|---|---|---|
| simple, flat | .6667 | .7245 | .7685 | .8028 | .8519 | .8889 | .9167 |
| simple, optimal window | .6725 | .7323 | .7782 | .8141 | .8657 | .9042 | .9323 |
| distinct, optimal | .8363 | .8661 | .8891 | .9071 | .9328 | .9521 | .9661 |

So to pass the bandwidth-one ceiling 0.6818 one needs `c ≥ 1.016` (optimal window) — any `c>1` with a power saving would do.
What exists unconditionally for `|α|>1`:
* [K] Goldston–Montgomery (1987): on RH, `F(α)~1` on `[1,c]` ⇔ `∫_1^X(ψ(x+h)−ψ(x)−h)²dx ~ hX log(X/h)` for `h=X^θ`, `θ ≥ 1−1/c`.
  Unconditionally (Huxley-type density estimates) only `≪ h²X(log X)^{-A}`: converts to `F(α) ≪ T^{α−1}(log T)^{-A}`, useless.
* [K] Mean-value theorem / MV Hilbert inequality: for `X=T^c`, `c>1`, gives `∫_T^{2T}|Σ_{n≤X}Λ(n)n^{-1/2-it}|²dt ≤ Σ Λ(n)²n^{-1}(T+O(n))`,
  dominated by `X log X ≫ T log²T`: again `F(α) ≪ T^{α−1}`.
* [K] Lower bounds (GGÖS 2000 on GRH: `F(α) ≥ 3/2−|α|−ε` on `[1,3/2]`) and `F ≥ 0` (Prop 2.1(a), unconditional) have the wrong sign for
  the device (Prop 2.1(b)).
* [K] Aryan and BGST give exactly `|α| ≤ 1` (they *are* input (P)); nothing beyond.
* [C] Twisted second moments / Kloosterman (Conrey's 4/7 mollifier length; BCY, PRZZ) extend the length of a *mollifier* in
  `∫|ζ M|²`, not the length of `Σ Λ(n)n^{-s}` in a mean square; I see no way to convert them into an upper bound for `F` on `(1,c]`.
  A weighted form (Route D) trades mollifier length against bandwidth and runs into the rank ceiling below.
* [R] **Rank ceiling.** At bandwidth `λ` the matrix has dimension `d = ⌊λlT/2π⌋ ≈ λN`, so any rank certificate is `≤ λ`.
  Consequently the unconditional `k`-th traces `tr G̃_λ^k` (Rudnick–Sarnak range `λk<2`; RS Thm 1.1 is unconditional for complex zeros —
  they say so explicitly) can never certify more than `2/k ≤ 2/3` from a single matrix ([AF] §7.2(e) says "higher moments add nothing";
  this is the reason). Mixed traces `tr(G_{λ_1}G_{λ_2}G_{λ_3})`, `λ_1+λ_2+λ_3<2`, are unconditional and are *not* covered by the
  two-moment ceiling theorem; [C] the scalar accounting (`1_{m=1} ≥ [−m³+(2+r)m²−2rm]/(1−r)`, giving `N_s ≥ (4−R_3)N/3` and
  `N_d ≥ (7−R_3)N/6` where `Σ_{distinct}m³ ≤ R_3N`) needs `R_3<2`, whereas the GUE value at full bandwidth 1 is already `m_3(1)=2`
  ([AF] §7.2(f)) and is larger at total bandwidth 2. So no gain is expected; a definitive computation of `inf R_3` is a cheap
  experiment.
Verdict [C]: for ζ in the t-aspect no usable unconditional information beyond `|α| ≤ 1` exists or is in sight.

### Route D (rank 4) — importing CGG / Bui–Heath-Brown (19/27 on RH)
[K] BHB (arXiv:1302.5018) = CGG's method without GLH: `N_s ≥ |Σ_ρ ζ'(ρ)B(ρ)|² / Σ_ρ|ζ'(ρ)B(ρ)|²` (Cauchy–Schwarz over zeros, mollifier
`B` of length `T^{1/2−ε}`), both sums evaluated by contour integration. RH is used to write `|ζ'B(ρ)|² = ζ'B(ρ)·ζ'B(1−ρ)` (an
analytic function of ρ), i.e. to identify the computable sum `A_2 := Σ_ρ a_ρ \overline{a_{ρ^*}}` (`a_ρ=ζ'(ρ)B(ρ)`, `ρ^*=1−ρ̄`) with
`Σ|a_ρ|²`.
[R] Formally this is the same place where [AF] replace RH: `A_2 = a^* J a` with `J = I_{on} ⊕ swap_{off}`, signature (1,1) on each
off-line pair. But the device does **not** apply: BHB have one vector `a` and two numbers `(A_1, A_2)`, no trace normalisation; an
adversary with off-line pairs `a_ρ ≈ −a_{ρ^*}` lowers `A_2` arbitrarily below `Σ|a_ρ|²` without changing the on-line data, so no
lower bound on on-line simple zeros follows from `(A_1,A_2)` alone.
[R] A matrix version exists: `G' := Σ_ρ a_ρ v_ρv_ρ^T` (non-symmetric weights). For any matrix `rank ≥ |tr|²/‖·‖²_HS`, multiple zeros drop
out (`a_ρ=0`), so `N_s ≥ |Σ_ρ a_ρ|² / Σ_{ρ,ρ'} a_ρ\overline{a_{ρ'^*}}κ(γ_ρ−γ_{ρ'})²` — every quantity analytic in the zeros, hence
unconditional *if* the weighted pair sum can be evaluated. [C] It needs the mean square over `|t| ≤ λ log T` of the discrete twisted
moment `Σ_ρ ζ'(ρ)B(ρ)e^{itγ_ρ}` (a Landau–Gonek formula with weight `ζ'B`), with total length `λ+θ` constrained, and is capped by the
rank ceiling `λ`; with `λ ≈ 0.7`, `θ ≈ 0.3` the mollifier is too short for 19/27. No gain expected; left to h4 (T2).

### Route E (rank 5) — combining with Levinson–Conrey (5/12, PRZZ)
[C] No combination found. (i) The two methods bound the same set from below; 2/3 > 5/12 and nothing is additive. (ii) The
Farmer/Feng–Wu trick (zeros of `ξ^{(j)}` on the line) controls multiplicities, but the extremal configuration of the chain has only
doubles and shallow off-line pairs; a double zero of ξ is a *simple* zero of `ξ'`, and non-real zeros can only decrease under
differentiation, so information on `ξ'` (even [AF]'s 0.868 simple on-line zeros of `ξ'`) gives no constraint on it. (iii) A joint
argument would be a mollified pair correlation, i.e. Route D.

### Route F — general bandwidth-one certificates not of spectral-remainder type
[C] The LP of Problem C has room up to 0.6818, and for the discretised 256-periodic problem a certificate with value ≈ 0.6818 exists by
finite LP duality — but only validated against marks {1,2} on a grid; validity for all real configurations, all multiplicities, and
all conjugation-symmetric complex configurations is a many-body inequality for which the only known proof technique is the matrix
identity of Prop 1.5. Route A is the part of this that can be proved today.

---------------------------------------------------------------------------------------------------------------------

## 4. Plan for the most promising route (Route A)

Goal: **Theorem.** `liminf N_0^s(T,2T)/N(T,2T) ≥ 2 − c_MT^{-1} + δ_0` and `liminf N_d/N ≥ ½(3−c_MT^{-1}) + δ_0/2` with an explicit `δ_0>0`
(first target `δ_0 = 2·10⁻⁵`; stretch `10⁻⁴`).

1. **First lemma to prove (and to have checked by a second helper): Prop 1.5 + Cor 1.6** — pure linear algebra, ~15 lines, already
   verified numerically. It is also a 1-file Lean target (`Zeta23/LinAlg/RankTrace.lean` has the pieces: Jordan decomposition
   `HermitianPosPart.lean`, projections; Hoffman–Wielandt may be replaced by the weaker `D ≥ ‖P−Π‖² − 2tr((P−Π)Q_-) + 2trQ_-`,
   which suffices when `‖Γ‖_op ≤ 2` on the blocks used).
2. **Edge lemma**: `‖Γ−Γ̃‖_1 = o(N)` (copy of [AF] Prop 4.2 for real γ) and the 2-Lipschitz property of `tr φ(·−I)`.
3. **Assembly** (Theorem A.1): verbatim [AF] §6 with the extra term.
4. **Energy lemma**: pinching (Lemma A.2) + pigeonhole (Lemma A.3) + a *rigorous* lower bound for `μ_3(ψ_MT,4)`:
   interval arithmetic on the compact set `{g_1,g_2 ≥ 0, g_1+g_2 ≤ 4}` using the closed form
   `κ(x) = [s(2πx−√2)+s(2πx+√2)]/(2s(√2)·…)`, `s(v)=sin(v/2)/v`; near `g_i → 0` use `κ → 1` (eigenvalue → 2, `φ ≥ 1`).
5. **Numerical experiment to run first** (cheap, decides how much is there):
   (a) rigorous-ish global minimisation of the `k`-point energy `μ_k(ψ,U)` for `k=2,…,6` on a fine grid + local refinement, for
       `ψ ∈ {cos(as)}` and `ψ_MT + ε·τ` (τ = triangle, `κ_τ = sinc²`), reporting `2−R(ψ)+δ(ψ)`;
   (b) the infinite-volume Problem E by simulated annealing on periodic point sets of density `σ ∈ [0.67,1]` with pair/spectral
       energy `Σφ(λ(Γ)−1)` — this gives the true limit of Route A for each ψ;
   (c) the LP of Problem C restricted to certificates `r = −ψ*ψ + (remainder terms)`, to see how much of the gap to 0.6818 the
       spectral remainder can explain.
6. Independent adversarial review: try to break A.1 with a configuration in which off-line pairs sit between close simple on-line
   zeros (the claim is that `Q'` cannot cancel `Σφ(p_i−1)`; Cor 1.6 is where this is proved).

Secondary: Route B — write out the weighted large sieve of Remark 7.2 and settle whether 0.811 or ≈0.83–0.85 is the right number.
