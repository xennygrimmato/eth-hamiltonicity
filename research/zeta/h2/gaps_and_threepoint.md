# (A) Distinct small gaps and (B) three-point data: what the literature has  [h2, 10 Nov 2026]

Tags: **V** read in the primary source today (PDF text); **S** from a secondary source named; **M** from memory, not
re-read; **U** unrefereed claim. Compared against: lead's announcements 6–7, x2/notebook.md Ideas 2–3, x1/notebook.md
Idea 8, h1/ceiling_class.md. I did not write into any other folder.

## 0. Headlines
1. **Distinct small gaps: nothing usable exists, even under RH.** The definitive reference is Bui–Goldston–Milinovich–
   Montgomery, *Small gaps and small spacings between zeta zeros*, Acta Arith. 210 (2023) 133–153 (arXiv:2208.02359) [V].
   They separate spacings (multiplicity counted) from gaps (distinct ordinates) and state that all three classical
   methods "fail to exclude the possibility that the small spacings that are detected are composed entirely from zero
   spacings between multiple zeros". Under RH they get: infinitely many distinct gaps ≤ 0.991 (Thm 2), and a positive
   proportion of distinct gaps only for λ ≤ **1.0522 > 1** (Cor. 2). Unconditionally there is no theorem about gaps
   between distinct ordinates below the mean spacing at all. x2's input ("≥ 5% of zeros have a distinct partner within
   0.5") is far beyond the literature, RH or not.
2. **The October 2026 "unconditional" small-gap theorem (Durkan–Pearce-Crump Thm 1) is not about distinct zeros**: its
   first step is "if infinitely many off-line pairs exist, the paired ordinates give µ = 0 since we count
   multiplicities" [V]. Bondarenko–Heap is RH-conditional. Lamzouri's 13/20 goes in the opposite direction (zeros with
   NO close neighbour).
3. **Three-point data.** (i) Nobody has *claimed* a valid unconditional three-point certificate above 0.68185.
   (ii) Two unrefereed works claim *exclusions*, both for restricted classes: Tyagi (finite flat-window model, one
   half-bandwidth cubic trace: no gain over the two-moment corner 2/3) and **Fabbian, Zenodo 23198632 (7 Oct 2026)**:
   clipped-Gram certificates augmented by level-3/4 Rudnick–Sarnak statistics with nonzero frequencies gain nothing
   (Thm 8.6) and are capped at 0.6764851 (Thm 8.8); in the single-window class the gain is ≤ c(0)+2c(1/2)−2 (Prop 9.9;
   ≤ 7.12·10⁻⁴ for the MT window per the abstract). The mechanism — **lattices of spacing in (1,2], including double
   points at spacing 2, are invisible to every strict-range k-point statistic with nonzero frequencies** — is a
   concrete threat that h1's finite-N LP (+0.02) must be tested against (§B4). (iii) Yang–Yang's 0.7962 is not a
   three-point claim; it needs the 4th–6th traces at bandwidth 1, outside the Rudnick–Sarnak range.
4. **Urgent side-finding for the D_CGdL target**: Fabbian's companion preprint (Zenodo 22778066, 15 Sep 2026) already
   proves the CGdL-type configuration inequality with value 0.6792041 for all configurations of depth ≤ 33/200, and
   the barriers paper proves that two-point LP certificates fail at every common depth in [0.055, 0.6] (§C).

---------------------------------------------------------------------------------------------------------------
## A. Small gaps

Notation (BGMM): γ ≤ γ⁺ consecutive ordinates with multiplicity ("spacing", may be 0); γ_d < γ_d⁺ consecutive distinct
ordinates ("gap"). µ, µ_d = liminf of normalised spacing / gap; µ_D, µ_{Dd} = inf of λ such that a positive proportion
of spacings / gaps are ≤ λ. Trivially µ ≤ µ_d ≤ µ_{Dd}, µ ≤ µ_D ≤ µ_{Dd}.

### A(i) Proportion of zeros with another distinct zero within λ mean spacings
| statement | hypothesis | distinct? | source | tag |
|---|---|---|---|---|
| µ_D ≤ 1 − δ, δ tiny (positive proportion of spacings below the mean) | none | **no** (multiplicity counted) | Selberg 1946 (announced); Fujii 1975; Heath-Brown in Titchmarsh §9.26 | S (STT-B, BGMM) |
| explicit version: if µ > 1 − 2c₀c₁/(1 − 2c₁) then D⁻(µ) > c₂ > 0, with c₀ = π e^{4.3}/exp(exp(30.76)) | none | **no** | Simonič–Trudgian–Turnage-Butterbaugh, Trans. AMS 375 (2022) 3239–3265, Thm 1 (arXiv:2010.10675); "the first unconditional results on gaps (large and small) which hold for a positive proportion of zeroes" | V |
| µ ≤ 0.5172; 0.5155; 0.5154; 0.515396; 0.50895 | RH | no | Conrey–Ghosh–Gonek 1984; Bui–Milinovich–Ng 2010; Feng–Wu 2012; Preobrazhenskiĭ 2016; Inoue arXiv:2604.05733 | S (Bondarenko–Heap intro) |
| the Montgomery–Odlyzko method cannot reach 0.5042 (0.508 for length ≤ T) | — | — | Goldston–Trudgian–Turnage-Butterbaugh, JMAA 527 (2023); Inoue–Kobayashi–Toma | V abstract / S |
| µ ≤ 1/2 | RH | no | Bondarenko–Heap arXiv:2610.26038, Thm 1 | V |
| µ ≤ 1/2 for every fixed primitive Dirichlet L | "none" — but reduces to the case of all zeros on the line, because off-line pairs give µ = 0 trivially | **no** | Durkan–Pearce-Crump arXiv:2610.28527, Thm 1 | V |
| positive proportion of spacings < 1/2 + ε for ζ | RH | no | Durkan–Pearce-Crump Thm 2 (c_ε may → 0) | V |
| µ_D ≤ 0.77; 0.6876; 0.6653 (BGMM) / 0.6553 (STT-B) — the two citations of Wu disagree | RH | no | Conrey–Ghosh–Goldston–Gonek–Heath-Brown, QJM 36 (1985); Soundararajan, QJM 47 (1996); Wu 2014 | S |
| µ ≤ 0.6039 by pair correlation; µ_D ≤ 0.6039 | RH | no | Chirre–Gonçalves–de Laat 2020; BGMM Thm 1 | V (BGMM) |
| **µ_d ≤ 0.991**; ≫ T exp(−C log T/log log T) such gaps in [T,2T] (C > log 4); the two zeros are a simple zero and a zero of odd multiplicity | RH | **yes** | BGMM Thm 2, Cor. 1 | V |
| **µ_{Dd} ≤ 1.0522** (positive proportion of distinct gaps, but above the mean); µ_{Dd} < 1 would need the mean-square multiplicity bound n* ≤ 1.2826, known n* ≤ 1.3208 (CGdL, RH) | RH | **yes** | BGMM Cor. 2 and Remark after it | V |
| ≥ 0.50875 of zeros have BOTH neighbours farther than 1/6; ≥ 0.6552 are c-isolated for some c > 0 | none | n/a (upper bound on close pairs: at most 49.1% of zeros have a neighbour within 1/6, multiple zeros included) | Lamzouri arXiv:2610.26841, Thm 1.1 (1.5), (1.4) | V |
| k = 3, 4, 5 consecutive gaps > c_k (0.1458, 0.1299, 0.1182): proportions 0.345, 0.1812, 0.0175 | none | lower bounds on gaps | Lamzouri Thm 1.3; Angón–Ross–Tang–Zhao arXiv:2610.22927 (c = 1/4, k = 2,3,4) | V |
| GUE prediction for comparison: P(gap < 0.5) ≈ 0.112 (Wigner surmise) | — | — | — | computed |

Consequences for x2's line.
- Needed: an unconditional lower bound δ(λ) > 0 for the proportion of *distinct* pairs within λ < 1. Known: none
  (not even one such pair unconditionally; under RH one gets infinitely many at 0.991 and no positive proportion
  below 1). BGMM say they "suspect that all three methods cannot be modified to prove µ_d < 1".
- The obstruction BGMM identify is exactly x2's: a small-spacing count cannot tell a close distinct pair from a double
  zero; the only device is to subtract the mass of multiple zeros, i.e. a bound on Σ m² (their n*). Unconditionally,
  Fabbian Thm 9.2(iii) [U] says no such Montgomery-type bound on Σ m²/N is certifiable in the single-window inertia
  class (sup = ∞ when the energy constant R > 1), because off-line clusters cancel energy.
- So the circle is: distinct close pairs ⇐ bound on multiplicities ⇐ (what we are trying to prove). A genuinely
  different input is needed: sign changes of Z.

### A(ii) Sign changes of Hardy's Z in intervals of length ≍ 1/log T (zeros of odd order on the line)
All from memory or secondary sources unless tagged; I found no post-2000 paper on *two* sign changes in a short window.
- Selberg 1942: N₀(T+U) − N₀(T) ≫ U log T for U ≥ T^{1/2+ε}; the proof shows that a positive proportion of the
  intervals (t, t + A/log T), **A a large constant**, contain a sign change of Z. Explicit proportion of critical zeros
  from this method: Zhuravlev 1974; **6.78%** (Pearce-Crump arXiv:2609.15329, V abstract). [M/V]
- Karatsuba 1984–: same with U ≥ T^{27/82+ε}, and for almost all t with U = T^ε. [M]
- Levinson / Conrey / Bui–Conrey–Young / PRZZ count zeros of odd order globally (by argument change of a mollified
  combination); they give no localisation at scale 1/log T. [M]
- Large gaps between zeros **on the line**, unconditional: Hall (Mathematika 52 (2005)): > 2.63 (S: D–PC refs);
  Bui–Milinovich, Q. J. Math. 69 (2018): > 3.18 "between consecutive zeros on the critical line" (V abstract;
  Wirtinger-inequality method with mixed moments of Z, Z'). The Wirtinger method gives large gaps only.
- **Small gaps between consecutive sign changes of Z, unconditional: I found no result.** A positive proportion of
  intervals of length (1/2)·2π/log T containing two sign changes would be new. The natural tool (Selberg's method with
  a short window) detects one sign change per window with a window of many mean spacings; pushing the window below one
  mean spacing with a mollifier of length < T^{1/2} is not known to work. [C]
- A possible lever [C]: Lamzouri's rigidity (2610.26841 §1: "zeros on the critical line that are extremely close
  behave roughly like double zeros" in the Hilbert-space inequality). His theorem bounds how many zeros can be
  *non-isolated*; x2 needs the reverse inequality, which the two-point data cannot give (the ceiling crystals have no
  close distinct pairs and satisfy all two-point data).

### A(iii) The three October 2026 preprints — exact statements
- **Bondarenko–Heap, arXiv:2610.26038** (19 Oct 2026), Thm 1: "Assume the Riemann hypothesis. Then µ ≤ 1/2", µ =
  liminf (γ_{n+1} − γ_n) log γ_n / 2π, ordinates **counted with multiplicity**. Method: resonance applied to a quotient
  of shifted zeta functions; N_c(v) counts ordinates with multiplicity. Not unconditional; not distinct. [V]
- **Durkan–Pearce-Crump, arXiv:2610.28527** (20 Oct, v2 23 Oct): Thm 1 "Unconditionally, µ ≤ 1/2 for every fixed
  primitive Dirichlet character χ" (Q = 1 is ζ); ordinates counted with multiplicity; the unconditional part is the
  remark that off-line zeros come in pairs with equal ordinate. Thm 2 (RH for ζ): #{n: T ≤ γ_n ≤ γ_{n+1} ≤ 2T,
  normalised spacing < 1/2 + ε} ≥ c_ε T log T. Thm 3 (RH for L(s,χ)): λ > 3.63846723. Not distinct. [V]
- **Lamzouri, arXiv:2610.26841** (19 Oct, v2 26 Oct): Thm 1.1: B₀(T,c) = #{ρ_n: 0 < γ_n ≤ T, min(γ_{n+1} − γ_n,
  γ_n − γ_{n−1}) > 2πc/log T}; ∃ c > 0 with liminf B₀/N ≥ 0.6552; liminf B₀(T,1/6)/N ≥ 0.50875. Unconditional;
  isolated zeros are automatically simple and on the line. Uses Conrey's 1989 mollified second moment + Littlewood's
  lemma for the off-line term (Remark 1.2). Thm 1.3 as in the table. Thm 1.5: ≥ 31% of zeros of b₁L(s,χ₁)+b₂L(s,χ₂)
  on the line with odd multiplicity. [V]

---------------------------------------------------------------------------------------------------------------
## B. Three-point data

### B1. What is unconditional (Rudnick–Sarnak; Hejhal)
- Rudnick–Sarnak, *Zeros of principal L-functions and random matrix theory*, Duke Math. J. 81 (1996) 269–322, Thm 1.1
  (ζ) / 1.2 (cuspidal π on GL_m): the smoothed n-level correlation sum Σ over n-tuples of **distinct indices** of
  h(γ_{j1}/T)…h(γ_{jn}/T) f(Lγ_{j1}/2π,…,Lγ_{jn}/2π) is asymptotic to the GUE n-level density integral for f
  translation-invariant with f̂(ξ) = Φ(ξ)δ(ξ₁+…+ξ_n), Φ supported in **Σ|ξ_j| < 2/m** (m = 1 for ζ: Σ|ξ_j| < 2).
  Unconditional for m ≤ 3 (general m under their Hypothesis H); RH is not needed for these smoothed sums when the
  γ are allowed to be complex and f is the entire extension (they say so explicitly; this is also the content of
  B. Rodgers's MathOverflow answer 91359). [M for theorem numbering and wording; S: Fabbian Remark 8.2 cites "[RS,
  Thm 1.1]" for the strict range, Tyagi and A–F cite RS96 for the same range; h1 §3(i) agrees]
  "Distinct indices" means a zero of multiplicity m contributes m(m−1)(m−2) ordered triples at separation 0 — so the
  three-point function does see Σ m³, as x2 notes.
- Hejhal, IMRN 1994: triple correlation under RH, support |ξ₁|+|ξ₂|+|ξ₁+ξ₂| < 2 (the same hexagon). [M]
- Mock-Gaussian moments of linear statistics, supp f̂ ⊂ (−2/k, 2/k) for the k-th moment: unconditional (Fabbian cites
  a note with "Thms 1.1 and 2.6"; presumably Hughes–Rudnick 2002/2003). [S, unverified]
- For n = 3 the range Σ|ξ_j| < 2 with ξ₁+ξ₂+ξ₃ = 0 is max|ξ_j| < 1: **the full bandwidth-one bispectrum is
  unconditional**. This is what h1's rows "a + b ≤ N − 1" and x2's "tri" rows encode, and what x1 Idea 8a derives
  directly (tr P³ diagonal for X < T^{1−ε}). It **contradicts the letter of A–F §7.2(e)** ("tr G̃^k … available exactly
  in the Rudnick–Sarnak range X^k ≤ T^{2−ε}; at X ≍ T this allows only k = 1", i.e. k = 3 only for λ < 2/3) — the
  correct RS condition for a 3-cycle is 2·max|ξ| < 2, not 3λ < 2. A–F's rule is right for k = 4 (the pattern
  (+,−,+,−) reaches Σ|ξ| = 4λ, so λ < 1/2), which is x1's 8c. Tyagi v1 §1.5 makes the same correction in words
  ("the third trace at bandwidth λ′ carries total Fourier support (k−1)λ′, not 3λ′") but still works at λ′ = 1/2.
  So: A–F's (e) understates the available cubic data; its *conclusion* for the single matrix (odd moments do not help)
  is nevertheless right, see B2.

### B2. Why a single cubic trace gives nothing (agreement of four sources)
- x1 Idea 8b [R]: tr G(G−1)(G−2) = tr(P³ − P) = 0 and the rank–trace extremal spectrum is {0,1,2}: m₃ is exactly
  neutral.
- A–F §7.2(d): the sharp k-moment bound is 1 − Λ_m(0) (Christoffel function); odd top moments do not lower it
  (teal-sea's digest of the 35-page version: "odd moments do not lower Λ₁(0)") [S].
- Tyagi, hexagon:2610.00252 (v1 26 Aug, v2 18 Oct 2026) [V both]: finite circle model N = 64, flat windows, bands
  B₁ = {−32..32}, B′ = {−16..16}; constraints: E tr H_{B₁}² within ±5% of a budget, E tr H_{B′}² within ±5%,
  |E tr H_{B′}³ − b₃| ≤ 0.05·N, an eigenvalue-count ladder. v2 Thm 3.2: over atom-only (on-line) configurations the
  augmented optimum equals the baseline 2 − U/N (the two-moment *rank–trace* corner, 2/3 as ε → 0), attained by an
  explicit grid law. v1's broader claims (pairs included, "940 records") are **withdrawn** in v2. Identity behind it:
  on isolated blocks the signed cubic row is the affine function 3F − 2 of the Frobenius row; on the ψ₁-zero grid the
  bandwidth-one Frobenius row is the multiplicity count while the half-band kernel is position-sensitive, "so the
  cubic budget is met by arrangement at zero cost". Scope note in v1 §: "the cited 0.6818287 ceiling belongs to the
  window-optimized certificate class, which the flat/flat row system used here does not consume".
  ⇒ Tyagi tests ONE scalar cubic row at half bandwidth with 5% tolerances against the 2/3 corner. It says nothing
  about the full bispectrum on the hexagon, nor about 0.68185. **No conflict with h1 §4**, and it confirms h1's
  warning (1) (single-matrix cubic traces are useless).
- h1 §5 warning (1) [R]: rank ≤ λN.

### B3. Yang–Yang (Zenodo 21975237, 17 Aug 2026) and why it conflicts
Claim [U]: N₀ˢ/N ≥ 0.7962, N_d/N ≥ 0.8981 for ζ and each primitive Dirichlet L, from the Gabor-compressed Weil matrix
with trace moments 3–6: "the 4th moment is evaluated exactly as m₄ = 13/4; m₅ = 101/18, m₆ = 12809/1260" via sine-kernel
Ursell constants, plus a Chebyshev–Markov dual certificate. Conflict:
- m₄ = 13/4 at bandwidth 1 is exactly A–F's hypothesis HL*(4) (their §7.2(f): 13/18 follows from it): the pattern
  (+,−,+,−) in tr P⁴ has Σ|ξ_j| up to 4λ and needs the variance of Λ⋆Λ in short intervals (x1 8c computes: diagonal
  value 49/15, sine value 13/4, the −1/60 difference is the non-diagonal Hardy–Littlewood term).
- With only the unconditional data the Chebyshev–Markov bound with m₁..m₃ gives 2/3 (x1 8d), and the two-point
  ceiling 0.68185 < 0.7962 applies to anything two-point.
- The authors themselves grade it "certified-candidate level, not an established theorem"; a second record claiming
  "almost all zeros" is under embargo "because the version contains errors" (S: D'Souza family paper §1.4, accessed
  28 Sep). Knausgård does not count it. Verdict: not a three-point certificate, and its 4th-moment "Lemma D" is the
  unproved step. [C: I did not read the PDF]

### B4. Has anyone claimed or excluded a three-point certificate above 0.68185?
**Claimed (valid, unconditional): no one.** Nearest items:
- elCanosail/riemann-conjecture README: "Compute tr(G³) unconditionally → ~0.676 (needs triple correlations)" — a
  guess below the ceiling, and wrong on both counts (it is available; alone it gives nothing). [U]
- Devine (Zenodo 22066689): "conditional advances beyond 67.92%" — conditional. [U, title only]
- A–F §7.3: under RH, cubic weight + BHB gives distinct ≥ 0.85082 (uses tr G̃³ under RH). Conditional.
**Excluded: only for restricted classes.**
- Tyagi (above): one half-bandwidth cubic row, finite model.
- **Fabbian, "Structural barriers for band-limited and low-order certificate methods…", Zenodo 10.5281/zenodo.23198631
  (record 23198632), 7 Oct 2026** [V §8–9, U]:
  - Def 8.1: clipped-Gram certificates (Gebendorfer's class C₂₅, valid for all finite sets of distinct real points)
    plus Σ η_i (T_{Φ_i}(Z) − t^G_{Φ_i} N) with Φ_i of level 3 or 4, strict RS range, all frequencies nonzero.
  - Thm 8.6: if the level-4 statistics are "genuine", the symmetrised statistics vanish identically and
    κ < 0.6740331 (= Gebendorfer's ceiling 0.674034 for the class, Thm 7.1): the statistics "contribute nothing".
  - Thm 8.8: every certificate of Def 8.1 has κ < 0.6764851. Proof: a mixture of four lattices (spacings 1, 1.001,
    1.027, 2) of mean gap 1/r is blind: "a lattice of spacing d ∈ (1,2] has, among the frequencies of modulus < 1,
    only ±1/d; a zero-sum triple of ±1/d is impossible, and the only zero-sum quadruples have Σ|ξ_i| = 4/d ≥ 2".
  - Prop 9.9 (single-window inertia class, i.e. s₁ ≥ (2+Δ)N − T₂ + Σ y_i Φ_{F_i} with a fixed window): Δ ≤
    c(0) + 2c(1/2) − 2, from a segment of real double points at spacing 2 − ε (blind to all levels ≥ 3 in the closed
    range). Abstract: ≤ 7.12·10⁻⁴ for the MT window; "the corresponding cap on the proportion requires one additional
    hypothesis".
  - Thm 9.2: optimal constants of the single-window class for several target sets (e.g. simple-or-on-line ≤ 0.88762,
    matching Lamzouri from above; no bound on Σ m²).
  - He cites Lagarias–Rodgers (Q. J. Math. 71 (2020), *Higher correlations and the alternative hypothesis*) for a
    genuine point process on a half-integer lattice matching all RS-range correlations, and Tyagi for level 3.
**Relation to h1/x2's +0.02.** No logical conflict: h1's LP dualises *all* certificates linear in the two-point rows
(any multiplier) and in the full set of bispectrum rows, a much larger class than "one window + clipping + statistics";
and its laws must satisfy the two-point rows exactly (E|S(l)|² = l for all l ≤ N−1), which a mixture of pure lattices
of spacing in (1,2] cannot (their two-point mass sits only at frequencies 1/d ∈ [1/2,1), nothing on (0,1/2)). But
Fabbian's observation is the right adversary for the large-N limit:
  *any component of the law that is locally a lattice of spacing d ∈ (1,2] — simple points, or double points at
  spacing 2 — carries no three-point signal at nonzero frequencies.*
At N = 8, 12 the model cannot host long lattice segments with defects far apart, so the +0.02 could be a small-N
effect; x2's "crystal of spacing ≈ 0.9 with double+vacancy defects" has frequencies 1/0.9 > 1 from the crystal (blind
at two- and three-point level) and all its in-band signal from the defects, whose bispectrum per unit length is
O(defect density) with the self-term Σm³ — that is the part RS data constrain. **Test for h1/x2 [C]:** at N ≥ 24 add
columns "blind lattice segments (d ∈ (1,2], marks 1 or 2) + dilute defects" and see whether the 3-point gain survives;
equivalently compute the bispectrum of the N = 256 two-point ceiling law — if it can be made to vanish on the hexagon
by rearranging defects (Tyagi's "met by arrangement at zero cost"), the three-point ceiling equals 0.68185.
Also relevant: h1's rows are for a ≥ 1, b ≥ 1 (nonzero frequencies), exactly Fabbian's class (nz); statistics with a
zero frequency (the "coordinate planes", i.e. density×pair terms) are excluded by both and are where a lattice is NOT
blind — they are two-point data in disguise.

### B5. Summary table
| source | data used | class | conclusion | status |
|---|---|---|---|---|
| A–F §7.2(e),(f) | tr G̃^k | single matrix, Christoffel bound | k = 3 adds nothing; k = 4 needs HL*(4) → 13/18 | V; (e)'s range for k = 3 is too conservative |
| x1 Idea 8 | tr P³ (unconditional, λ < 1), tr P⁴ one-sided | single matrix | m₃ exactly neutral; need tr P⁴ ≤ 0.305N (truth 0.25, diagonal 0.2667) | team [R]/[N] |
| Tyagi hexagon:2610.00252 v2 | one cubic trace at λ′ = 1/2, ±5% budgets | finite model N = 64, flat windows, atoms only | no gain over 2/3 | V, U; v1 claims withdrawn |
| Fabbian Zenodo 23198632 | all strict-range level-3/4 statistics with nonzero frequencies | clipped-Gram (distinct real points); single-window inertia | no gain / cap 0.6764851 / gain ≤ 7·10⁻⁴ | V §8–9, U |
| h1 ceiling_class §4, x2 Idea 3 | full bispectrum rows (and 4-pt rows a+b ≤ N−1) | all linear certificates, periodic model N ≤ 12 | ceiling 0.686 → 0.709 (N = 8), ≈ 0.705 (N = 12) | team [N]; large-N limit open |
| Yang–Yang Zenodo 21975237 | m₃..m₆ at bandwidth 1 | single matrix | 0.7962 | U; needs HL*(4); invalid as unconditional |
| Lagarias–Rodgers 2020 | all RS-range n-level data | point processes | cannot exclude the Alternative Hypothesis | M/S |

---------------------------------------------------------------------------------------------------------------
## C. Side-finding: prior art for the D_CGdL target (announcement 5)
- **Fabbian, *A bounded-depth positivity inequality for zeta-zero configurations and simple critical zeros under a
  narrow-box hypothesis*, Zenodo 10.5281/zenodo.22778066, v1.0, 15 Sep 2026** [V abstract, U]: explicit even
  piecewise-linear kernel g_A on [−1,1]; proves (computer-assisted: exact identities, combinatorial certificate with a
  Lean component, ball arithmetic) ∫ g_A |E_Z|² ≥ 2|Z| − κ(Z) for every finite conjugation-invariant configuration of
  depth ≤ 33/200. Consequence: if all zeros in (T,2T] satisfy |β − 1/2| log T ≤ 33π/100 then N₀ˢ/N ≥ 0.679204126….
  This is "CGdL's certificate stays valid for shallow off-line pairs" — h3's single-pair reduction is a special case.
- **Barriers paper (same author, 7 Oct)** [V theorem statements]: Thm 3.4: the homogeneous two-point (LP) relaxation is
  infeasible at every common depth y ∈ [0.055, 0.6] (counter-configurations: unit masses at 0,2,…,2N and pairs of small
  mass ε at the odd sites; integer version Remark 3.5: triple points at odd integers and simple pairs 2j ± i y*,
  y* = π⁻¹ arccosh(3/2) = 0.3063); Thm 3.9: continuous certificates fail for every y ≥ 0.56; Thm 4.5, 4.13:
  fixed-charge and pair-by-pair local-kernel certificates fail (the latter at every y ≥ 0.032); Prop 6.1: no bound can
  remove points of depth > Y at a cost depending only on them; Prop 10.3: weighted Gram certificates from the
  CGG/BHB mollified moments are capped (cf. h4 Prop 1). Prop 11.1 (positive): for y ∈ {0.13, 0.2, 0.25, 0.3, 0.4, 0.5}
  the inequality Φ_g(Z) ≥ 0 does hold on integer-site configurations with one object per site.
- Reading: the inequality itself is not shown false at depth > 33/200; what is shown is that the *proof methods*
  h3/h5 are likely to try (two-point LP duals, local kernels, per-pair charges) cannot prove it, and why (integrality
  gap). h3's counterexample to the general Conjecture D ("two adjacent off-line pairs") should be compared with his
  Thm 3.4 configurations. An unconditional 0.6792 therefore needs either a non-LP argument for deep pairs or an
  arithmetic input bounding the mass of zeros at depth > 33/200 in units of 1/log T — e.g. a zero-density estimate
  near the line of the Selberg type N(σ,T) ≪ T^{1−(σ−1/2)/4} log T, which controls depth ≫ 1 but not depth ≈ 0.2;
  Lamzouri uses Conrey's mollified density bound for exactly this purpose in 2610.26841.
- Also found: rStation post 72 (8 Nov 2026) "Simple critical zeros at bandwidth one: an honest-adversary LP (0.6764 /
  0.6795 / 0.6810)" [S, U]: LP values with MT; MT + Fejér; MT + Fejér + bump windows, stated as hypothesis.
