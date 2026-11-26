# Referee report: Lemma 5.3 (zero-loss lemma), `attain-notes.md` §5.2

Scope: the statement of Lemma 5.3, its use in Theorem W (§5.3), Steps 1–3 of the proof, and the junctions between
the ranges proved by hand and the ranges computed. Input (K2) (Bessenrodt–Ono, arXiv:1403.3352) taken as given, as
instructed. Independent code (directory `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/ref53/`,
not durable): `ref53.py` (all comparisons exact integer or rigorous interval
arithmetic, `mpmath.iv`, 90 digits, outward rounding; an undecidable comparison would be reported, none occurred),
`tight.py` (float diagnostic of slack), `kappa.py` (remark 4). Output: `ref53.out`.

**Overall verdict: correct.** No real gap. Three presentational points (items 1–3 below) should be fixed in the text;
none changes the statement Theorem W needs or its truth. The lemma is far from tight on the computed range (the arc can
be enlarged by a factor 1.66 in radius for every pair with m ≤ 30 and still be covered).

Verdicts, weakest first.

## 1. Interface with Theorem W — correct, with one missing sentence (presentational gap, repaired)

What Theorem W consumes: at a crossing of (a,c;p), (b,d;q), Lemma S gives (r_c, r_b) with r_c² + r_b² ≤ 2(p²+q²)
(a point of the **disc**, not necessarily of the arc) and r_c, r_b ≤ p+q; the proof needs one N with
b_c(N) ≥ r_c and b_b(N) ≥ r_b. Lemma 5.3 is stated for points **on the arc** only. The passage disc ∩ box → arc ∩ box is
the domination argument that appears only inside Step 3 ("monotone in (p,q)"): a point (r,r′) with r²+r′² ≤ R²,
r, r′ ≤ p+q is dominated coordinatewise by the arc point (x, √(R²−x²)) for any x ∈ [max(r,|p−q|), min(√(R²−r′²), p+q)],
which is non-empty (r ≤ p+q; |p−q| ≤ p+q; r² ≤ R²−r′²; (p−q)² ≤ R²−r′² ⇔ r′ ≤ p+q). I re-derived this; it is correct.
**Repair:** state it once in Lemma 5.3 ("equivalently, for every (r,r′) in the disc with r, r′ ≤ p+q") or in the proof
of Theorem W. The same remark is what makes the (M1) definition ("boxes cover the arc") sufficient for the disc point of
Lemma S in general.

Other normalisations, all checked against the paper (`fm/paper.txt`, App. B):
- Classes: B.2 takes Σ_i = all symbols of size n_i and energy e_i. Energy Σ(2i+1)+Σ(2j+1) is even, so e_i = 2m_i, and
  Σ_i ⊆ {symbols of energy 2m_i} ↔ partitions of m_i, so |Σ_i| ≤ p(m_i). Correct.
- P(E) = number of symbols of energy ≤ E = Σ_{m ≤ E/2} p(m). Correct.
- Θ = 2(e₁+e₂) = 4(m₁+m₂): matches B.2.
- Factor (E+1): B.2(b) bounds the number of products across {a,d}|{b,c} by (N+1)P(N); B.2(c) across {a,b}|{c,d} by
  (N′+1)P(N′), N′ = Θ−N. In (M1), "cut c" joins a,b at o (cut ab|cd), "cut b" joins a,d at w (cut ad|bc). Hence
  b_c(N) = f(Θ−N), b_b(N) = f(N), r ↔ r_c, r′ ↔ r_b, exactly as Lemma 5.3 and Lemma S are written (Lemma S's N₁ uses
  p|ao| + q|bo| + p|co′| + q|do′|). Consistent. Including the factor (E+1) is legitimate (it is in the certificate) and is
  what makes Step 1 hold with E₀ = 44; without it (Z′) would need a different E₀ but nothing else is sensitive to it.
- Bits: p, q, f all log₂; the arc radius 2(p²+q²) is that of Lemma S in the same units. Consistent.
- Wire bits vs class sizes: a wire of β bits crossed via B.2 is ⟨2^β⟩ = a restriction of ⟨|Σ|⟩ with |Σ| ≥ 2^β. Lemma 5.3
  is then applied with p = log₂|Σ| ≥ β; Lemma S's point lies in disc(β,γ) ∩ [0,β+γ]² ⊆ disc(p,q) ∩ [0,p+q]², so the
  domination of item 1 covers it. The notes do not say this; one clause would do ("p, q may be taken ≥ the wire bits").
- The constant κ: Lemma 5.3 uses κ = π/√3 (from (K1)/(K2) directly). Lemma 5.2 uses the paper's κ = sup_E ln P(E)/√E of
  Lemma B.1. These need not be the same number; Lemma 5.3 never uses the paper's κ, so the proof is unaffected, but the
  shared symbol should be disambiguated (remark: numerically ln P(E)/√E ≤ 1.766 < π/√3 for E ≤ 20000, `kappa.py`).

## 2. Hypothesis m_i ≥ 1 — harmless restriction (presentational)

B.2 allows e_i = 0 (Σ_i = {empty symbol}, |Σ_i| = 1, p = 0). Lemma 5.3 excludes it. It holds there trivially: if p = 0
the arc ∩ box is the single point (q,q) and N = Θ/2 = 2m₂ gives f(2m₂) ≥ log₂ p(m₂) ≥ q; if both are 0, N = 0. Step 2
also covers m₁ = 0 verbatim (p = a₁ = 0). My exhaustive run includes m₁ = 0 (all 120 pairs (0, m₂), m₂ ≤ 120): no
failure. **Repair:** replace m_i ≥ 1 by m_i ≥ 0.

## 3. Step 3 (case max(m₁,m₂) ≤ 30) — correct

- Monotonicity reduction (to p = log₂ p(m₁), q = log₂ p(m₂)): correct, argument as in item 1 (Θ is fixed by the m_i, so
  shrinking the classes only shrinks the disc and the box). The interval as printed names the new *first* coordinate x;
  the other coordinate is √(R²−x²). Terse but right.
- The finite criterion in the notes (for each N whose window (f(N−1), f(N)] meets [|p−q|, p+q]:
  f(Θ−N)² ≥ R² − max(f(N−1), |p−q|)², with "f(Θ−N) ≥ p+q" as a sufficient shortcut) is equivalent to the property: N(r′)
  = least N with f(N) ≥ r′ is optimal since f is non-decreasing, and the worst r′ in a window is its infimum. Checked.
- `zeroloss.py` (D) implements it correctly (N = 0 only matters when p = q; loop stops at the first N with f(N) ≥ p+q or
  N = Θ; f(Θ) ≥ p+q is tested). Its comparisons are 60-digit floats without an error bound.
- **My recomputation**, different formulation: N covers the closed r′-interval I_N = [√(max(0,R²−f(Θ−N)²)), f(N)]; both
  endpoints are non-decreasing in N, so one sweep decides whether ∪ I_N ⊇ [|p−q|, p+q]. Comparisons with p+q and |p−q|
  are exact integer comparisons ((N+1)P(N) vs p(m₁)p(m₂), resp. vs p(m_max)/p(m_min)); the circle comparisons
  f(Θ−N)² + f(N′)² ≥ R² are rigorous interval comparisons (90 digits; error bound: outward-rounded intervals, every
  sign decided, 0 undecided). Result: **all 7380 pairs 0 ≤ m₁ ≤ m₂ ≤ 120 (m₂ ≥ 1) covered, 0 failures**; smallest margin of
  an interval-decided comparison 2544 squared bits (at (84,91)).
- Extra check of monotonicity on the true classes: for every m₁ ≤ m₂ ≤ 30 and every pair of Durfee-square class sizes
  (|Σ| = #partitions of m with Durfee square n; sums verified = p(m)), 5186 cases: 0 failures.
- Slack (float diagnostic, `tight.py`): for every pair with m ≤ 30 the arc of radius s·R with box s(p+q) is still
  covered for s ≤ 1.665 (worst pair (0,30)). The case is nowhere near tight.

## 4. Step 1 ((Z′): (E+1)P(E) ≥ exp(κ√(E+½)) for E ≥ 44) — correct

Finite part, my exact-integer/interval code: (Z′) fails for exactly 39 values in 0 ≤ E ≤ 43, last failure E = 43, and
holds for 44 ≤ E < 20000 (so the computed range 44–799 and the analytic range ≥ 800 overlap; 800–19999 is an extra
cross-check). Smallest ratio on 44 ≤ E < 800: 1.00753 (E = 45), matching the notes.

Analytic part (E ≥ 800, E ∈ {2M, 2M+1}, M ≥ 400, J = ⌊√M⌋), redone by hand:
- P(E) = Σ_{m≤M} p(m) ≥ Σ_{j=0}^{J} p(M−j), and for n ∈ [M−J, M] (K2) gives p(n) > (4√3·M)^{−1}(1 − (M−J)^{−1/2})e^{μ(M−J)}
  (each factor monotone in the right direction; √3/12 = 1/(4√3)). With E+1 ≥ 2M+1 > 2M, J+1 > √M, M−J ≥ M−√M:
  (E+1)P(E)e^{−μ(M−J)} ≥ c₁√M, c₁ = (1 − (M−√M)^{−1/2})/(2√3); c₁(400) = 0.2738664 (interval). ✓
- κ√(E+½) ≤ κ√(2M+3/2) = π√(2M/3+½) =: πA; μ(M−J) = π√(2(M−J)/3 − 1/36) =: πB; A² − B² = 2J/3 + 19/36 ✓. Using
  J ≤ √M in the numerator and A+B ≥ 2B ≥ 2√(2M/3)·(1 − M^{−1/2} − (24M)^{−1})^{1/2} in the denominator gives exactly
  c₂ = (π/√6)(1 + 19/(24√M))(1 − M^{−1/2} − (24M)^{−1})^{−1/2} ✓; c₂(400) = 1.36802982 (interval; the notes' "≤ 1.36803"
  is correct with margin 2·10⁻⁷, irrelevant against 1.70).
- Monotonicity in M: c₁√M increasing, c₂ decreasing (both factors) ✓. ln(c₁(400)·20) = 1.70062 > 1.36803 ✓.
- Also needed and true: M − J ≥ 1 and 1 − (M−J)^{−1/2} > 0 for (K2) to be usable as a positive lower bound.

## 5. Step 2 (case max(m₁,m₂) ≥ 31) — correct

Every inequality re-derived:
- p ≤ a₁ = κ′√(2m₁) from (K1) (p(m) ≤ e^{π√(2m/3)} = e^{κ√(2m)}); (K1) follows from (K2) since (√3/12n)(1+n^{−1/2}) < 1
  and μ(n) < π√(2n/3), and p(0) = 1. κ′²Θ = 2(a₁²+a₂²) ≥ R² ✓.
- S = κ′²Θ − (p+q)² ≥ 2(a₁²−p²) + 2(a₂²−q²) since (p+q)² ≤ 2(p²+q²) ✓.
- For the larger m: log₂ p(m) < μ(m)/ln2 − d₀(m) ≤ a − d₀ with d₀ = log₂(4√3 m/(1+m^{−1/2})) ✓ (rigorously confirmed
  numerically for m ≤ 2000 as a sanity check). Then a² − p² ≥ 2ad₀ − d₀² (needs 0 ≤ p ≤ a − d₀ ✓), so
  2(a²−p²) ≥ 4ad₀ − 2d₀² ≥ 2ad₀ because a ≥ d₀ (as a − d₀ > p ≥ 0). The notes' "S ≥ 2d₀a" is correct (with a factor-2
  slack they do not use). The case is symmetric in the two classes, so "the larger m" may be either.
- 2d₀(m)κ′√(2m) ≥ κ′²(E₀+½) ⇔ 2d₀√(2m) ≥ 44.5κ′: margin −0.92 at m = 30, +1.80 at m = 31 (interval). Both d₀ and √m are
  increasing, so it holds for all m ≥ 31 by hand; the computed check to 2000 is unnecessary.
- Θ = 4(m₁+m₂) ≥ 124 ≥ 2E₀ = 88 ✓, so (Z′) applies at Θ − E₀.
- Existence of N: f(Θ)² ≥ f(Θ−E₀)² ≥ κ′²(Θ−E₀+½) ≥ κ′²Θ − S = (p+q)² (needs only S ≥ κ′²(E₀−½)) ✓, and N ≤ Θ.
- Case N = 0 and case 1 ≤ N ≤ E₀: f(Θ−N) ≥ f(Θ−E₀) ≥ p+q ≥ r (f non-decreasing: (E+1)P(E) is) ✓.
- Case N > E₀: f(N−1) < r′ ≤ p+q; (Z′) at N−1 ≥ E₀ gives κ′²(N−½) < κ′²Θ − S, so Θ−N > S/κ′² − ½ ≥ E₀, so (Z′) applies
  at Θ−N, and f(Θ−N)² ≥ κ′²Θ − κ′²(N−½) > R² − r′² = r² ✓ (r ≥ 0, f ≥ 0).
Uses r′ ≤ p+q, r ≤ p+q and the arc equation exactly as stated.

## 6. Junctions — no gap

- Step 1: computed 44 ≤ E ≤ 799, analytic E ≥ 800 (M ≥ 400): contiguous; (Z′) is used in Step 2 only at E ≥ 44.
- Steps 2/3: "max energy ≥ 62" = max m ≥ 31 (Step 2), "≤ 60" = max m ≤ 30 (Step 3): contiguous; Step 3 computed to
  m ≤ 120 (overlap = cross-check of Step 2); Step 2 itself is fully by hand for all m ≥ 31 (no upper end).
- m = 0: see item 2.
- The quoted (K2) is used for n ≥ 1 only (M − J ≥ 380 in Step 1, m ≥ 31 in Step 2).

## Summary of repairs requested

1. Say once that the arc statement implies the disc ∩ box statement (domination), since Lemma S delivers a disc point.
2. Allow m_i ≥ 0 (trivial case) and note that p, q may be the log-sizes of classes larger than the wire dimension.
3. Distinguish Lemma 5.3's κ = π/√3 from the paper's κ (Lemma B.1) used in Lemma 5.2.
4. Optional: drop "checked for 31 ≤ m < 2000; the left side increases" in favour of the one-line monotonicity, and
   note that the finite checks are now rigorous (interval arithmetic, `ref53.py`).
