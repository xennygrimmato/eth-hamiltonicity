# Prior-art check of h5's family route (h5/T3_families.md: ≥ 0.7523 simple-on-line, ≥ 0.8761 distinct)  [h2, 10 Nov 2026]

Sources read today: D'Souza family paper (github.com/Oliverds321/simple-zeros v1.0, `papers/family/main.pdf`, 46 pp.;
also at aixiv.science/pdf/aixiv.261005.000002v1.0.pdf), its §1.2, §1.4, §2.5, §3, §4.3, §8; Alpöge–Furman Remark 7.2
(draft18 `rem:Davg`); Hua–Yang arXiv:2608.16034 Thm 2.1 / Prop 8.3 and 2609.27808 abstract; Sono JNT 2025 abstract page
(for Conrey–Iwaniec–Soundararajan and Wu); riemannzeta.fun `/challenge`. NOT read: D'Souza's earlier preprint
(his ref [9], the 0.7212 paper; only as described in the family paper), the Lean sources.
Scripts: `h2/killed_check.py`, `h2/af_reconstruct.py` (both import h5's `family_opt.optimise` read-only).

## Verdict
1. **Mechanism: already claimed.** h5 §1 + §3 is the method of D'Souza's preprint [9] as described in the family paper
   §1.2: run the A–F rank–trace certificate on the direct sum of per-χ Gram blocks (their H1 / Prop 2.1), so that only
   an *upper* bound for the family Frobenius norm is needed; functional B(v) = ψ(0) + ∫k(α)ψ(α)dα, ψ = v⋆v, with kernel
   k = |α| in-zone (|α| ≤ 1) and **k = C|α| out-zone, "C the loss of the multiplicative large sieve applied pointwise
   in the dual variable"**; window optimised numerically. For the unweighted family of all primitive χ, q ≤ Q,
   C = π⁴/18 = 5.4116 (= Q²/#harmonics), giving 0.7212 at λ* = 1.2507 (Lean library ZetaQ). h5's (a)–(e) proof
   skeleton (trace from the prime side, μP cross term by linear character sums, Gevrey taper, T a power of log Q)
   matches the list in D'Souza §2.5(i). Hua–Yang have the same summed-certificate step (Prop 8.3) at bandwidth 1.
2. **What is not in the prior art found: the choice of family weight 1/φ(q) with the Montgomery–Vaughan weighted
   large sieve**, which lowers the out-zone constant to K = 3/(2𝔖) = 3.1306 (classical large sieve in the same
   weighted family: 2/𝔖 = 4.174). No occurrence of "Montgomery–Vaughan", "Selberg" or a 1/φ(q)-weighted family in
   D'Souza's family paper (grep); his families are the sharp one w = 1_{[0,1]} and the dyadic one, unweighted. The
   number **0.7523 (or 0.8761) appears nowhere** in arXiv, Hexagon, D'Souza's README/paper, or web search. The
   riemannzeta.fun leaderboard has a single frozen statement (ζ, distinct zeros on the line; dyadic and cumulative
   forms) and **no family track**.
3. **But the number is not a frontier for "Dirichlet family, unconditional":** D'Souza Thm 1.2 claims 0.9059 for the
   unweighted family using two published hybrid zero-density theorems; and the comparison of 0.7523 with his
   hypothesis-free 0.7235 is across *different families* (1/φ(q)-weighted, q ∈ (Q^{1−ε}, Q], versus unweighted
   q ≤ Q). The MV gain is specific to the 1/q-type weighting: in the unweighted family MV gives 1.5·Q², worse than
   the classical Q² (my check, [R] trivial: weights (N + 1.5 qQ)^{-1} ≥ (1.5Q²)^{-1}(1+o(1)) only).
   Honest statement of novelty: "in the CIS/CLLR-normalised family (weights 1/φ(q)), no zero-density input, 0.7523".
4. **Improvements h5 can take from the prior art** (numbers [N], h2/killed_check.py, n = 240 grid, so ±0.002):

   | out-zone kernel | C = π⁴/18 (D'Souza family) | K = 2/𝔖 = 4.174 | K = 3/(2𝔖) = 3.131 (h5) |
   |---|---|---|---|
   | C·|α| (pointwise large sieve) | 0.7226 (D'Souza's design: 0.7212) | 0.7353 | 0.7533 (h5: 0.7523) |
   | C·min(|α|,1) (D'Souza "killed kernel", Lemma 3.1) | 0.7252 (D'Souza: 0.7235, sup 0.723795) | 0.7394 | **0.7602** |

   My QP reproduces D'Souza's two constants to within 0.0015 (the residual is unexplained: his profile class or the
   weight C_Q·L/s near the top edge, §5; treat my 0.760 as ±0.002 and as [C] until the killed-kernel lemma is
   re-proved for the weighted family). The killed kernel is: for s > L the prime polynomial S(ϑ) has a fixed
   proportion of its mass on short arcs around a/r with small r, where no other Farey point of level Q comes near;
   Gallagher's large sieve with a zero set turns C|α| into C·min(|α|,1). It should combine with MV weights but that
   is not checked.
5. **h5's follow-up T3b ("sharp weighted Farey large sieve") is essentially D'Souza §4.3–4.4** (Lemma 4.3 "local
   density of weighted Farey points": outside shells around a/r, r ≤ R₁, the weighted Farey density is asymptotically
   the constant H_w; inside holes it vanishes). That is the lossless large sieve away from major arcs; the major-arc
   rings are then what force the zero-density input (J), (M). So "sharp constant" without density estimates is not
   available by that route — the obstruction is the mass of S(ϑ) on major arcs, i.e. exactly h5 §2's small-conductor
   characters. A–F's remark claims to avoid this with a weight vanishing at q = Q (next section); unproved.

## Reconstruction of Alpöge–Furman Remark 7.2 (0.811 / 0.905)  [N]/[C]
Data in the remark: weights (1 − q/Q)², "weighted large-sieve inequality whose constant is 1.263… times the number
of harmonics (in place of Q²), valid for X ≤ Q^{2−ε}", bandwidth 3/2, Gevrey taper, T a power of log Q.
0.811 and 0.905 are one datum: R = 1.189–1.190 (2 − R, (3 − R)/2).
- Kernel k = |α| (≤ 1), 1.263·|α| (1 < |α| ≤ 3/2): optimal window gives **0.8339 / 0.9170** (h5's 0.834, confirmed);
  flat window 0.7994; **window cos(u/√2) on [−3/4, 3/4] gives 0.8109 / 0.9055** — matches the remark to 3 digits.
  The same value also occurs at cos(2u), and K ≈ 1.6 with the optimal window gives 0.8116, so the match is not
  unique. Most likely reading [C]: A–F used kernel 1.263|α| on the out-zone at λ = 3/2 with a non-optimised
  one-parameter (cosine) window; then their remark *understates* what its own inequality gives (0.834 at 3/2,
  0.849 as λ → 2). Other readings tested and rejected (h2/af_reconstruct.py): large sieve for all α (0.737),
  K·min(α,1) (0.748), cap K beyond 1 (0.846), α + (K − 1) (0.836).
- Where 1.263 could come from [C]: for 1/φ(q)-type weights the ratio (generic Farey density)/(primitive harmonics)
  is (6/π²)/𝔖 = 1.2688 (Σφ(q)/q ~ (6/π²)Q against Σφ*(q)/φ(q) ~ 𝔖Q, 𝔖 = Π(1 − p⁻² − p⁻³) = 0.479145). This is
  close to but not equal to 1.263; with the (1 − q/Q)² weight the true extremal local density is presumably what
  they computed ("the extremal configuration for the sharp cut-off is the single Farey spoke {1/q} near 1/Q, and a
  weight vanishing at q = Q removes it"). **Unresolved**; the claim that the *sup* of the weighted local Farey
  density is only 1.263× the mean contradicts nothing in D'Souza (his density statement is "outside shells"), but
  near a/r with small r the unweighted-in-a density is far above the mean for N ≫ Q (major arcs), so a uniform
  constant 1.263 for all X ≤ Q^{2−ε} needs the weight to tame every spoke, not only r = 1. I could not verify it;
  D'Souza explicitly declines to compare. Treat 0.811 as an unproved claim.

## Other prior art in the same family normalisation (all unconditional, Levinson + asymptotic large sieve)
- Conrey–Iwaniec–Soundararajan (J. reine angew. Math. 681 (2013)): weights Ψ(q/Q)/φ(q), (log Q)⁶ ≤ T ≤ (log Q)^A:
  ≥ 14/25 = 0.56 simple and on the line (0.5865 with the best polynomial, as they remark). [S: Sono's JNT abstract,
  D'Souza §1.4]
- Wu (same family): ≥ 0.6024 simple, ≥ 0.8012 distinct. [S: Sono JNT 2025 introduction] — so h5's distinct 0.8761
  should be compared with 0.8012, not only with ζ's 0.839.
- Sono (J. Number Theory, 2025, "Zeros of Dirichlet L-functions on the critical line"): even primitive characters,
  smooth dyadic weight, (log Q)² ≤ T ≤ (log Q)^A: ≥ 0.6044 simple and on the line, 0.6107 on the line (Thm 1.1). [V abstract]
- Under GRH: CLLR 11/12 (Q. J. Math. 65 (2014)); Sono 0.9322 (Bull. Aust. Math. Soc. 2016). h5's GRH sanity value
  0.9315 agrees with D'Souza's "variational value 0.9322826 for kernel min(|α|,1) on |α| < 2".
- Hua–Yang 2608.16034 / 2609.27808: single prime modulus, bandwidth ≤ 1 (λ_bw = min{1, log(q−1)/ℓ}); no large-sieve
  gain is possible there (one modulus), constants 0.6725 / 0.83625. No overlap with h5 beyond the summed certificate.

## Checks of h5's inputs
- MV weighted large sieve: Σ_r |S(x_r)|² (N + (3/2)δ_r⁻¹)⁻¹ ≤ Σ|c_n|² is Montgomery–Vaughan, "The large sieve",
  Mathematika 20 (1973) 119–134, Theorem 1 (constant 3/2) [M: from memory, consistent with h5's reading; not
  re-read today]. With δ_{a/q} ≥ 1/(qQ) and N = o(qQ) it gives Σ_q q⁻¹Σ*_a|S(a/q)|² ≤ (3/2)Q(1+o(1))Σ|c_n|², and
  Σ*_χ|Σc_nχ(n)|² ≤ (φ(q)/q)Σ*_a|S(a/q)|² turns this into the 1/φ(q)-weighted character sum. [R] as a derivation.
- Harmonic count: Σ_{q≤Q} φ*(q)/φ(q) ~ 𝔖Q with 𝔖 = Π_p(1 − p⁻² − p⁻³): verified by hand (local factor
  (1 − 1/p)(1 + (p−2)/(p(p−1)) + 1/p²) = 1 − p⁻² − p⁻³). [R]
- Restricting to q ∈ (Q^{1−ε}, Q] changes neither constant. But note the per-χ denominators N_χ ~ (T/2π) log(qT)
  vary by a factor (1 − ε) over the family; harmless as ε → 0.
- Not checked: h5's steps (b), (d), (e) (error terms); D'Souza §2.5 and Appendix B list several places where the
  analogous steps of his draft were false as written (ends constant, moment floor, ramp rate) — worth reading
  before h5 claims [R].

## Recommendation
State h5's result as: *new variant, same mechanism as D'Souza [9]; weighted family; K = 3/(2𝔖); 0.7523, and ≈ 0.760
if D'Souza's killed-kernel lemma transfers.* It is not a record for Dirichlet families (0.9059 claimed with density
theorems) but it would be the best *density-free* constant, in the standard CIS normalisation, if written out.
A cleaner unclaimed target than pushing K: (i) bounded height / low-lying window (D'Souza: "sketch with a stated
gap", not claimed), (ii) real characters, (iii) verifying or refuting A–F's 1.263.
