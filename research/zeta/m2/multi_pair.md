# m2: the several-pair case of the configuration inequality — break attempts, exact reductions, and what remains

Scripts are in `m2/`: `cilib.py` (kernels and the continuum defect with analytic gradient), `attack1.py`, `attack2.py`
(finite configurations, free or forced depth), `percell.py`, `percell2.py` (exact infinite periodic limit),
`tau_search.py` (Φ_C against Φ_MT). Outputs are `*.out`.

Notation is Fabbian's (Zenodo 23198632, §2). Z is a finite conjugation-invariant multiset, E_Z(a) = Σ m e(za), and
Φ_g(Z) = ∫_{-1}^{1} g|E_Z|² − (2|Z| − κ(Z)). The weight of a pair x ± iy in E_Z is 2c_y(a)e(xa), with c_y = cosh(2πya).
- C = h3's kernel K5: r = f⋆f, value 0.677610, r(0) = 1.006013, r(1) = 0, τ_C = ∫_{|a|>1}|r| = 0.0112.
- MT = Montgomery–Taylor kernel: ψ⋆ψ/(∫ψ)², ψ = cos(√2 s) on [−½,½], value 0.672501, r(0) = 1.006127.
- Mixtures r_ε = (1−ε)MT + εC.
Φ is linear in g, so Φ_mix = (1−ε)Φ_MT + εΦ_C, and Φ_MT ≥ 0 at all depths (A–F rank/inertia; Lamzouri 2609.02882 Prop 2.1).

## 0. Bottom line
1. **No counter-configuration [N].** Multistart L-BFGS-B searches found no configuration with Φ_C < 0. The search space was
   finite continuum configurations with up to 9 pairs plus on-line simples, doubles and triples:
   - free depth, and forced depths ≥ 0.1, 0.17, 0.25, 0.4, 0.6;
   - structured starts: combs; Fabbian's integer-triple chain at y* = 0.3063; one pair between doubles at ±r (his Thm 4.13
     witness); the tight lattice of doubles at spacing 2 with some doubles turned into pairs; deep clusters with shallow mass;
     mixed depths; pair–simple chains.
   An exact infinite-periodic search (cells with up to 5 pairs and 5 on-line objects, any period, forced depth ≥ 0.1, 0.3,
   0.6) also found none. **So numerically τ := sup(−Φ_C/Φ_MT) = 0**: there is no configuration where the CGdL-type
   kernel needs MT's surplus. Every mixture (1−ε)MT + εC passes the same searches. The numerical evidence is for full
   (C)[K5], value 0.67761, not just for a mixture.
2. **The binding objects are combs [N, matches Fabbian Lemma 2.4].** At every forced depth the periodic optimum is the
   comb of pairs at spacing exactly 1, with Ψ_C = 4(r_C(0) − 1) = **0.02405 per pair** (Ψ_MT = 0.02451), independent of
   the depth. Inserting on-line points, defects or other spacings only increases Ψ.
   Without a depth constraint the binding objects are real: K5 is exactly tight on doubles at spacing 2 (K5(2k) = 0 and
   r(3/2) = 0, so Ψ = 0), and nearly tight on isolated objects.
3. **Fourier-side reductions [R]** (§2–§4):
   - the exact decomposition Φ(Z) = Φ(Z⁰) + Δ_P + 4Σ_{b,p} m_b β_{y_p}(x_b − x_p), with the pair–pair part kept whole on
     the Fourier side;
   - equal-depth pair-only configurations satisfy (C) for every CGdL-admissible kernel;
   - every periodic configuration of period ≤ 2 satisfies (C) in the limit;
   - two-object domination;
   - the exact periodic-cell formula, under which (C) is equivalent to Ψ ≥ 0 for all cells.
4. **No complete proof of (C) or of D_τ for several deep pairs.** §5 states exactly what remains, and why the routes are not
   in Fabbian's excluded classes.

## 1. Break attempts [N]
| search | space | min found | at |
|---|---|---|---|
| attack1 (K5, 60 random structures, free depth) | finite, ≤ 8 pairs + ≤ 14 on-line | Φ = +0.041 | depth 0, simples |
| attack2 (K5, equal forced depth y, p = 1..6 pairs, 40 starts each) | finite | Φ/p = +0.040 (y = .05), +0.086 (.1), +0.17 (.2), +0.55 (.3) | — |
| tau_search λ = 0, free depth, 2 × 300 starts | finite, structured | Φ_C = +0.030 (two simples + one double) | depth 0 |
| tau_search, depth ≥ 0.17 / ≥ 0.4, 300 starts each | finite | Φ_C = +0.377 / +3.69 (one pair between 4 doubles) | forced depth |
| percell2, depth ≥ 0.1 / ≥ 0.3 (150 cells each) | exact infinite periodic | Ψ_C = +0.02405 per pair | comb, spacing 1 |
| tau_search round 2, depth ≥ 0.1 (200) | finite | min Φ_C/pair = +0.063 (chain: pairs at odd sites, doubles at even); min Φ_C/Φ_MT = **0.653** (same chain) | y = 0.1 |
| tau_search round 2, depth ≥ 0.25 (200) | finite | min Φ_C/pair = +0.35 (finite comb of 8 pairs + one double); min Φ_C/Φ_MT = 0.91 | y = 0.25 |
| tau_search round 2, depth ≥ 0.6 (200) | finite | min Φ_C/pair = +1.29 (finite combs; the ends cost the self energy); min ratio Φ_C/Φ_MT = 0.88 (one pair + 4 doubles) | y ≥ 0.6 |
| periodic, depth ≥ 0.6 | exact periodic | (run pending at the time of writing; `pc2_y60.out`) | — |

Smallest ratio Φ_C/Φ_MT seen on any configuration that contains a pair of depth ≥ 0.1: 0.653 (pair–double chain at y = 0.1;
isolated deep pairs: 0.65 at y = 4, decreasing slowly). The infimum over all configurations is 0, attained on real configurations where Φ_C = 0
(doubles at spacing 2). Nowhere is Φ_C < 0.

Isolated pair, Φ_C/Φ_MT (`cilib`): 19.3 (y = .01), 1.68 (.05), 1.13 (.1), 0.99 (.2), 0.95 (.3), 0.91 (.5), 0.81 (1), 0.72 (2),
0.67 (3), 0.65 (4). The ratio decreases toward the ratio of the edge slopes of r_C and r_MT at a = 1, which is about 0.6.
δ := r_C − r_MT on [0,1] at a = 0, 0.1, …, 1:
−.0001, +.041, +.039, +.021, +.006, −.0003, −.004, −.011, −.020, −.019, 0.
So C puts *less* weight than MT exactly where deep pairs live (a near 1), and more in the bulk.

## 2. [R] Exact periodic-cell formula, and (C) ⟺ Ψ ≥ 0 for all cells
Take a cell of length d > 0 containing objects o at distinct positions x_o mod d. An object is either an on-line point of
multiplicity m_o (weight w_o ≡ m_o, target T_o = 2m_o − 1[m_o = 1]) or a simple pair x_o ± iy_o (weight w_o(a) = 2c_{y_o}(a),
target 4). Let Z_N be N consecutive translates of the cell by multiples of d. Assume g is even, continuous on [−1,1],
g(±1) = 0, and g'' is a finite measure (true for K5, MT and the mixtures). Then
  Φ_g(Z_N)/N → Ψ := (1/d) Σ_{k∈Z, |k|<d} g(k/d) |A(k/d)|² − Σ_o T_o,  A(a) := Σ_o w_o(a) e(a x_o).
*Proof.* E_{Z_N} = A·D_N with D_N(a) = Σ_{j<N} e(jda). |D_N|²/N is a Fejér kernel in da: period 1/d, mass 1/d per period,
concentrating at a ∈ Z/d. The function h := g|A|²1_{[−1,1]} is continuous on R, because h(±1) = 0. The target is additive
because positions are distinct mod d. ∎
**Equivalence.** (C)[g] for all finite Z implies Ψ ≥ 0 for every cell. Conversely, a finite Z placed in one cell of length
d → ∞ gives Ψ_d → Φ_g(Z) (Riemann sum). So (C) is *equivalent* to Ψ ≥ 0 for all cells. This is a convenient exact
finite-dimensional search space: all of §1's periodic rows are exact limits, not periodic-model approximations, and
the density is free.
**Heuristic consequence (dof count) [C].** If all in-band frequencies k/d ≠ 0 are cancelled, then Ψ = r(0)M²/d − T, with M
the mass per cell. Since T ≤ 2M, a violation needs mass density M/d < 2/r(0). Cancelling the ≈ d complex frequencies needs ≈ 2d
real parameters, and pairs carry 2 parameters per 2 units of mass, so the density is ≈ 2 and Ψ ≈ 4(r(0) − 1) per pair. This is
the comb. So every kernel with r(0) ≥ 1 is *marginal* at all depths, with margin 4(r(0) − 1), which is Fabbian's comb deficit ε_c.

## 3. [R] Small lemmas that hold for every CGdL-admissible kernel
Assume r is even and continuous, r̂ ≥ 0, r ≥ 0 on [−1,1], r ≤ 0 off it, and ∫r = 1. Put g = r1_{[−1,1]}.
- **(a) r(0) ≥ 1.** Poisson summation applies (r ∈ C_c with r'' a measure, so r̂ = O(x⁻²)) and gives Σ_k r̂(k) = Σ_n r(n). The
  left side is ≥ r̂(0) = 1 because r̂ ≥ 0. The right side is ≤ r(0) because r(n) ≤ 0 for n ≠ 0. ∎
  (So the comb deficit 4(r(0) − 1) is ≥ 0 automatically; this is the real double comb.)
- **(b) Equal depth, pairs only.** If Z consists of pairs x_p ± iy, all at one depth y, with multiplicities m_p, then Φ_g(Z) ≥ 0.
  More precisely, Φ_g(Z) ≥ 4∫g(c_y² − 1)|E|² + 4Σ_{p≠q}m_pm_q r̂(x_p − x_q) + 4Σ(m_p² − m_p) ≥ 0, where E = Σ m_p e(x_p ·).
  *Proof.* E_Z = 2c_yE, and ∫g·4c_y²|E|² = 4∫g(c_y² − 1)|E|² + 4∫g|E|². Then ∫g|E|² ≥ ∫_R r|E|² = Σ m m' r̂(x − x'), since
  r ≤ 0 off [−1,1]. Finally r̂ ≥ 0 and r̂(0) = 1, and the target is 4Σm_p. ∎
- **(c) Pointwise domination.** If |E_Z(a)| ≥ |E_{Z⁰}(a)| on [−1,1], where Z⁰ replaces each pair by a real double at its
  abscissa, then Φ_g(Z) ≥ Φ_g(Z⁰) ≥ 0 (same target; W1 for Z⁰). It holds in particular when:
  - Z has exactly two objects. For |u| = |v| = 1 and c₁, c₂ ≥ 1, |c₁u + c₂v|² − |u + v|² ≥ (c₁ − c₂)² ≥ 0.
  - Z is one pair plus one on-line point of multiplicity m ≤ 2: |2cu + mv|² − |2u + mv|² ≥ 4(c − 1)(c + 1 − m) ≥ 0.
  It fails for a pair plus a triple: 2c = 3 cancels. This is the mechanism of Fabbian's integer witness (Rem. 3.5); there the
  slack σ(3) = 3 must be used.
- **(d) Periodic configurations of period d ≤ 2 satisfy (C) in the limit (Ψ ≥ 0).** *Proof.* For d ≤ 2 the only in-band
  frequencies are 0 and ±1/d (a = ±1 carries g = 0).
  - If the mass per cell M ≥ 4: Ψ ≥ r(0)M²/d − T ≥ M²/2 − 2M ≥ 0, by (a) and T_o ≤ 2·mass_o.
  - If M ≤ 3 and the cell is real: Ψ ≥ 0 by W1 and the limit.
  - Otherwise the cell is {pair} or {pair, simple}. If d ≤ 1, then Ψ ≥ M² − T ∈ {0, 4}. If 1 < d ≤ 2, then |A(1/d)| ≥ 2c − 1 ≥ 1,
    resp. ≥ 2c ≥ 2. This dominates the real cell {double at 0, simple at d/2}, resp. {double}, which has the same M and T and
    |A(1/d)| = 1, resp. 2. That real cell has Ψ ≥ 0. ∎
  For d ∈ (2,3] two frequencies must be cancelled, and the cells with M ≤ 5 are a finite list. They are the first open case of
  the periodic programme. Numerically they are all ≥ 0 (§1).

## 4. [R] Exact Fourier-side decomposition for several pairs, and the reduced criterion
Let Z = B ∪ {x_p ± iy_p}, with B real, and let Z⁰ be Z with every pair collapsed to a real double. Write E := Σ_p e(x_p·),
C := Σ_p c_{y_p}e(x_p·), u_p := c_{y_p} − 1 ≥ 0, β_y(x) := ∫g(c_y − 1)cos(2πxa) da = Re ĝ(x+iy) − ĝ(x), and
G_y := r̂ + β_y (h3's G). Expanding |E_B + 2C|² − |E_B + 2E|² and using W1 for Z⁰ gives, **exactly**,
  Φ_g(Z) = OB(Z⁰) + [Δ_P + 4Σ_{p≠q} r̂(x_p − x_q)] + [Σ_b σ(m_b) + Σ_{b≠b'} m_b m_b' r̂(x_b − x_b') + 4Σ_b m_b Σ_p G_{y_p}(x_b − x_p)],
where
  Δ_P := 4∫g(|C|² − |E|²) da   (pairs only, kept whole on the Fourier side),   OB(Z⁰) = ∫_{|a|>1}|r||E_{Z⁰}|² ≥ 0.
- The first bracket depends on the pairs only.
- The second bracket is the energy of the real background B in the **superposed** field Σ_p G_{y_p}(· − x_p) of all pairs,
  plus B's own K-energy.
- This is h3's Lemma C with one change: the pair–pair terms are not split into the position-space terms
  2[G_{y_p+y_q} + G_{|y_p−y_q|}]. On the comb those terms cancel only through Poisson summation (Fabbian Lemma 2.4(b)), and
  here they never appear.

**Reduced multi-pair criterion (MP).** Let ℰ(F) := inf_B [Σσ(m_b) + Σ_{b≠b'} m m' r̂ + 4Σ m_b F(x_b)] ≤ 0, over real
backgrounds. Then (C) follows from
  Δ_P + 4Σ_{p≠q} r̂(x_p − x_q) + ℰ(Σ_p G_{y_p}(· − x_p)) ≥ 0   for every finite set of pairs.
By the packing lemma (h3 T1f §4), ℰ(F) ≥ −Σ_{cells of {F<0}} h_C(F), which leaves a statement about pairs alone.
- **Comb check.** For the infinite comb, Σ_k G_y(x − k) = r(0) + 2Σ_{n≥2} r(n)cos(2πnx) by Poisson (the n = ±1 term carries
  g(1) = 0). So the superposed field of a comb has no wells deeper than 2Σ_{n≥2}|r(n)|. The comb's tightness costs nothing
  in (MP).
- **[N] Δ_P ≥ 0 numerically** (`deltaP.py`, 3–8 pairs, depths ≤ 2, 200 starts): min Δ_P / Σ_p self_p = +7e−5. The near-zeros are
  deep pairs at spacing ≈ 0.53, i.e. edge cancellation. **[C] Conjecture P (pair-only depth monotonicity):** Δ_P ≥ 0 for every
  finite set of pairs. It is [R] for equal depths (§3b) and for two pairs (§3c).

## 5. What remains, and why these routes are not in Fabbian's excluded classes
**(i) Statement.** Numerically, (C)[K5] itself holds; τ = 0. The binding families are:
- the comb, margin 0.024 per pair at every depth;
- the tight doubles lattice at spacing 2, margin 0;
- isolated objects.
Nothing found needs MT's surplus. So the mixture route (h5 Lemma T) is numerically not needed. But no proof of D_τ is easier
than a proof of (C) itself: on the comb, Φ_MT is also only 0.0245 per pair. MT's surplus is of the same size as C's
everywhere it matters.
- Isolated deep pair: Φ_C/Φ_MT → ≈ 0.6–0.65.
- Comb: Φ_C/Φ_MT = 0.981.
**A pointwise route to τ is excluded.** h5 §1 notes that r_C ≥ ρ ∈ conv{ψ⋆ψ/(∫ψ)²} on [−1,1] would cap the value at
0.6725. So D_τ cannot come from kernel domination; it must be configuration-wise.

**(ii) The exact remaining inequality** (if Conjecture P is granted, everything else in §4 is exact or [R]):
  for every finite set of pairs, Δ_P + 4Σ_{p≠q} r̂(x_p − x_q) ≥ Σ_{C} h_C(Σ_p G_{y_p}(· − x_p)),
with the cell charges of the packing lemma, or ℰ in place of −Σh_C. For one pair this is h3's R4 < 1, numerically true at all
sampled depths for K5. For several pairs the field superposes linearly. The h_C grow quadratically in the well depth g ~ e^{2πy}y^{−2}, so a cluster gain is ~ g² ~ e^{4πy}y^{−4}; the self term of
a deep pair is ~ e^{4πy}y^{−2}, so isolated deep wells are paid with room (h3's asymptotics). Δ_P is small only when the pairs
cancel at the edge (comb-like). Then their superposed field is also small, because its β-part Σ_p β_{y_p}(x − x_p) = Re∫g·conj(C − E)(a)e(xa)da is the Fourier
transform of g·(C − E). Turning this last remark into an inequality is the open step. A Cauchy–Schwarz version loses a factor
√(number of background points).

**(iii) Barrier check.**
- (MP) is inhomogeneous in the pair mass. It uses each pair's own self term inside Δ_P, and the integrality of the
  background through the packing lemma (σ(m) and Σm² ≤ 2M for m ≤ 2). So Thm 3.4 / Cor 3.8 do not apply.
- It is not a block sum (Def. 4.10): every background point sees the superposed field of all pairs, and pair–pair terms are
  treated exactly.
- It is not a fixed-charge scheme (Def. 4.1): the cell charges are computed from the configuration's own field. That is the
  escape "configuration-dependent charges / exact first shell" of §12(ii).
- It removes no deep points (Prop 6.1).
- Using the triple slack σ(3) is compulsory at y* = 0.3063 (Rem. 3.5). The packing lemma keeps it (m² − 2m for m ≥ 3).

**(iv) The planned edge/bulk split (h3 T1f §6) in its fixed-charge form is excluded** (Fabbian Thm 4.5 / Evidence 4.9; m3).
I did not pursue it. §4 is the configuration-dependent replacement.

## 6. Next steps
1. Prove Conjecture P (Δ_P ≥ 0). It is a statement about sums of exponentials with weights c_{y_p}(a) ≥ 1, pairs only. A natural
   attempt: write c_pc_q − 1 = u_pu_q + u_p + u_q and show that ∫g(|U|² + 2Re U Ē) ≥ 0 using the monotonicity of u_p in a and
   r̂ ≥ 0.
2. Settle the d ∈ (2,3] periodic cells (finite list, two frequencies), which extends §3(d).
3. Turn (MP) into a certified computation for the superposed field at bounded depth, in Fabbian's style, but with the field
   recomputed per configuration rather than with fixed charges.
