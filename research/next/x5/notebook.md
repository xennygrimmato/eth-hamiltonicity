# x5 notebook: the crossing exponent ρ_× and the five-point set M5

24 Nov 2026. Tags: [R] proved here, [N] computed, [C] conjecture. Code in `code/`, outputs in `*.out`.
Inputs: `ideas-dichotomy.md` (ideas 1 and 2), c1/b2 notebooks, `two-proofs.md`, paper App. B.

## 0. Verdict

1. **Tool (Task 1) [N].** Prop. B.2 is implemented exactly and all of its claims are checked at small sizes. The exponent
   1/√2 is reproduced from exact counts.
2. **Idea 1, as written, is wrong in direction [R].** Sparser spectra (α < 1/2) do lower the paper-type certified exponent,
   but the identity then violates flattening: it cannot exist. The real constraint is a trade-off between the density
   exponent α and the degree budget β (deg Ψ = β·E).
   - The bound is ρ_cert ≥ max(2^{−α}, (β/2)^α/2), and flattening requires β^α ≥ 2.
   - The paper has β = 4, because its reflection symmetry makes the degree equal the total energy of the four parties. With
     β = 4 every α gives ρ ≥ 1/√2, with equality only at α = 1/2.
   - So the √E law is not forced by a group action. It is the optimum forced by "degree = total energy" plus flattening.
   - Denser spectra exist and give valid identities (I checked d = 2 harmonic levels exactly), but with β = 4 they are worse
     (ρ = 2^{−1/3} ≈ 0.794).
   - The corrected target is an identity with sub-additive degree, β < 4, together with α > 1/2.
3. **Idea 2 [N + R].**
   - M5 is confirmed non-Euclidean: det Gram = −1/4, and every 4-subset of Mat_2(F₂) is Euclidean. The 960 bad 5-sets form
     3 orbits; M5's orbit has size 576.
   - M5 is ℓ1-embeddable.
   - The violated Euclidean inequality is the 5-point negative-type inequality with weights (0,S,A,D,C) = (−2,−2,1,2,1). This
     is the finite form of (E5).
   - [R] No composition of crossing identities, with hubs anywhere, can refute a space that satisfies B.3. Together with c1's
     B.3 search on ρ_2 and ρ_3, this means the "joint three-wire identity" must be genuinely new, not a composition.
   - No cheaper cover was found. Nothing here proves contracting.

## 1. Task 1: exact Prop. B.2 (`code/crossing.py`, `b2_ranks.out`, `calib.out`)

**Implementation.** M(X) is built entry by entry as in App. B.3. B and C are computed as closed binomial sums:
B(r,n) = Σ_k C(r,k)C(r+n−k,n−k)(−y)^{n−k}, and similarly for C. Ψ = det M is evaluated with exact Bareiss determinants at
X = 0..Θ, and exact Newton interpolation gives the integer coefficients Ψ_N. Ranks over ℚ are taken as the maximum of the
ranks mod 2^61−1 and mod 2^31−1.

**Checks, all passed [N].** Classes (n,e) = (1,4), (1,6), (1,8), (1,10), (2,12) on both wires, and (1,12)×(1,4):
- deg Ψ ≤ Θ (by an extra evaluation at X = Θ+3);
- Ψ(1) = ε·[s_c = s_a^T, s_d = s_b^T] with ε = +1, i.e. (a) holds;
- rk_{ad|bc}Ψ_N ≤ (N+1)P(N) and rk_{ab|cd}Ψ_N ≤ (N′+1)P(N′), i.e. (b) and (c) hold;
- rk_{ab|cd}Ψ_N = rk_{ad|bc}Ψ_{Θ−N} for equal classes (the reflection).

**Rank profiles [N].**
- The actual ranks are far below the bounds at small N. For n = 1 classes, rk_{ad|bc}Ψ_{2k} = 1, 3, 7, 13, 21, … = k² + k + 1,
  until it saturates at |Σ|². The bound gives 1, 6, 20, 49, 108.
- For n = 2 the sequence is 1, 3, 7, 11, 16, 21, 23, 24, 25.
- At these sizes almost every piece is full rank in both cuts, so the finite-size "ρ" is near 1. The exponent is purely
  asymptotic.
- The third cut, ac|bd (Idea 4 data): every piece has full rank |Σ|², except the middle piece N = Θ/2, which drops to
  6/9, 10/16, 15/25, 15/25. Only the matching cut sees the middle.

**Calibration of 1/√2 [N].** Symbols of energy 2n ↔ partitions of n, so P(E) = Σ_{n≤E/2} p(n), and |Σ| is the largest Durfee
class.
- Without polynomial factors, ρ(E) = max_N [ln P(N) + ln P(4E−N)]/(4 ln P(E)) is:

  | E | 20 | 100 | 200 | 500 | 1000 | 2000 | 4000 |
  |---|---|---|---|---|---|---|---|
  | ρ(E) | 0.801 | 0.754 | 0.742 | 0.731 | 0.725 | 0.720 | 0.717 |

- The excess over 1/√2 shrinks by a factor ≈ √2 per doubling of E, i.e. like E^{−1/2}. So the limit is 1/√2.
- With the (N+1) factors and the true class sizes, the same quantity is 1.15, 0.92, 0.87, 0.83, 0.80 at
  E = 100, 500, 1000, 2000, 4000. It converges much more slowly.
- ln P(E)/√E → π/√3 = 1.814 (1.72 at E = 4000).

**Framing (precise).**
- For two crossing wires of λ bits each, let ρ_× = lim inf over identity families with 2^{o(λ)} pieces of
  max_pieces (c_{ad|bc} + c_{ab|cd})/(4λ).
- Flattening gives ρ_× ≥ 1/2 [R]: some piece is full in one cut. The paper gives ρ_× ≤ 1/√2.
- Under PH, ρ_× = 1/√2 (b2). So **any family with ρ < 1/√2 refutes PH, and therefore proves contracting.**
- The same statement holds for finite identities via two-proofs Prop. 1 with D = 2, after the computation below [R].
  - A piece of rank 2^ℓ across ad|bc, routed with optimal hubs between unit-disc terminals ±e1 (one wire) and ±e2 (the other),
    costs √2·(ℓ + √(4m² − ℓ²)) for ℓ ≤ √2·m, and 4m otherwise.
  - So a finite identity C_{2,m} = Σ_{a≤A} Ψ_a proves contracting as soon as
    max_a g(min(ℓ_row,a, ℓ_col,a)) + 2·log₂A < 2√2·m, where g(ℓ) = ℓ + √(4m²−ℓ²).
  - The paper's pieces sit exactly on g = 2√2·m at N = Θ/2.
  - This is x3's √D-shortening criterion at D = 2. I did not search for such identities.

## 2. Idea 1: dispersion engineering (`code/dispersion.py`, `code/crossing_d.py`, outputs `dispersion*.out`, `crossing_d.out`)

**What gives √E.**
- The levels have energies 2i+1, one mode per level (linear dispersion, density of states constant). Symbols are then
  partitions (Frobenius), and ln P ~ π√(E/3).
- Bosonic versus fermionic modes do not change the exponent: both are partition counts.
- Levels ~ i^k give ln P ~ E^{1/(k+1)}. A d-dimensional oscillator (degeneracy ~ ε^{d−1}) gives E^{d/(d+1)}. Lacunary spectra
  give step-like P.

**Proposition 1 (degree–density trade-off) [R].**
- *Hypotheses.*
  - A family of identities Σ_{N=0}^{Θ} Ψ_N = ⟨Q⟩_{ac}⟨Q⟩_{bd} with rk_{ad|bc}Ψ_N ≤ T·P(N) and rk_{ab|cd}Ψ_N ≤ T·P(Θ−N),
    where T, Θ = e^{o(λ)}, λ = ln Q → ∞, and F = ln P.
  - The paper-type certified exponent is ρ_cert := max_N [F(N) + F(Θ−N)]/(4λ).
- *Conclusion.*
  - (i) Flattening forces F(Θ) ≥ 2λ − o(λ), because the crossing has rank Q² in ad|bc and ranks are subadditive.
  - (ii) Hence ρ_cert ≥ F(Θ/2)/(2λ) ≥ F(Θ/2)/F(Θ) − o(1).
  - (iii) If the wires are symbol classes of energy E, so that λ ≤ F(E), and Θ = βE, then also ρ_cert ≥ F(βE/2)/(2F(E)).
- *Power-law case.* For F ~ κx^α this gives **ρ_cert ≥ max(2^{−α}, (β/2)^α/2)**, and (i) requires β^α ≥ 2.
  - The paper has β = 4 (Θ = 2(e1+e2)), so ρ_cert ≥ max(2^{−α}, 2^{α−1}) ≥ 1/√2, with equality iff α = 1/2.
  - The ideas file's ρ = 2^{α−1} for α < 1/2 violates (i): the top piece cannot reach rank Q².
- *General F.* If t ↦ ln F(2^t E) is concave on [0, 2], then (i) and (iii) give ρ_cert² ≥ F(2E)²/(4F(E)²) ≥ F(4E)/(4F(E)) ≥ 1/2.
  So only spectra whose ln ln P is locally convex in ln E could escape. That is a loophole, but see the numerics.
- **Why 1/√2 is rigid in the paper's mechanism.** The reflection X^Θ Ψ(1/X; a,b,c,d) = Ψ(X; a,d,c,b) multiplies each party by
  X^{its energy}. So the degree equals the total energy, β = 4, and α = 1/2 is the unique optimum. This is a statement about
  the degree budget, not a group action on the modes.

**Numerics [N].** E = 25..400. Each row lists α_eff, flat(E) := ln P(4E)/(2 ln P(E)) (an identity requires ≥ 1), ρ_cert with
Θ = 4E, and ρ_opt, which is ρ with Θ lowered to the flattening minimum (a hypothetical β < 4).

| spectrum (fermions) | α_eff (E=400) | flat | ρ_cert (Θ=4E) | ρ_opt (β<4) |
|---|---|---|---|---|
| linear 2i+1 (paper) | 0.55 → 1/2 | 1.065 ≥ 1 | 0.733 → 0.707 | 0.688 → 0.707 |
| i² | 0.40 | 0.863 < 1: impossible | 0.660 | > 0.75 |
| i³ | 0.30 | 0.753 < 1: impossible | 0.615 | > 0.81 |
| 2D oscillator | 0.70 | 1.31 | 0.814 → 2^{−1/3} = 0.794 | 0.617 → 2^{−2/3} = 0.630 |
| lacunary 4^j × 2^j, 2^j × 2^{j/2} | 0.40–0.41 | 0.87 < 1 | 0.66 | > 0.75 |

- In all runs (7 spectra × up to 6 sizes) there is no instance with flat ≥ 1 and ρ_cert < 1/√2.
- The bosonic runs are in `dispersion.out` where they finished, with the same pattern.

**The d-dimensional construction exists [N].** `crossing_d.py` replaces each level by a d-tuple, with:
- energy Σ(2r_t+1);
- kernels B_d = Π B(r_t, n_t) and C_d = Π C(r_t, n_t);
- the factor (y−1) replaced by (y−1)^d.

Results:
- (B.1) holds factorwise, so the paper's proof of (b) goes through verbatim [R].
- Exact checks at d = 2, e = 6 and e = 8 (|Σ| = 4 and 10): Ψ(1) is the matching with ε = 1, and deg ≤ Θ = 2(e1+e2).
- The ad|bc ranks are 1, 2, 4, 9, 24, 48, 72, … and the ab|cd ranks mirror them at the top. So (c) holds numerically.
- The paper's literal reflection formula fails for 416 of 6400 coefficients at d = 2. Whether (c) holds exactly is [C].
- This family has α = 2/3 and β = 4, hence ρ_cert = 2^{−1/3}. **The dispersion knob is real but turns the wrong way unless
  β drops.**

**Corrected target for Idea 1 [C].** A graded identity whose degree is sub-additive in the party energies (β < 4), with a
dense spectrum (α > 1/2, β^α ≥ 2). For example, the 2D-oscillator counting with β = 2^{3/2} would give ρ = 2^{−2/3} ≈ 0.63, and
would prove contracting. Under PH no such identity exists. I see no unconditional obstruction: Ψ_0 and Ψ_Θ only need to be
products in one cut each.

## 3. Idea 2: M5 (`code/m5.py`, `code/floors.py`, outputs `m5.out`, `m5_weighted.out`, `floors.out`)

**Geometry [N, exact].**
- Squared distances on (0,S,A,D,C): |0S|² = |AD|² = |CD|² = 2, all others 1.
- The Gram matrix based at 0 has det = −1/4, so M5 is not Euclidean.
- None of the 1820 4-subsets of Mat_2(F₂) is non-Euclidean. 960 of the 4368 5-subsets are.
- Under a ↦ P a^{(T)} Q + B the bad 5-sets form 3 orbits:
  - size 576, distance multiset 1⁷2³ (this is M5);
  - size 288, 1⁵2⁵;
  - size 96, 1⁶2⁴.
- M5 is in the cut cone (LP feasible), so it is ℓ1-embeddable.
- The violated Euclidean inequality: the centred matrix P·D²·P has the positive eigenvalue (√161 − 11)/10 = 0.169. The integer
  witness v = (0:−2, S:−2, A:1, D:2, C:1) has Σv = 0 and vᵀD²v = +2 > 0, where Euclidean spaces have ≤ 0. Written out:
  4|0S|² + 2|AD|² + 2|CD|² + |AC|² ≤ 2(|0A|²+|SA|²+|0C|²+|SC|²) + 4(|0D|²+|SD|²).
  M5 gives 17 ≤ 16, false, and the excess is exactly |AC|². This is the (E5) of the ideas file in negative-type form.
  - The 4-point analogue with weights (1,−1,1,−1) is the Berg–Nikolaev quadrilateral inequality = CAT(0), which B.3 does
    give (Thm C.1).
  - So **C ⇐ "prices satisfy the 5-point negative-type inequality with weights (−2,−2,1,2,1)"**, which buildings violate.
  - Its "wires" are the same-sign pairs 0S (×4), AD (×2), CD (×2) and AC (×1). Its "routes" are the opposite-sign pairs.

**The finite statement.** This specialises c1's cover characterisation.
- M5 is not a price ⟸ for some weights w on M5-pairs and infinitely many m there is a cover of
  H_w^{(m)} = Π_e ⟨2^{⌊m w_e⌋}⟩_e by 2^{o(m)} graph tensors on M5 ∪ hub points with cost exponent ≤ Σ_e w_e|e| − ε.
- Hubs must be points whose distances are known in every price extension: points of ρ_μ, or CAT(0)-geodesic points with
  comparison upper bounds.
- It suffices to take hubs in Mat_μ(F₂), since then the cover proves that ρ_μ is not a price, which already gives contracting.

**Lower bounds on covers from explicit spectral points (flattenings, CVZ, support functionals = partition-star metrics
δ ≤ M5) [N, LP over all 52 partitions].**

| network | M5 length | best explicit | ratio |
|---|---|---|---|
| diagonals 0S, AD (= crossing) | 2.828 | 2 | 0.707 |
| 0S, AD, CD | 4.243 | 3.414 | 0.805 |
| 0S, AD, CD, AC | 5.243 | 4 | 0.763 |
| (E5) weights 4·0S + 2·AD + 2·CD + AC | 12.314 | 9 | 0.731 |
| square 0ASD, all six pairs | 6.828 | 6 | 0.879 |
| all 10 pairs | 11.243 | 10 | 0.889 |

So explicit points leave a window of 20–30%. A cheap cover must land in it, and on the (E5) network it would have to beat
12.31 with all hubs in ρ_μ.

**Compositions of crossings cannot do it (Proposition 2) [R].**
- *Statement.* Let Y be a pseudometric space containing the parties and all hubs, and suppose B.3 holds in Y. Then every cover
  obtained by iterating "apply the crossing identity (any p, q) to two wires, route each piece through either hub pair, take
  products and restrictions" has Y-cost exponent ≥ the Y-length of the original network.
- *Proof.*
  1. Induct on the steps, with the potential "Y-length of the current network".
  2. In one crossing step, B.3 in Y supplies (r, r′) in the disc r² + r′² ≤ 2(p²+q²) with p|xv| + q|yu| ≤ both routed costs.
  3. The paper's pieces sweep the boundary circle. Scaling (r, r′) radially onto the circle gives a piece whose two costs are
     both at least as large, because the costs are monotone in r and r′.
  4. So the worst piece costs at least the potential. Products add lengths. ∎
- *Consequence.* c1 found B.3 unviolated on ρ_2 and ρ_3 with all 8 points in Mat_μ (hill climbing). So no composition of
  paper crossings with hubs in Mat_{≤3} refutes ρ_μ [R + N]. If c1's [C] "B.3 holds in CAT(0)" is true, no composition with
  hubs anywhere does.
- The ideas file's step (c), "two paper crossings sharing wire 0S", is therefore excluded. In particular, splitting 0S into two
  half-width wires gives product pieces, and φ(product) = product of φ, so each half is a separate B.3 instance.

**Floors (ideas step (b)) [N] (`floors.out`).**
- Setting: b2's (★) score F = Σ_K max(b_K, 0) for 5-party piece problems. F_ρ3 places legs and hubs in Mat_3(F₂) (512 points,
  coordinate hill climbing). F_E places them in ℝ⁵ (smoothed Nelder–Mead, then Powell).
- Calibration (crossing): F_E = 2.817 → 2√2, the far-leg supremum. F_ρ3 = 2.0. Hubs at rank-metric vertices are coarse.
- See the table in §4 for the other problems. A problem with F_ρ3 > F_E would define a window where a piece family proves
  contracting while staying consistent with FH.

Results (30 hill-climbing restarts for ρ, 10 optimiser restarts for E):

| problem (wires; cuts) | F_ρ3 | F_E | ratio |
|---|---|---|---|
| crossing 0S, AD; {0A}, {0D} (calibration) | 2.000 | 2.817 (→ 2√2) | 0.71 |
| 0S, AD, CD; {0A}, {0D}, {0C}, {0D} (the {0D} cut is listed twice: an input typo) | 6.000 | 7.328 | 0.82 |
| 0S, AD, CD; {0AC}, {0D}, {0A}, {0C} | 8.000 | 8.001 | 1.00 (tie) |
| 0S, AD, CD, AC; {0A}, {0C}, {0D} | 3.000 | 5.399 | 0.56 |
| 0S, AD, CD; {0A}, {0C}, {0D} | 4.000 | 5.192 | 0.77 |

- **No window.** In every problem F_ρ3 ≤ F_E. Hubs restricted to rank-metric vertices are too coarse to beat the Euclidean
  floors, and the far-leg supremum is not available in a bounded discrete space.
- The one tie, {0AC}, {0D}, {0A}, {0C}, equals the trivial "all wires full" value 8.
- So the (★) method with hubs in Mat_3 gives no target where ρ_μ demands more than FH does. A real target would need hubs at
  CAT(0) geodesic points of a price extension, whose distances are known only as comparison upper bounds. That is not done.

## 3b. Follow-up after the lead's message

**(3) Exact region for the power-law Fock framework [R].**
- *Setting.* Write per-wire λ = κE^α and total degree Θ = βE (equal wires). Flattening requires β^α ≥ 2.
- *Bound.* The certified exponent satisfies ρ_cert ≥ max(2^{−α}, (β/2)^α/2).
- *Region.* ρ_cert < 1/√2 is possible iff **α > 1/2 and 2^{1/α} ≤ β < 2^{1+1/(2α)}**. The interval is nonempty exactly when
  α > 1/2.
- *Best point.* At β = 2^{1/α} (flattening tight) the bound is ρ = 2^{−α}. For example:
  - α = 2/3 (2D oscillator counting): β ∈ [2.83, 3.36), ρ down to 0.63;
  - α = 1: β ∈ [2, 2.83), ρ down to 1/2.
- *Paper.* The paper sits at the corner (α, β) = (1/2, 4).
- *No emptiness theorem.* The region is nonempty, and flattening alone does not exclude it. Only PH (b2) does. So there is no
  structural emptiness theorem at the level of rank counting; deciding it is equivalent to the open problem.
- **One-line target:** a graded identity Σ_N Ψ_N = crossing with rk_{ad|bc}Ψ_N ≤ e^{κN^α + o}, rk_{ab|cd}Ψ_N ≤ e^{κ(Θ−N)^α + o},
  and Θ < 2^{1+1/(2α)}·E, where the wires have ln Q = κE^α and α > 1/2.

**(1) What forces "degree = total energy" [R for the paper's mechanism, C beyond].**
- *The degree comes from the reflection.* Its multipliers are the party energies: X^{e1} at a and at c, X^{e2 ∓ 2n2} at d and
  at b.
- *The bond needs capacity for two parties.* In the Schur-complement proof, the bond across ad|bc has the *same*
  single-particle spectrum as one party. Its sectors T must encode the pair (s_a, s_d) at the top.
  - For the linear spectrum the cheapest injective encoding is Lemma B.1's interleaving, which costs energy (√e_a + √e_d)².
  - That equals e_a + e_c + e_b + e_d at equal wires. So in d = 1, "degree = total energy" and "flattening-tight" coincide,
    and β = 4 is forced twice.
- *In d dimensions the bound is loose.* For a d-dimensional spectrum the encoding needs only (e_a^α + e_d^α)^{1/α} = 2^{1/α}E,
  but the paper-type reflection still charges 4E. My d = 2 family is wasteful in exactly this sense.
- *What a β < 4 construction requires.* A kernel B on the d-dimensional levels with:
  - (B.1) for the weight X^{ε(r)} (needed for (b));
  - a reflection C(r,n) = X^{h(n)}·B(r,n)|_{X→1/X} whose degrees satisfy Σ h ≤ (β/4)·Σ ε.

  For α = 2/3 that means h ≤ 0.84·ε on average. With product kernels h = ε exactly. Whether a non-product kernel exists
  (e.g. one adapted to SU(1,1)^d ⊂ Sp(2d), or a Pfaffian whose rows are shared by a and d) is the open step [C].

**(2) Characteristic p [N] (`code/charp.py`, `charp.out`).**
- *Setup.* The pieces are integral and Σ_N Ψ_N = crossing holds mod p, so the same Ψ_N form an identity over F_p.
- *Ranks drop strongly mod p, and differently for each p.* Class (1,10)², Q = 5:
  - ab|cd rank of Ψ_0 is 25 over ℚ but 4 over F₂ and 1 over F₃;
  - middle pieces drop to 13–23.
- *Finite-size exponent* max_N ln(r_N r′_N)/ln Q⁴: ℚ 1.00, F₂ 0.96, F₃ 0.97, F₅ 0.89. Class (2,12)²: F₂ is markedly lower
  (most pieces have rank 8–12 of 25).
- *Caveat.* These are finite sizes, and the selector penalty 2·log₂(Θ+1) is ignored, so this is not evidence for the
  asymptotic exponent. It is consistent with a field-dependent exponent, and ties to z1/Idea 3. For the α/β bookkeeping: over
  F_p, the "degree" relevant to ranks is the rank profile, not the polynomial degree, so the region of (3) may be reachable
  without β < 4 polynomially [C].

## 4. Honest table

| # | tried | numbers | status |
|---|---|---|---|
| 1 | exact Prop. B.2, all claims | 6 class pairs, all asserts pass | [N] done |
| 1 | calibration of 1/√2 | ρ(E) = 0.801 → 0.717 at E = 4000, excess ∝ E^{−1/2} | [N] reproduced |
| 1 | finite-D=2 certificate (two-proofs Prop. 1) | g(ℓ) = ℓ + √(4m²−ℓ²); the paper sits on g = 2√2·m | [R], left to x3 |
| I1 | sparser spectra (α < 1/2) | i², i³, lacunary: flat = 0.75–0.88 < 1 | **excluded** [R]: flattening |
| I1 | denser spectra with β = 4 | d = 2 oscillator: valid identity [N], ρ = 2^{−1/3} | excluded (worse) |
| I1 | bosonic modes | same exponents as fermions | no effect [N] |
| I1 | (α, β) region | ρ < 1/√2 iff α > 1/2 and 2^{1/α} ≤ β < 2^{1+1/(2α)} | [R] target, open |
| I1 | ALS profile search | not run: finite sizes saturate (pieces full rank at Q ≤ 5), so no calibrated target | skipped, with reason |
| I2 | M5 non-Euclidean, 4-sets Euclidean | det Gram = −1/4; 0 bad 4-sets; 960 bad 5-sets in 3 orbits | [N] verified |
| I2 | M5 ℓ1 / cut cone | feasible | [N] |
| I2 | violated inequality | negative type, v = (−2,−2,1,2,1), excess = \|AC\|² | [N] exact |
| I2 | explicit spectral points vs M5 length | ratio 0.71–0.89; worst ≈ 0.707 (crossing) | [N] |
| I2 | composed crossings (step (c)) | cannot beat any B.3 space | **excluded** [R] |
| I2 | (★) floors, hubs in Mat_3 vs ℝ⁵ | F_ρ ≤ F_E in all 5 problems | no window [N] |
| I2 | cheaper cover of an M5 network | none found | not proved |
| I3 | char-p ranks of the paper's pieces | finite-size exponent 1.00 (ℚ), 0.96 (F₂), 0.89 (F₅) | [N] lead, finite size only |

Nothing here proves contracting. The two clean outputs:
- the (α, β) theorem and target (Prop. 1 plus §3b), which says why 1/√2 is rigid;
- the exclusion of compositions for M5 (Prop. 2), together with the explicit (E5) negative-type inequality that a new
  5-party identity would have to prove.
