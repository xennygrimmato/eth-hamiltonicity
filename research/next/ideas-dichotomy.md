# Ideas for deciding the flat/contracting dichotomy of "VP ≠ VNP over every field"

24 Nov 2026. Idea generation only; nothing below is proved unless tagged.
Tags: [K] known/cited, [R] short argument given here (check before use), [N] computed here, [C] conjecture/heuristic.
Inputs read: `vpvnp/c1/notebook.md`, `vpvnp/b2/notebook.md`, `vpvnp/b1/notebook.md`, `engine3-STATUS.md`, paper §2, App. A–D.

## 0. Framing that the ideas share

**Three outcomes, not two.** FH (every finite Euclidean set is a price) and C (contracting) are not known to exclude
each other (c1 §4). The decisive theorems are:
- **C** holds  ⇐  ρ_2 (or any ρ_μ) is not a price  ⇐  some finite subset of Mat_μ(F₂) with the rank metric is not a price.
- **C** holds  ⇐  ¬FH  ⇐  ¬PH  ⇐  the Euclidean unit square is not a price  ⇐  crossing pieces with ρ < 1/√2 exist (b2).
- **FH** holds  ⇔  the cube vertices ({0,1}^n, √Hamming) are prices for all n (Step 8 of D.2 fills the cube) [R from K].

**"What is the p of tensor geometry?"** [R/C] The crossing identity has pieces of bond exponents (r, r′) with
r² + r′² ≤ 2(p² + q²) because wires are Fock spaces with ln(dim) ≈ κ√E and energy E is additive. Define the crossing
exponent ρ_× = lim min-max (c_row + c_col)/(4λ) ∈ [1/2, 1/√2]. Every *known* spectral point gives a tree metric
(partition-star, c1 §3): that is the "ℓ∞ / 4-point-equality" end, ρ_× = 1/2. The only *known* identity gives the ℓ2 end.
PH says the truth is ℓ2; Majdoddin's Open Problem 1 (ideal pieces) says ℓ∞. Anything strictly inside proves C.

**Two computations done here** [N] (script: scratchpad `m5.py`, 5 lines of numpy):
- Every 4-subset of (Mat_2(F₂), √rk) is Euclidean. 960 of the 4368 5-subsets are not. So ρ_2 is already non-Euclidean
  (the paper's D.3 only says μ ≥ 3), and the smallest witness has 5 points.
- Witness **M5** = {0, S=I, A=e11, D=e22, C=e11+e12}: |0S|=|AD|=|CD|=√2, the other seven distances are 1.
  (0,A,S,D) and (0,C,S,D) are two flat unit squares on the three common vertices 0, D, S, with |AC| = 1.
  In Euclidean space the fourth vertex of a square is unique, so |AC| would be 0. Around the diagonal 0–I there are six
  such completions forming a hexagon with right angles: cone angle 3π instead of 2π.

**A negative remark** [R]. Fast matrix multiplication cannot help by itself. A rank bound G ≤ ⟨R⟩ followed by
⟨R⟩ ≤ (any tree network) only yields Σ_{e∈G}|e| ≤ maxcut(G)·Steiner(S) when ω = 2, and that already follows from the
triangle inequality in every metric space. Rank bounds also carry an absolute scale, and prices are scale-free.
Only graph-tensor-to-graph-tensor identities with a non-trivial *family* of piece shapes (like Fock) can cut prices.

---

## Idea 1 (constructive → Contracting). Dispersion engineering of the crossing identity

**Idea.** In Prop. B.2 the piece Ψ_N has rank ≤ P(N) across one cut and ≤ P(Θ−N) across the other, and the wire has
ln|Σ| ≈ κ√e. If the same statement held for a mode system with ln P(E) ≈ κE^α, the pieces would satisfy
r^{1/α} + r′^{1/α} ≤ 2(p^{1/α} + q^{1/α}) and the crossing would have ρ_× = 2^{α−1} [R]. α = 1/2 is the paper
(levels of energy 2i+1, a 1+1-dimensional free fermion). Levels of energy ~ i² give α = 1/3 and ρ = 0.63; i^m gives
α = 1/(m+1). The number of terms stays Θ+1 = poly(λ). Any α < 1/2 refutes PH and proves C. So: look for an
interpolating determinant (matching at X = 1, product forms at X → 0, ∞) for a *convex* dispersion, replacing Meixner
polynomials by another family (q-Meixner, Al-Salam–Chihara, little q-Jacobi; weight y^{g(r)} instead of y^r).

**Why it might work.** The Pythagoras law is an artefact of one specific partition-counting rate, not of anything
structural that we can see; Lemma B.1's interleaving (P(k²E) ≥ P(E)^k) is the only place the exponent 2 enters.
All explicit spectral points are consistent with any α ∈ (0, 1/2].

**Most likely failure.** The telescoping proof of (B.1) needs the geometric weight, i.e. the harmonic (SU(1,1)) spectrum;
for other dispersions no determinant has both product limits. If FH is true this must fail, and the *way* it fails
(which rank bound breaks first) is the uncertainty principle of Idea 4.

**First experiment (< 2 h).** Calibrated feasibility search, no orthogonal polynomials needed.
1. Implement Prop. B.2 exactly for small (n_i, e_i) (|Σ| up to ~10) and record the profile (rk_{ad|bc}Ψ_N, rk_{ab|cd}Ψ_N)_N.
2. ALS/Gauss–Newton search for a decomposition of the same crossing tensor into the same number of pieces with a
   prescribed rank profile. Calibration: the paper's profile must be found (if ALS cannot find a known solution, stop).
3. Tighten the profile towards the "α = 1/3" shape (replace P by the count of symbol-like sets with energies i²)
   and towards ideal (r·r′ = const).
Outcome: tighter profile feasible at ≥ 3 sizes with a consistent pattern ⇒ extract the kernel, strong lead to C.
Calibration found but every tightening infeasible ⇒ evidence for PH plus the exact list of tight rank constraints.

## Idea 2 (small finite case, μ = 2 → Contracting or a new structure theorem). Do flats branch in a price space?

**Idea.** By pull-back monotonicity (c1 Prop. 1), "M5 is not a price" ⇒ ρ_2 not a price ⇒ ρ_3 not a price ⇒ C. In
Euclidean space the Euler quadrilateral identity gives the 5-point inequality
(E5)  |AC| ≤ √(σ_A − |0S|² − |AD|²) + √(σ_C − |0S|² − |CD|²),  σ_X = sum of squared sides of (0, X, S, D) [R].
M5 has left side 1 and right side 0. CAT(0) gives only the inequalities σ ≥ diag², never (E5). So:
**C ⇐ "prices satisfy (E5) with any modulus"**, i.e. flat squares in a price space have a unique fourth vertex;
and ¬C ⇒ flats branch (the price space is a genuine rank-2 building, not a product of trees: I checked that tree×tree
and tree×ℝ have unique square completion [R]). The needed identity is a *joint* crossing identity for three wires
0S, AD, CD in which the two Fock gradings on the shared wire 0S (frames {e1,e2} and {e1,e1+e2}, related by a shear)
are refined simultaneously.

**Why it might work.** It is the first place where ρ differs from every Euclidean and every product-of-trees model, it
lives on 5 parties, and a shear is not an orthogonal map: three frames of F₂² cannot all be orthonormal, so a
"Gaussian" identity respecting all three should lose a constant, which is exactly s² < 2 at μ = 2 (Hilbert pull-backs
have D(2)²/D(1)² ≤ 1.5, c1 §4).

**Most likely failure.** The building is a consistent model of every identity (¬C is true), or the identity exists only
asymptotically and no small search sees it. M5 looks ℓ1-embeddable (pentagonal inequalities hold by hand), so no
single piece shape can refute it; a one-parameter family of shapes is needed, as in Fock.

**First experiment (< 2 h).** (a) LP: confirm M5 is in the cut cone; list the 960 bad 5-sets up to symmetry (expect 1–3
orbits). (b) With b2's (★) machinery, find the weighted configuration on M5 (weights on AC and the three diagonals,
hub pairs for the cuts {0,A|S,D}, {0,D|S,A}, {0,C|S,D}, {0,D|S,C}) that maximises
[floor from ρ_2 with hubs in the 16 points] / [best Euclidean floor]. A ratio > 1 defines a concrete piece problem:
any family below the ρ_2 floor proves C. (c) Evaluate the composition of two paper crossings sharing wire 0S on that
configuration. If the composition already beats the ρ_2 floor, C is proved; expect equality, and then the gap to the
Euclidean floor is the target for a search as in Idea 1 step 2.

## Idea 3 (finite fields → characteristic-dependent answer). Lucas factorisation of the crossing determinant

**Idea.** The price notion depends on the field, and by Strassen only on its characteristic, so the dichotomy may be
decided differently in characteristic p. Mod p the kernels (1+t)^r/(1+yt)^{r+1} factor digit by digit (Lucas), so the
coefficient tensors Ψ_N mod p acquire a self-similar (Sierpinski-like) structure, and in characteristic 2 determinant
= permanent, so bosonic variants are free. Flattening ranks of the *same integral pieces* can drop mod p, and extra
decompositions via Frobenius (x+y)^p = x^p + y^p become available. Look for ρ_× < 1/√2 over F₂ first.

**Why it might work.** The paper's pieces are integral for a reason (they are reduced mod p), and rank drops of
binomial-type kernels mod p are the rule, not the exception. Nothing in the flat-case analysis uses char 0.

**Most likely failure.** Ranks drop only by constant factors, not in the exponent; the exponent is set by the count of
symbols, which is characteristic-free.

**First experiment (< 2 h).** Reuse the implementation of Idea 1 step 1. Compute both flattening ranks of every Ψ_N over
ℚ, F₂, F₃, F₅ for all (n_i, e_i) with |Σ| ≤ ~30; fit ln rk against √N. Outcome: slope over F₂ smaller than over ℚ by a
stable factor ⇒ C in characteristic 2 is live, push sizes; identical slopes ⇒ drop this idea.

## Idea 4 (route to Flat over ℂ). Crossing-cut quantum functionals, the cover roof, and an uncertainty principle

**Idea.** Every Euclidean metric is a Crofton average of cut metrics. For the unit square the weights are explicit:
θ = (1/√2, 1/√2, 1 − 1/√2) on the cuts {12|34}, {14|23}, {13|24} gives sides 1 and diagonals √2 [R]. So on graph
tensors the wanted spectral point must equal F^θ(t) = sup over the orbit closure of exp Σ_S θ_S·S(ρ_S), a quantum
functional on *crossing* bipartitions. F^θ is monotone and super-multiplicative but not subadditive on covers; the
crossing identity is exactly the witness (the ℓ1 square θ = (1,1,0) is killed by it). Take the cover roof
Ĝ^θ(t) = inf over covers Σ_j F^θ(t_j). It is an upper functional, so Prop. A.5 + the triple trick A.7 give a spectral
point φ ≤ Ĝ^θ with φ(C) = lim Ĝ^θ(C^m)^{1/m}. Hence **the square is a price as soon as Ĝ^θ regularises to full value
on the six wires**, which is an *entropic uncertainty relation*: in every sub-exponential decomposition of two crossing
wires some piece has (S_{12|34} + S_{14|23})/√2 + (1 − 1/√2)·S_{13|24} ≥ 2√2·λ − o(λ). The same with hyperplane cuts of
the n-cube gives FH. Prove it first for restricted piece classes (pieces that are isotypic for a global torus;
cancellation-free pieces), then in general.

**Why it might work.** It replaces "find a Zorn-lemma point" by one inequality about entropies of pieces, where strong
subadditivity, entanglement polytopes and uncertainty relations with memory are available; the third cut {13|24}
(weight 0.29) is new information that neither the paper nor Theorem 1 uses.

**Most likely failure.** Cancellation between pieces: no analytic inequality survives arbitrary signed sums, which is why
spectral points were needed in the first place. One then gets theorems only for restricted classes.

**First experiment (< 2 h).** On the pieces Ψ_N from Idea 1 step 1 compute all three cut ranks (including {a,c|b,d}) and
the value Σ θ_S log rk_S. Outcome: constant in N and equal to the total ⇒ the Fock family is exactly extremal for
this functional, which fixes θ as the right dual object (go and prove the inequality for torus-isotypic pieces).
Pieces with slack ⇒ the slack pieces say where a better cover could gain: feed into Idea 1 step 3.

## Idea 5 (constructive, engine value; contracting if the floor is beaten). Three-flavour Howe determinant

**Idea.** Read the crossing determinant as skew Howe duality on Λ(ℂ^levels ⊗ ℂ^parties): a rotation in the *party*
index, pieces = weight spaces of the rotated torus. Two merges use one grading (N, Θ−N). For p = 3 merges that are
"orthogonal" (K4 with its three pair-partitions = alternate vertices of a cube; Δ3 with rows, columns, diagonals) use
a homogeneous determinant in X1, X2, X3 whose coefficient of X^N has rank ≤ P(N_k) across merge k. That would give
pieces with r_1² + r_2² + r_3² = const, i.e. the flat floor ρ = 1/√3 of b2 Theorem 3.

**Why it might work.** The flat floor is "Pythagoras in p dimensions" and the Fock mechanism is a rotation; SO(3) acts
on three flavours as SO(2) acts on two. Majdoddin-type and ALS searches at N₀ = 2 cannot see it, since it is asymptotic.

**Most likely failure.** Three cuts need three commuting gradings with complementary rank control; for two cuts the
complement is automatic (N′ = Θ − N), for three it is a new condition and may be impossible (then p = 3 costs more than
the flat floor, itself a statement worth knowing).

**Value.** Reaching 1/√3 gives the engine α′ = log₂√3 ≈ 0.79 instead of 1/2, unconditionally. Going *below* 1/√3 proves
C (b2). It does not decide the dichotomy otherwise.

**First experiment (< 2 h).** Smallest case, one particle–hole pair per wire, levels < R ≤ 4, K4 with wires on the two
"body diagonals" of each coordinate direction: write the 3-variable matrix by analogy with B.3 (same B, C kernels in
y_k = X_k²), check the X = (1,1,1) specialisation, and compute the three merge ranks of each coefficient.
Outcome: ranks follow P(N_k) ⇒ write up the p-merge identity; ranks blow up in one merge ⇒ record which, try the
Griffiths multivariate Meixner kernels once, then stop.

## Idea 6 (cheap audit, could be decisive). Test every known identity against the building, hubs included

**Idea.** ¬C implies ρ_μ, hence (plausibly) the whole Bruhat–Tits building of GL_{2μ}(F₂((t))), is a price space, so
*every* tensor identity anyone has (paper B.2; engine rectangle and Δ3 pieces; Majdoddin's rewrite-and-merge; the
2-adic D.1 decomposition; clause-product designs) must hold as an inequality there. c1 tested only B.3 and only with
hubs inside Mat_μ. A single violated instance proves C with no new mathematics.

**Why it might work.** Nobody designed those identities with a building in mind, and buildings have much more room than
Euclidean space only in specific directions (the 3π cone of §0).

**Most likely failure.** All known identities are consequences of B.3 plus routing, and B.3 holds in CAT(0) (c1's [C]).

**First experiment (< 2 h).** For each identity in the repo with ρ < 1, write its (★) inequality; maximise the violation
over placements of legs and hubs in Mat_3(F₂) (512 points, hill climbing as in `c1/code/cross_rank.py`) and in the
lattice classes of the building within distance 2 of L_0. Any positive violation ⇒ C (then verify exactly). None ⇒ a
table "identity × model: consistent", and a reason to prove B.3 for CAT(0) spaces, which would make c1's
undecidability statement unconditional.

## Idea 7 (wild). Geometry from recoupling: Ponzano–Regge for prices, and q-deformation for the building

**Idea.** The one place in mathematics where Euclidean 4-point geometry comes out of representation theory is the
asymptotics of 6j symbols: the overlap between the coupling schemes (12)(34) and (14)(23) is non-negligible exactly
when the six labels are the edges of a Euclidean tetrahedron (Cayley–Menger ≥ 0), and decays exponentially outside.
Our problem has the same shape: four parties, two crossing coupling schemes, six "lengths". Build 4-party functionals
from non-commuting Schur–Weyl projectors P^{12}_λ, P^{14}_μ (the recoupling overlaps of S_n / U(d)), and ask whether
their large-deviation zero set in entropy coordinates is the Euclidean cone. The deformation is then canonical:
quantum 6j symbols give spherical tetrahedra at roots of unity and hyperbolic ones at real q. Characteristic p with
Hecke parameter q = p would be the building (branching) geometry, so the two cases of the dichotomy would be
"q = 1" versus "q ≠ 1", and could depend on the field.

**Why it might work.** It explains at once why crossing-cut functionals fail to be multiplicative (the projectors do not
commute), why the correction is quadratic (Pythagoras), and why F₂-matrices appear.

**Most likely failure.** For the crossing state every Schur–Weyl sector is typical, so these projectors do not cut it
into Fock-like pieces; lengths in Ponzano–Regge are spins, not log-dimensions.

**First experiment (< 2 h).** n ≤ 5 copies, local dimension 2: build P^{12}_λ, P^{14}_μ on (ℂ²)^{⊗4n} from S_n class sums,
apply them to the crossing state and to the paper's smallest Ψ_N, and tabulate ‖P^{12}_λ P^{14}_μ ψ‖². Outcome: the
supports of the Ψ_N separate along a curve ⇒ pursue; all supports identical ⇒ kill.

---

## Ranking by P(decisive) × value

| # | Idea | Decides | P(decisive) | Cost of first step | Note |
|---|------|---------|-------------|--------------------|------|
| 1 | Dispersion engineering / calibrated profile search | C (via ¬PH) | ~6% | 2 h | failure mode yields the tight constraints for Idea 4 |
| 2 | Branching flats, M5 at μ = 2 | C (ρ_2 not a price) | ~5% | 2 h | gives the cleanest finite target and a geometric reformulation |
| 4 | Cover roof + entropic uncertainty | FH (square first) | ~3% | 1 h (rides on Idea 1 code) | partial theorems likely |
| 3 | Characteristic-2 ranks of the paper's pieces | C in char 2 | ~3% | 1 h (same code) | cheapest genuinely new data |
| 5 | Three-flavour Howe determinant | engine α′ 0.5 → 0.79; C only if floor beaten | ~12% for 1/√3, <1% for C | 2 h | high engine value |
| 6 | Audit of identities against the building | C | ~1–2% | 2 h | nearly free |
| 7 | Recoupling / q-deformation | either | <1% | 2 h | wild |

**Top two: Idea 1 and Idea 2.** One implementation of Prop. B.2 with exact rank computation serves Ideas 1, 3, 4 and 5,
so the efficient first day is: build that, run the char-p and three-cut tables (Ideas 3, 4), then the calibrated
profile search (Idea 1), with the M5 configuration (Idea 2) as the second target for the same search code.
