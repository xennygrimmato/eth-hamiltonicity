# dichotomy-attack: multi-party constraints against the filtration space

Theory notes with computations, 27 Nov 2026. Not committed, not machine-checked, not refereed.

Tags: **[K]** quoted, with location; **[R]** proved here in full from the cited inputs; **[D]** derived here,
unreviewed (or resting on an unreviewed input, named); **[N]** numerical (script named); **[C]** conjecture;
**[X]** dead, with reason.

Sources. K-AN = Anthropic's paper (`scratchpad/fm/paper.txt`), App. A–D read in full. K-EG = OpenAI, "Euclidean
geometry in the asymptotic spectrum of tensors" (`scratchpad/survey/oa/preprints/Euclidean-…/paper.txt`): §§1–6 read
(statements and the proofs of Prop. 5.2, Thm 5.3, Cor. 6.2), §11 statement only. K-MM = OpenAI, "The matrix
multiplication exponent is nine fourths": §7.4 (from (7.6) on), §8 read; statements of 2.1, 2.2, 4.1. K-HC: statements
only. Both labs' papers are machine-generated and unrefereed; every use is flagged. Ours: `q1-notes.md` (Theorem B
there is called **Thm B** below), `review-q1.md`, `hunch-triangle.md`, `ports/middle/notes.md`, `ports/hull/notes.md`
§2, `ports/literature-check.md` item 4.

Scripts (all in `research/sat3/dich/`, plain Python with numpy/scipy; outputs in the `.out` files next to them):
`label_lp.py`, `run_book.py` (label LP in the open book T₃ × ℝ), `filt_lp.py`, `run_filt3.py` (label LP in 𝒞₃(2)),
`gauss_chain.py` (closed forms and the scan of arm ratios), `mc_check.py` (Monte-Carlo check), `cutdom.py`,
`cutdom2.py` (label bound against cut domination), `hconfig.py` (H-configurations), `negtype.py` (negative type
of √rank).

---

## 0. Verdict

**No multi-party inequality is violated on the filtration space, and no realisation was found.** What is definite:

1. **The test of `hunch-triangle.md` Observation 3.1 is done, and it is a near miss, not a violation.** In a spectral
   space (K-EG sense) that contains the filtration space, the common-label rate of three tips of a pod with arms a
   is forced **strictly below the hub cost**:

       (8/3)·a = 2.6667a  ≤  D(tips)  ≤  3·exp(−t₃²/2)·a = 2.7342a  <  3a,      P(g > t₃) = 1/3.

   Left: OpenAI's tripod inequality (K-MM Prop. 8.1). Right: Theorem L below (flat law K-EG Thm 5.3 + submodularity
   K-EG Prop. 5.2, applied in pod × ℝ^M ⊂ 𝒞_{M+1}, M → ∞) [D]. So D/hp ∈ [0.8889, 0.9114]: the margin is **2.5 %**.
   Contact (D = D\*) is not decided; "label-flat" (D = hp) is excluded.
2. **Corollary [D].** If contracting fails in the OpenAI class over k (the hypothesis under which Thm B's proof gives
   spectral spaces in the K-EG sense, §1), then **ω_k ≥ 6/2.7342 = 2.1944**; more precisely R(⟨n,n,n⟩) ≥ n^{2.1944}
   for every n. Contrapositive: ω_k < 2.1944 ⇒ contracting (OpenAI class) ⇒ ports ⇒ (K-OA chain) power-saving 3-SAT in
   characteristic 0. This is consistent with ω ≤ 9/4 (K-MM Oct, re-derived by others per `hunch-triangle.md` §1.1).
   **A proof of contracting by this route needs the label bound 2.7342a pushed below 2.6667a**: that is the whole
   remaining distance, and nothing found here closes it (§4.5).
3. **Why the simpler tests cannot fail [R].** (a) With three sites, wire data and graph-tensor upper bounds never
   push D below hp, so the tripod inequality alone is never violated on any metric (Lemma 3.2). (b) Every constraint
   obtained from restrictions, degenerations and products only (no sum of terms of different shapes) holds on every
   ℓ₁-embeddable metric, with label rate "measure of the cuts splitting the set" (Lemma 3.1). The filtration space is
   **not** ℓ₁-embeddable and (Mat_μ(F₂), √rk) is not even of negative type for μ ≥ 3 ([N], `negtype.py`), which is
   exactly why the single-term tripod inequality has any bite there. (c) Convexity of prices with flat end
   configurations never gives less than hp on a triple (Lemma 3.3).
4. **`thm_alt_rank_price` constructs nothing (§5) [R].** K-AN D.2 Step 2 is a compactness limit. No multi-party
   quantity of the limit point can be read off; they are constrained only by inequalities valid at all spectral
   points. The numbers in item 1 are obtained that way.
5. **Realisation (§6).** Unconditional in characteristic 0: every finite tree metric (any number of branch points) is
   a price, by the laminar quantum functionals [K, VZ26 Thm 1.9, via the literature check; D for the metric]; their
   label rate is the Steiner length (D = hp on a tripod). This removes "trees with two branch points" from the open
   list of `sat3/notes.md` §4 and `q1-notes.md` Remark 3.4 in characteristic 0. Not realised: anything containing a
   flat square or a pod × segment. [R]: no spectral point that is a function of the flattening ranks of a tensor has
   a non-ℓ₁ wire metric, so stabiliser or graph states (whose data are cut ranks) cannot produce √rk by any
   "normalised entropy" formula. A realisation is equivalent to a lower bound for all asymptotic covers.
6. **(GE) (§7).** The filtration geometry does not decide (GE) and produces no port family. It strengthens the
   necessary condition for the middle cell from (GE) to (GE⁺): Poincaré against all 𝒞_N(2^s), i.e. against cones over
   spherical buildings of unbounded rank including interior points [R given Thm B].

Rechecks: the chain value was obtained three ways (closed form; LP with exact planar/3D mean widths in two different
models; Monte Carlo), and the absence of a violation was scanned over all arm ratios (§4.3).

---

## 1. Setting, classes, and what a violation would prove

**Two classes of spectral points.** AN-points (K-AN Def. A.1): multiplicative, subadditive on covers, not
normalised; prices are limits of c·d_φ. OA-points (K-EG §1–2): Strassen's spectrum (additive on direct sums,
normalised on the full diagonal); a *spectral space* is a metric space with prices H(T; x) of all placed tensors, a
positive multiple of log F_S on every finite set S of sites. OA spectral metrics are AN prices (`middle/notes.md`
§2.4). Write C_AN, C_OA for the contracting hypothesis in each class; C_AN ⇒ C_OA.

**Hypothesis H_spec.** "Every 𝒞_N(2^s) is (isometric to a subspace of) a spectral space over k in the K-EG sense."

- **¬C_OA ⇒ H_spec [D].** K-AN D.2 Steps 1–8 use only: compactness and scaling of prices, pull-backs, C.4(b), C.4(f).
  All are available in the OA class (K-EG §2.3 for limits, (4.5), §4.4). So ¬C_OA ⇒ √rk on Mat_μ(F₂) is OA-spectral
  for μ ≥ 3 (`middle/notes.md` §2.4 states the same). Thm B's Steps 0–6 use pull-backs, multiples, C.3 (K-EG Thm 4.3:
  embedding into a Hadamard spectral space with prices), C.4(a),(f): so every finite subset of 𝒞_N(2^s) lies in a
  Hadamard spectral space. An inverse limit over finite subsets (the spectral price systems on a finite set with
  given wire metric form a compact set, restriction to subsets is K-EG §2 "Normalization on subsets") gives one
  spectral space containing a countable dense subset, hence 𝒞_N. Not refereed.
- **AN class [C].** To get C_AN (and Theorem R) from a violation one needs the label calculus of §4 for AN prices.
  K-EG Prop. 5.2 transfers (restriction, degenerations of polynomial degree, tensor powers). K-EG Thm 5.3 uses joint
  convexity of all tensor prices (K-EG Prop. 3.3), which rests on exact extension (K-EG Thm 3.1); K-AN A.7 gives
  only "≤, with equality on one chosen tensor". An exact extension for cover-subadditive points (for instance for a
  Zorn-minimal point) is not written anywhere. Open.

**What a violation would give.** A valid inequality of spectral spaces that fails in some 𝒞_N(2^s) refutes H_spec,
hence proves C_OA over k, hence ports (K-EG §11.1.2–3 through `middle/notes.md` §2.4, [D, OA]) and OpenAI's 3-SAT
conclusion in characteristic 0. It proves C_AN only after the transfer above.

**Notation.** For a finite set S of sites, δ(S) is the price of the binary diagonal (common label) on S; δ({u,v}) =
d(u,v). For three sites at distances a_i + a_j: hp = a₁+a₂+a₃ (half perimeter), D\*(a) = Σa − 1/Σ(1/a). W(S) = mean
width of a finite subset of a Euclidean space, normalised so that a segment has its length; W(S) = √(2π)·E max_{s∈S}
⟨G,s⟩. T_k = k rays [0,∞) glued at 0 (infinite k-pod). T_k × ℝ^M (ℓ₂ product) is the "open book" with pages
H_i = ray i × ℝ^M, spine {0} × ℝ^M, flats F_ij = H_i ∪ H_j ≅ ℝ^{M+1}. For k ≤ q+1 it is a convex subset of
𝒞_{M+1}(q) (block sum of a line W with a fixed basis of a complement; `q1-notes.md` §3 "pod × ℝ^M") [R]. The tips of a
pod with arms a_i are the points (i, a_i, 0).

---

## 2. Constraints on prices that are not CAT(0) statements

"Class" says where the statement is proved: AN = every AN-point; OA = every spectral space of K-EG. "Type": **S** =
follows from single restrictions/degenerations and products (no sums of different shapes); **M** = uses a cover with
several terms of different shapes. Verdict = outcome on the filtration space 𝒞_N(2^s).

| # | Constraint | Source | Class | Type | Verdict on 𝒞_N |
|---|---|---|---|---|---|
| 1 | diam(S) ≤ δ(S) ≤ length of any tree on S through auxiliary sites | [K] K-AN Lemma A.2; K-EG (2.1) | AN, OA | S | consistent (defines the hub bound δ(tips) ≤ Σa) |
| 2 | A tensor of rank r across I₁ ∣ I₂ costs at most its legs' wires to two hubs plus log r·\|oo′\| | [K] K-AN Lemma A.3 | AN, OA | S | consistent; with #3 it is the only source of wire-only constraints |
| 3 | Crossing identity and inequality: r² + r′² ≤ 2(p² + q²) ("circle law"); shifted form 2^{n√(S±δ)} | [K] K-AN Prop. B.2, B.3; K-EG Thm 4.1 | AN, OA | **M** | holds: B.3 is true in every CAT(0) space (Lemma S, `q1-notes.md` §7); sharp (K-EG Cor. 6.2) |
| 4 | Extension: new sites at random old positions, φ′(t) ≤ Π φ(π_i t)^{θ_i}; exact form and joint convexity of H(T; ·) along geodesics for **every** tensor | [K] K-AN Prop. A.7, A.8; K-EG Thm 3.1, Prop. 3.3 | AN (≤ form), OA (exact) | **M** | for wires: CAT(0), holds. For labels: used in #6; alone it gives nothing below hp on triples (Lemma 3.3) |
| 5 | Copying: δ(A∪B) + δ(A∩B) ≤ δ(A) + δ(B) for A∩B ≠ ∅; for a tensor carrying a label on I, a copy at z costs ≤ δ(I∪z) − δ(I) | [K] K-EG Prop. 5.2 (proof read) | OA; AN [D] | S | used in Theorem L |
| 6 | Flat law: δ(V) = W(V) for V in an isometric ℝ^D; hull invariance δ(V∪z) = δ(V) for z in the closed convex hull of V | [K] K-EG Thm 5.3 and the first step of its proof | OA | **M** | used in Theorem L; consistent on all configurations tried |
| 7 | Tripod inequality D ≥ D\*(a) for three sites; equivalently Σ x_i d_i ≤ ω(x)·δ with the rectangular exponents | [K] K-MM Prop. 8.1, §8.1 (upper bounds on rectangular rank) | OA; AN [D] (monotone) | S | **not violated; margin 2.5 %** at equal arms, > 0 for all arm ratios (§4.3) |
| 8 | Graph tensors: Σ_{ij} x_ij d_ij ≤ ρ(x)·δ(S), ρ(x) = asymptotic rank exponent; ρ ≥ maxcut; ρ(K_m) = m²/4 | [R] monotonicity; values [K, third-hand: Zhou via `why-nine-fourths.md` §15] | AN, OA | S | not violated: k tips need ρ(K_k) < k(k−1)/c_k, below the flattening bound for k ≥ 4 (§4.4) |
| 9 | Decoder inequality on H-configurations (pairs AB, CD′ at distance h, all cross distances L): ½(D_ABC + D_ABD′) + h/4 ≤ D₄(h) + εh for h/L < δ(ε)/2; with #7: D₄(h) ≥ L + (½ − ε)h | [K] K-MM Lemma 8.2, §8.2 | OA | **M** (two terms) | not violated: best bound found is D₄(h) ≤ L + h + o(h) (§4.4) |
| 10 | Four tips: D₄ ≤ (3/2)·(2ℓ) | [K] K-MM (7.8) | only for a "moving family" (K-MM §7 hypotheses) | M | not a constraint on prices in general; on 𝒞_N we get D₄ ≤ 1.593·(2ℓ) |
| 11 | Flattening ranks, quantum and support functionals as particular points | [K] K-AN A.1 example; CVZ; VZ26 | – | – | existence statements; give ℓ₁ wire metrics only (§6) |
| 12 | Sum bound H(ΣT_i) ≤ max H(T_i) + δ(S) log #terms | [K] K-EG (2.3); K-AN Def. A.1 | OA, AN | M | bookkeeping; no constraint by itself |
| 13 | Duality (inequality at all points ⇔ asymptotic cover) | [K] K-AN Thm A.6; Strassen | AN, OA | – | translates a realisation into a lower bound (§6) |
| 14 | Poincaré inequality on U_h(F₂); ports | [K] K-AN Thm F.6; K-EG Def. 11.1, Prop. 11.2 | conditional (contracting; largest flat) | – | the negation of the hypothesis under test; M2′ shows the graphs fail on Mat_μ |
| 15 | No-ports and ports worlds: K-HC Thm 7.1, 11.2; K-MM Lemma 4.1, Thm 2.2 (volume of list distinctness) | [K] statements | conditional on ports / no ports; 2.2 is a network-size bound, not a price inequality | – | not applicable as a test (see §8) |

Reading of the table. All unconditional constraints on *wire metrics alone* are consequences of #2+#3+#4, i.e. of
CAT(0); the filtration space is CAT(0), so nothing wire-only can fail. The constraints that see more than pairs are
#5–#9, all about common labels. They are tested in §4.

---

## 3. Three lemmas on what cannot fail

**Lemma 3.1 (single-term constraints do not see ℓ₁ metrics) [R].** Let d = Σ_S ν_S·δ_S be a nonnegative combination
of cut metrics on a finite set V. For a tensor t placed on V put Φ(t) = Σ_S ν_S·log₂ rk_S(t) (rk_S = flattening rank
across S ∣ V∖S). Then Φ is monotone under restriction and under degeneration, additive on tensor products,
Φ(⟨q⟩_{uv}) = d(u,v)·log q and Φ(⟨q⟩_P) = ν(cuts splitting P)·log q. Hence every inequality between prices that is
derived from finitely many restrictions, degenerations and products holds for (d, Φ). In particular #1, #2, #5, #7,
#8 hold, with D = ν(splitting) = hp on every triple.
*Proof.* Each rk_S is monotone, multiplicative and lower semicontinuous. A cut that splits a triple separates
exactly two of its pairs. ∎
Φ is not subadditive on sums (K-EG §1.1), so #3, #4, #6, #9 can fail: an ℓ₁ metric is excluded only by a cover whose
terms have different flattening profiles. The crossing identity is the only such identity in either paper that
is used unconditionally on wires.

**The filtration space is outside the range of Lemma 3.1.**
- [R given `ports/hull/notes.md` §2 and the Lean file `W5.lean`] T₃ × ℝ ⊂ 𝒞₂(2) contains the five-point set W5, which
  is not a nonnegative combination of cuts. (Direct argument: in a geodesic space with an ℓ₁ metric almost every
  cut is convex with convex complement; in the open book T₃ × ℝ such cuts are {height > c} and {r_i > c} only,
  which generate the ℓ₁-sum of the factors, not the ℓ₂-product.) [D]
- [N, `negtype.py`] (Mat_μ(F₂), √rk) is of negative type for μ = 2 and **not of negative type for μ = 3, 4** (the
  Walsh transform of a ↦ √rk(a) is +0.714 at characters of rank 2 for μ = 3; +28.7 and +4.15 at ranks 2, 4 for
  μ = 4). Negative type is necessary for ℓ₁. For μ = 4 even rk^{1/4} fails. (The five points Sub(F₂²), with
  d(0,V) = √2, are ℓ₁; W5 is a different five-point subset of the same book.)

So on 𝒞_N single-term constraints such as the tripod inequality are not automatic. This is the reason the test of
§4 is meaningful at all.

**Lemma 3.2 (three sites: no violation from wire data) [R].** At every spectral point and for any three sites,
D\*(a) ≤ δ ≤ hp, and no graph tensor G on the three sites and any auxiliary sites, at any positions in any metric,
gives an upper bound δ ≤ cost(G) with cost(G) < hp.
*Proof.* δ ≥ D\* is #7; δ ≤ hp is the subrank of the triangle (K-EG §5.1). If ⟨q⟩_P is an asymptotic restriction of
G = Π ⟨q^{x_e}⟩_e, every cut separating one site from the other two has capacity ≥ 1. By the locking theorem for three
terminals (Lovász, Cherkassky) there is a multiflow with f_uv + f_uw ≥ 1 at every terminal u; flow paths are at least
as long as the distance of their ends, so cost(G) ≥ Σ f_ij(a_i + a_j) ≥ Σ a_i. ∎
So the comparison "label rate against D\*" can only be decided with constraints that involve other sites *and* are of
type M. The flat law is such a constraint.

**Lemma 3.3 (convexity with flat ends gives nothing on triples) [R].** Let z₁, z₂, z₃ lie on geodesics [a_i, b_i] of a
CAT(0) spectral space and let μ be any coupling of the end choices with the right marginals (K-EG Prop. 3.3). If
every triple in the support of μ is flat or has two coinciding points, the resulting bound E_μ δ(x) is ≥ hp(z).
*Proof.* δ(x) = hp(x) on such triples, and each pairwise distance is convex along the two geodesics under any
coupling (K-EG Prop. 3.3 for the wire). ∎
The same holds for any larger label of which the triple is a part (dropping legs lowers the price).

---

## 4. The label calculus on the filtration space

### 4.1 Theorem L

**Theorem L [D; inputs K-EG Prop. 5.2, Thm 5.3].** Let X be a spectral space containing T_k × ℝ^M isometrically, and
let p_i = (i, a_i, 0), i = 1..k, be the tips of a pod with arms a_i. For every finite K in the spine with 0 ∈ conv K
and support function S = s_K(G) (G standard Gaussian in ℝ^M, g an independent standard Gaussian)

    δ(p₁,…,p_k) ≤ δ(K ∪ {p_i}) ≤ √(2π)·E[ S + Σ_i (a_i g − S)₊ ].                                      (4.1)

Consequently, with K a fine net of a sphere of radius R:

- M = 1 (book T_k × ℝ, K = {±H}): δ ≤ Σ_i √(H² + a_i²) − (k−2)H; for equal arms the minimum is **2a√(k−1)**;
- M → ∞, R√M = r: S → r, and δ ≤ √(2π)·min_r [ r + Σ_i E(a_i g − r)₊ ]; for equal arms this is
  **c_k·a, c_k = k·exp(−t_k²/2), P(g > t_k) = 1/k**.

*Proof.* A_j := K ∪ {p₁, p_j} lies in the flat F_{1j}, so δ(A_j) = W(A_j) (Thm 5.3). For j ≥ 3 the sets
A₂ ∪ … ∪ A_{j−1} and A_j meet in K ∪ {p₁} ≠ ∅, which lies in a flat. Submodularity (Prop. 5.2) gives

    δ(K ∪ {p_i}) ≤ Σ_{j=2}^{k} W(K ∪ p₁ ∪ p_j) − (k−2)·W(K ∪ p₁).

In F_{1j} with coordinates (u, y), p₁ = (a₁, 0), p_j = (−a_j, 0), K ⊂ {u = 0}: the support functions are
max(S, a₁g, −a_j g) = S + (a₁g − S)₊ + (−a_j g − S)₊ and max(S, a₁g) = S + (a₁g − S)₊ (S ≥ 0). Taking expectations
and using g ↦ −g gives (4.1). For M = 1, S = H|g′| and √(2π)E(a g − H|g′|)₊ = √(H²+a²) − H. For M → ∞, |G|/√M → 1 in
L¹. For equal arms the minimiser has k·P(ag > r) = 1 and the value is √(2π)·k·a·φ(t_k). The first inequality in
(4.1) is monotonicity. ∎

| k | 2a√(k−1) (M = 1) | M = 2 | M = 3 | M = 8 | c_k (M = ∞) | lower bound 4(k−1)/k if ρ(K_k) = k²/4 | Steiner |
|---|---|---|---|---|---|---|---|
| 3 | 2.8284 | 2.7894 | 2.7730 | 2.7496 | **2.7342** | **2.6667** (= 6/ω at ω = 9/4) | 3 |
| 4 | 3.4641 | 3.3472 | 3.2986 | 3.2305 | 3.1862 | 3.0000 | 4 |
| 5 | 4.0000 | 3.7904 | 3.7043 | 3.5852 | 3.5088 | 3.2000 | 5 |
| 8 | 5.2915 | 4.7772 | 4.5731 | 4.2984 | 4.1280 | 3.5000 | 8 |

(arms a = 1; [N] `gauss_chain.py`.)

**Under H_spec the theorem applies to the √rk pod**: three points of a projective line of F_{2^s}^N, as points "line
⟨v⟩ at level 1", are the tips of a pod with a = 1/√2 inside T_{q+1} × ℝ^{N−1} ⊂ 𝒞_N. In Mat_μ(F₂) (graphs, scale 1/√2)
this is the pod S_m of `hunch-triangle.md` §5.

### 4.2 Checks [N]

1. `label_lp.py`, `run_book.py`: LP over all subsets of a finite V₀ ⊂ T₃ × ℝ with unknowns δ(S) and constraints
   δ = 0 on singletons, monotone, submodular on intersecting sets (elemental form), flat law (exact planar mean
   width), hull invariance (exact convex hulls in the book). max δ(tips) = 3√(H²+1) − H for V₀ = tips ∪ {Q_±} at
   every H tried, minimum **2.828427 = 2√2** at H = 1/(2√2). Adding the centre, more spine points, off-spine points,
   outer tips, and 12 random sets of 7 auxiliary points (n ≤ 12) never lowers it: within T₃ × ℝ the chain is the
   best derivation the LP finds. With the tripod inequality imposed on all triples the system stays feasible, and
   min δ(tips) = 8/3.
2. `filt_lp.py`, `run_filt3.py`: the same LP with points given as filtrations of F₂³, distances from the formula of
   `q1-notes.md` §1, flatness by enumeration of the 28 bases, exact 3D mean widths (edge formula), sound hull
   closure. K = regular 8-gon in the wall x₁ = x₂ around the pod centre gives 2.7933·a (disk optimum 2.7894·a);
   hull invariance changes nothing; with the tripod inequality on: feasible, min = (8/3)a. 25 random sets of 7
   auxiliary points of 𝒞₃(2) (vertices of both types at random scales, two-step flags, wall points): best 2.843·a.
   Near the pod centre the four apartments (v₁, v₂, w) share the wall, so 𝒞₃ is locally the product book.
3. `mc_check.py`: Monte-Carlo mean widths of explicit point sets in ℝ⁴ and ℝ⁷ reproduce the closed form for M = 3, 6
   within sampling error (2.769 against 2.773; 2.763 against 2.755).

### 4.3 The tripod test (Observation 3.1), all arm ratios [N]

`gauss_chain.py` scans arms (a₁, a₂, a₃) on a grid of the simplex Σa = 3. The M = ∞ bound U(a) of Theorem L stays
above D\*(a) everywhere: min U/D\* = 1.0014 at the most degenerate grid point (0.05, 1.45, 1.5), and U/D\* → 1 only as
one arm → 0, where both tend to the wire. Equal arms: U − D\* = 0.0676a. One long arm (1, 1, b → ∞): U − b → 1.593,
D\* − b → 1.5. **No violation at any arm ratio.**

**Corollaries, all under H_spec [D].**
- (a) D/hp ≤ 0.9114 on every pod of the filtration space with equal arms: the label is strictly cheaper than three
  wires to the centre. The dichotomy of Observation 3.1 ("contact, or D > D\* and hubs gain") is not decided, but
  its "label-flat" end is excluded.
- (b) R(⟨n,n,n⟩) ≥ n^{6/2.7342} = n^{2.1944} over k for all n (the product costs 6a·log n, a rank-r decomposition
  supplies it from a label of r values on the three tips). From M = 1 alone: ω ≥ 3/√2 = 2.1213.
- (c) Hub floor on Δ₃ (`hunch-triangle.md` Prop. 2.3, last paragraph of §5): with D ≤ 1.3671·δ (δ = 2a) and κ = 4/3,
  max(δ, D/κ) ≤ 1.0254δ, so the pod price gives hub floor ≥ (2/3)/1.0254 = 0.650 on Δ₃ instead of 16/27 = 0.593,
  provided the hub triples sit in a book T₃ × ℝ^M with M large inside the price space (true in 𝒞_N).
- (d) The label rate is not a function of the wire metric of the sites: on {tips, centre} the laminar quantum
  functional (§6) has D = 3a, the filtration space forces D ≤ 2.7342a.

### 4.4 Other configurations

- **k tips against K_k.** A violation needs ρ(K_k) < k(k−1)/c_k: 2.194 (k = 3), 3.77 (k = 4), 5.70 (k = 5). For
  k ≥ 4 this is below the flattening bound ⌊k²/4⌋ = 4, 6. So only the triangle can be tight, and there the question
  is ω against 2.1944.
- **The diamond.** For Sub(F₂²) = {0, V, p₁, p₂, p₃} (hull = K₂(2)): δ ≤ 2 + 2 − (1 + 1/√2) = 3 − 1/√2 = 2.2929 by one
  submodular step on two unit squares meeting in a half square; hull invariance gives the same bound for every
  finite subset of K₂(2). For q+1 tips: 2 + (q−1)(1 − 1/√2). No lower bound comes close (the three tips need 1.886).
- **H-configurations and the decoder inequality (#9).** In T₄ × ℝ^M take A, B = (1, h/2, 0), (2, h/2, 0) and
  C, D′ = (3, h/2, m e₁), (4, h/2, m e₁): within-pair distance h, all cross distances L = √(h² + m²). Formula (4.1)
  holds verbatim for tips over several spine points y_t, with (a g + ⟨G, y_t⟩ − S)₊ in place of (a g − S)₊. With
  K = segment [lo, hi]·e₁ + (ball of Gaussian radius r) and all three parameters optimised [N, `hconfig.py`]:
  (δ₄ − L)/h ≤ 0.945, 0.973, 0.987, 0.995 at h/L = 0.2, 0.1, 0.05, 0.02; the optimum tends to K = [0, m e₁], r = 0
  and the slope to 1. Flats and trees also have L + h. #9 needs δ₄ ≥ L + (½ − ε)h as h/L → 0: **not violated; the
  slope found is 1, the threshold ½.** K-MM obtains slope ½ (contact) only on a "moving family" through (7.8).
- **Cut domination [N, `cutdom.py`, `cutdom2.py`].** For random Z ⊂ T₃ × ℝ (n = 5..7, 200 samples) compare the LP
  bound U(Z) on δ(Z) with c(Z) = max_x Σ x_ij d_ij / maxcut(x) (= least total weight of cuts dominating d). U < c
  would be a violation if ρ(x\*) = maxcut(x\*) for the maximiser. U/c < 0.999 occurred in 15 samples (least 0.943, the
  optimal K = Q_± configuration), and **in every one x\* is a single triangle on three pages**, where ρ = ω and the
  needed bound is again ω < 2.12…2.19. No other graph tensor comes within reach.
- **Twelve hubs of X₄, Fano points.** All pairwise distances are √2; m such points need δ ≥ √2·2(m−1)/m if
  ρ(K_m) = m²/4. Independent points are flat (regular simplex, W grows like √(2π ln m)·… ), collinear triples are
  pods. Chain bounds: 7 Fano points ≤ 2.12 + 4·0.52 = 4.2 against 2.42; nothing near a violation.

### 4.5 Where it resists

The bound 2.7342a uses two flats at a time (submodularity) and the flat law. The LP of §4.2 finds nothing better in
T₃ × ℝ with all subsets of up to 12 points, and nothing better in 𝒞₃(2) with the points tried. Three reasons it is
hard to improve:

1. Two distinct apartments meet in at most a half-apartment, so the common part I of the two flats lies on one side
   of a wall at distance a from the third tip; (4.1) is then the exact value of W(I∪p₁∪p₂) + W(I∪p₃) − W(I), and
   among convex I the Gaussian ball (constant support function) is optimal by Jensen: r ↦ r + Σ E(a_i g − r)₊ is
   convex [R].
2. A non-flat spine (the pod centre of a 0/1 pod is a cone point of 𝒞_{N−2}) does not help in any derivation tried:
   increments are always computed relative to a flat subset, and the non-flat set costs at least its largest flat
   part [C that this is general].
3. Convexity (#4) cannot help on triples (Lemma 3.3).

What is missing for a decision in either direction: either a derivation with more than two flats at once that the
small LPs do not reach (M ≥ 3 with a singular spine has not been searched: it needs mean widths in dimension ≥ 4), or
a consistent label law on T₃ × ℝ^∞ (monotone, submodular on intersecting sets, hull invariant, mean width on flats)
with value ≥ (8/3)a on tips, which would show that the constraints #5–#7 cannot refute H_spec on books. The LP
optima are such laws on finite V₀ only.

---

## 5. What `thm_alt_rank_price` constructs

[R, from K-AN D.2 as printed.] Step 1 averages C.4(b) over quadrilaterals. Step 2: "for every s < √μ there is a
price with D(μ) > sD(1); scale to D(1) = 1 and pass to a limit by compactness". Steps 3–7 are rigidity: equality in a
mean of inequalities forces |a,a′|² = rk(a−a′). Step 8 fills cubes. No tensor, no spectral point and no rate appears;
the price is a limit of c_n·d_{φ_n} along an unspecified sequence, possibly with c_n → ∞.

Consequences.
- Multi-party values of "the" rank price are not defined by the theorem. After passing to a subsequence, limits
  H(T) = lim c_n log φ_n(T) exist for all placed tensors (they are bounded by network costs). The limit system is
  monotone and additive on products, and it respects every asymptotic cover with 2^{o(N)} terms (apply the cover at
  fixed n, divide by N, then let n → ∞). It need not satisfy the two-term sum bound #12 if c_n → ∞. In the OA
  class the normalisation is intrinsic (δ(S)·log F_S) and this issue does not arise.
- Therefore the only way to "compute" δ on tips of the √rk pod is the one used in §4: bounds valid at every
  spectral point of a space containing the configuration. Result: δ(three tips) ∈ [(8/3)a, 2.7342a] in the OA class.
- No quantitative form (dependence of λ₀ on g in `q1-notes.md` §4.1) can come out of D.2; unchanged.

---

## 6. Realisation

**6.1 What is realised unconditionally.**
- Cut pseudometrics (flattening ranks), every field [K, K-AN A.1].
- **All finite tree metrics, characteristic 0 [K + D].** For a laminar (pairwise non-crossing) family ℬ of
  bipartitions of the party set and weights θ, the upper quantum functional F^θ is a point of Strassen's spectrum of
  complex tensors [K: Vrana–Zuiddam arXiv:2611.34664 Thm 1.9, and BCFLN arXiv:2604.18283, as recorded in
  `ports/literature-check.md` item 4; I did not open them]. On a wire the maximally entangled state maximises all
  cut entropies at once, so d(u,v) = Σ_b θ_b·[b separates u, v]; laminar families of splits are exactly trees with
  the parties at their nodes. Likewise δ(P) = Σ_b θ_b·[b splits P] = length of the subtree spanned by P [D]. So every
  finite tree metric, with any number of branch points and with parties at inner nodes, is an OA-spectral metric
  and an AN price over fields of characteristic 0 (prices depend only on the characteristic, K-EG Lemma 2.3), with
  label rate = Steiner length, i.e. D = hp on tripods (no contact). This settles in characteristic 0 the item "trees
  with two branch points" left open in `sat3/notes.md` §4 and `q1-notes.md` Remark 3.4, without any hypothesis; it
  gives no new floor by itself, because tree products, not trees, carry the floors there.
- Euclidean metrics: K-EG Thm 1.2 claims them over every field, by contradiction; K-AN gives them when contracting
  fails. No explicit point.

**6.2 What obstructs an explicit √rk [R].**
- Let φ be a spectral point of the form φ(t) = f((rk_S(t))_S) with f nondecreasing in every flattening rank. On
  graph tensors log φ is a function of the cut vector (cut_x(S))_S; it is additive (products add cut vectors) and
  nondecreasing, hence a positive linear functional on the cone of cut vectors, and by the M. Riesz extension
  theorem (the cut vector of the complete graph is strictly positive) it is Σ_S θ_S·cut(S) with θ ≥ 0. So
  d = Σ_S θ_S δ_S: an ℓ₁ metric. By §3, √rk on Mat_μ(F₂) is not ℓ₁ (not even of negative type for μ ≥ 3). The same
  argument applies to monotone functions of the entropies of the marginals across fixed cuts.
- **Stabiliser and graph states.** The cut-rank function S ↦ rk_{F₂} A[S, V∖S] of a graph state is one tensor seen
  across many cuts. A price is one functional evaluated on many tensors (the wires between pairs of sites). A family
  of tensors can certify relations between graph tensors, i.e. constraints on all prices; it cannot certify that a
  metric is a price. The coincidence "rank over F₂" in both objects does not connect them. [X as a route.]
- Also the rank metric itself (not its root) is not ℓ₁ for five points (K_{2,3} ⊂ Mat₂(F₂), `middle/notes.md` §3), so
  no formula "√(number of separating cuts of a family)" exists either.
- **Equivalent lower bound.** By duality (#13), a metric d on V is a price iff no asymptotic cover of a product of
  wires by graph tensors on V ∪ hubs is cheaper in d-cost. For d = √rk on Mat_μ(F₂) this is ¬Contracting at μ. So an
  explicit realisation is a universal lower bound for covers with terms of mixed shapes; the only tools that prove
  such bounds are spectral points, and the only explicit ones are those of 6.1. The smallest instance is unchanged
  from `ports/hull/notes.md` §2: "T₃ × ℝ is spectral ⇔ f\*(K_{2,3}) = 3/√10".
- A by-product: the upper quantum functionals with crossing support have wire metrics outside CAT(0) (the 4-cycle),
  so by K-AN B.3 / K-EG Thm 4.1 they are not spectral points [D; presumably known, cf. BCFLN "obstructions"].

**6.3 Candidates from D.2's groups [X].** U_h(F₂) and SL_h(F₂[s]/sⁿ) enter K-AN only in the contracting case, through
length functions on price spaces (F.1) and duality (G); they are sources of identities, not of spectral points.
Nothing in them produces a functional.

---

## 7. Ports and (GE)

(GE) as in `middle/notes.md` §1.1: some bounded-degree family has E_pairs δ ≤ γ·E_edges δ for all δ in the rank cone.

- **(GE⁺) [R given Thm B].** If contracting fails over k, an AN port family over k satisfies the Poincaré inequality
  for d² against every map into every 𝒞_N(2^s). Call this (GE⁺). (GE⁺) ⇒ (GE) (subspaces are points of 𝒞_N and
  τ² is the rank cone, `middle/notes.md` §1.2), and ¬(GE⁺) ⇒ (AN-ports ⇒ contracting). So the statement to refute
  became weaker: placements may now use interior points of the cones.
- **(GE) does not obviously imply (GE⁺) [D].** A point of K_N is a convex combination of the subspaces of its chain,
  and the random-threshold map θ ↦ F_θ turns d² into the ℓ₁ distance of level vectors on average: d² ≤ E_θ τ² when
  all level differences are ≤ 1, with equality only for 0/1 differences. On edges the inequality goes the wrong way.
  The rank cone contains no three collinear points (rank is a metric, so √rk has no midpoints), while 𝒞_N is
  geodesic; this is the whole difference.
- **Reduction to spherical buildings [K\*, not re-opened].** 𝒞_N = Cone(Δ) × ℝ; for Euclidean cones the Poincaré
  constant is controlled by that of the base with the metric min(d_Δ, π) and of ℝ (Mendel–Naor, Duke 2015, cone
  lemma). So (GE⁺) is a statement about the spherical buildings of GL_N(F_{2^s}), all N, with truncated angular
  metric, all points; (GE) is the same statement for vertices of one type with the chordal metric.
- **A placement that uses interior points, and gains nothing [D].** Complete flags with N equally spaced levels (gap
  η) map the chamber graph of the building into 𝒞_N with edges of length √2·η; a pair of flags in relative position
  w ∈ S_N is at distance η·(Σ_i (i − w(i))²)^{1/2}, i.e. η·N^{3/2}/√3 for opposite flags and ≈ η·N^{3/2}/√6 for a
  random w: ratio between N³/12 and N³/6. [C] This is presumably of the order of the inverse spectral gap of the
  chamber walk (adjacent-transposition type), i.e. what a Hilbert-space placement gives; and the chamber graph has
  degree (N−1)q. A bounded-degree graph with a spreading homomorphism into the chamber graph meets the obstruction of
  `middle/notes.md` §7.3 (few generators act on few coordinates).
- **Verdict.** The filtration geometry neither decides (GE) nor produces port families (ports is a statement about
  all prices; a space of prices can only refute it). Theorem M2's graphs fail already on vertices. New test
  placements exist only in irreducible higher-rank pieces; pods, flats and their ℓ₂-products are harmless for every
  expander (Izeki–Nayatani invariant 0, `middle/notes.md` §2.3).
- Unchanged: (GE) open; `middle/notes.md` §10 item 2 stays the next step there. Added: its strengthening (GE⁺) is
  the relevant statement when contracting fails.

---

## 8. Dead ends

- [X] Violating the tripod inequality with wire data and hubs only: Lemma 3.2.
- [X] Any constraint of type S against an ℓ₁ part of the space (trees, flats, their ℓ₁-like subsets): Lemma 3.1.
- [X] Convexity (K-EG Prop. 3.3) with flat or collided end configurations to bound a triple label: Lemma 3.3. The
  same for four tips moved to two collisions: every coupling returns c₄a ≤ c₄a + (positive).
- [X] K-MM (7.8) on the filtration space: it needs the harmonic star inequality (7.1) of a moving family, which is a
  hypothesis on a parametrised family of sites, not a property of spectral spaces. Its geometric input (H-trees
  with constant cross distance) does not exist in 𝒞_N (no tree with two branch points, `q1-notes.md` Remark 3.4);
  the H-configurations that do exist (two pairs of tips at different heights of T₄ × ℝ) have label slope 1.
- [X] "E max" models of a label law on the book (integrals of convex or Busemann-type functions over the boundary):
  singletons must have width 0, which forces the functions to be affine on every geodesic; on a tripod factor
  affine functions are constant. So no Crofton-type formula exists on T₃ × ℝ; consistent with non-ℓ₁.
- [X] K_k graph tensors for k ≥ 4, cycles, bipartite graphs as lower bounds for labels on pods: bipartite graphs give
  only δ ≥ diameter; K_k is protected by the flattening bound (§4.4).
- [X] List distinctness (K-MM Thm 2.2) and K-HC Thm 7.1 / 11.2, K-MM Lemma 4.1 as tests: 2.2 is a bound on network
  volume proved separately in the two worlds (ports / no ports); the others are theorems of the no-ports world.
  Since contracting ⇒ ports (Theorem A), "no ports" implies that the filtration space consists of prices; these
  theorems hold in a world where H_spec is expected, so they cannot refute it without an independent proof of
  ports.
- [X] W and GHZ states: the W tensor has border rank 2 and restricts to a wire on each pair, so it gives
  max d ≤ H(W) ≤ δ, weaker than #1.
- Not done: K-EG §§7–16 (the proof of Thm 1.2), K-MM §§9–11 (proof of the tripod principle; used as [K]); LPs in
  𝒞₄(2) and 𝒞₃(4) (need mean widths in dimension 4 and many more bases); the AN-class transfer of §1.

---

## 9. Best next steps

1. **Decide the 2.5 % window on the three-tip label** (the single place where a known inequality comes within reach
   of the filtration space). Two specs.
   - *Search for a better derivation.* LP of `filt_lp.py` in 𝒞₄(2) around a pod whose spine point is singular
     (the 0/1 pod: spine = cone point of 𝒞₂ × ℝ²), with points on several apartments through the cone point and a
     polygon/polytope K in each; needs exact mean widths in ℝ⁴ (use one fixed set of ≈ 10⁶ Gaussian directions for
     all sets, so that the numerical W is itself monotone and submodular) and column generation instead of all
     subsets. Decision value: any value below 2.7342a shows that non-product structure helps; below 2.6667a is a
     violation.
   - *Prove optimality.* Construct a label law on T_k × ℝ^M (set function on finite subsets: 0 on singletons,
     monotone, submodular on intersecting sets, hull invariant, mean width on flats) with value c_k^{(M)}·a on the
     tips. The LP optimal solutions (`label_lp.solve`, primal values) are such laws on finite V₀ and can be
     inspected for a pattern. This would show that #5–#7 cannot refute H_spec on books and move the question to
     the tensors behind K-MM §8.2.
2. **Transfer the label calculus to AN prices** (exact extension for cover-subadditive points; §1). Without it a
   violation proves C_OA, not C_AN, and reaches 3-SAT only through OpenAI's chain, not through Theorem R.
3. **Referee Theorem L and Lemma 3.1–3.3**, and the reading of K-EG Prop. 5.2 and Thm 5.3 they rest on (in
   particular: Prop. 5.2 for a union that is not flat; Thm 5.3 for a flat inside a larger non-flat spectral space).
4. If item 1 ends in "optimal": the next multi-party test is the decoder inequality #9 with tensors other than
   labels (K-MM U_N), priced on H-configurations of T₄ × ℝ^M by direct networks instead of through D₄.
5. (GE⁺) for one candidate family (random regular graphs): unchanged from `middle/notes.md` §10, with the target
   class enlarged as in §7.

---

## 10. Continuation (27 Nov, second pass): search beyond the product chain, a label law on books, the ω corollary

Scripts added in `dich/`: `gen_lp.py` (generic label LP), `tripod2.py` (T × T′), `tripod2R.py`, `tripod2R_small.py` (T × T′ × ℝ),
`booklaw.py`, `booklaw2.py`, `booklaw3.py`, `booklaw4.py`, `booklaw5.py` (the law of §10.2 and its tests).

**Summary.** (1) No derivation below 2.7342a was found; the best upper bound on the three-tip label is unchanged.
A singular (branching) spine gives exactly the flat-spine value in both models tried. (2) On the book T_k × ℝ there
is an explicit label law L with L(tips) equal to the chain value; it satisfies every label constraint of §2 in all
numerical tests, and all of them except submodularity are proved. So on books the label constraints cannot refute
the filtration space: **the pod route is closed there ([N] for M = 1, [C] for M ≥ 2)**. (3) The ω corollary is stated
on its own in §10.3.

### 10.1 Search for a better derivation [N]

- **T × T′ ⊂ 𝒞₄(2)** (`tripod2.py`; block sum of two lines; nine flats ℝ², exact planar mean widths, sound hull
  closure). The tips of T sit over the centre of T′, so the spine of the T-book is the tripod T′, singular at that
  point. K = two points of T′ at radius H\* (flat spine): 2.82843. K = the three tips of T′ at radius H: 2.8594,
  2.8321, **2.82843**, 2.8398 at H = 0.2, 0.3, H\*, 0.45. Adding the centre, a second radius, mixed points
  (i, r; k, t), or 16 random sets of 7 auxiliary points: never below 2.82843 (best random 2.82942). The third ray of
  the spine neither helps nor hurts.
- **T × T′ × ℝ ⊂ 𝒞₄(2)** (`tripod2R.py`, `tripod2R_small.py`; flats ℝ³, exact mean widths). The spine of the T-book
  is the book T′ × ℝ. K = {(centre, ±R)} ∪ {points at radius R, 1, 2 or 3 angles, on each ray of T′ used}. With two
  rays of T′ (flat spine part) against all three rays (non-flat), at R = 0.22, 0.2747, 0.32:
  2.80611 / 2.80611, 2.79297 / 2.79297, 2.79193 / 2.79193 (one point per ray); 2.80262 / 2.80262, 2.79132 / 2.79132,
  2.79193 / 2.79193 (two points per ray). **Identical to five digits in all six comparisons.** The flat octagon
  (three points per ray, two rays) gives 2.78993 at R = 0.2747 (disk optimum 2.78943); its three-ray version
  (n = 14, all 16383 subsets) was started and stopped unfinished after 12 minutes, so `tripod2R.out` holds only
  the first line.
- **Other apartments through the tips.** Three collinear points lie in no common flat; two tips p_i, p_j lie in the
  apartments of all bases (v_i, v_j, f). Two such apartments with different f meet in a half-apartment bounded by a
  wall x_f = x_{v}, which contains both tips; they are the same flat as far as the pair is concerned. A two-flat
  step δ(B₁ ∪ B₂) ≤ W(B₁) + W(B₂) − W(B₁ ∩ B₂) with p_i, p_j ∈ B₁, p_l ∈ B₂ needs B₁ ∩ B₂ inside the intersection of an
  apartment through v_i, v_j with one through v_l; this is at most a half-apartment bounded by the wall x_{v_i} =
  x_{v_j}, at distance a from p_l, whichever complements f are used. Choosing different complements in B₁ and B₂
  only shrinks B₁ ∩ B₂. So extra apartments enter only through steps whose intersection is not flat, and for those
  only lower bounds by flat parts (or by the tripod inequality) are available. The LPs contain all such steps
  automatically: `run_filt3.py` (random auxiliary points on all 28 apartments of 𝒞₃(2)) and `tripod2.py` found
  nothing.
- **Not done:** 𝒞₃(4) and a full 𝒞₄(2) (840 bases) LP. With the law of §10.2 the expected outcome on every
  book-like neighbourhood is "no gain"; the only places not covered by a law are neighbourhoods that are not books
  (three pairwise opposite directions at a cone point of rank ≥ 3), where two flats through pairs of tips meet in
  small sectors and the two-flat bound is weaker than on a book, not stronger.

**Best upper bound found: still 2.7342a. No value below 2.7342a, hence none below 2.6667a.**

### 10.2 A label law on the book

Setting: B = T_k × ℝ^M, pages H_i, spine Σ = {0} × ℝ^M. For a finite S ⊂ B let S_i be its points in the open page i,
and X(S) = (S ∩ Σ) ∪ {spine crossings of the segments between points of S on different pages}. A compact convex
K ⊂ Σ is *admissible* for S if K ⊇ X(S) (K = ∅ is allowed iff X(S) = ∅). Put

    Θ(S; K) = Σ_i W(conv(S_i ∪ K)) − (k−1)·W(K),            L(S) = inf { Θ(S; K) : K admissible for S }.

**Proposition O.**
1. [R] For admissible K, C = ∪_i conv(S_i ∪ K) is the closed convex hull of S ∪ K, C ∩ Σ = K, and Θ(S; K) is the
   first intrinsic volume of C by inclusion–exclusion over the pages (all multiple intersections are K, and
   Σ_{j≥2} (−1)^j C(k,j) = k − 1). In Gaussian form, with s = s_K(G), h_i and β_i the suprema over S_i ∪ K of
   g·r + ⟨G,y⟩ and −g·r + ⟨G,y⟩ (g ≥ 0):  Θ = √(2π)·E[ s + ½ Σ_i (h_i − s) + ½ Σ_i (β_i − s) ]. For convex C at
   most one page has β_i > s in a given direction, and then h_j = s on all other pages, so this equals
   √(2π)·E[ m + ½ Σ_i (h_i − m)₊ ], m = max_i β_i [N: the two formulas agree to 6·10⁻⁹, `booklaw2.py`].
2. [R] L is 0 on singletons; **monotone** (an admissible K for S′ ⊇ S is admissible for S, and Θ(·; K) is monotone);
   **hull invariant** (for z ∈ hull S ⊂ C: K stays admissible and conv((S ∪ z)_i ∪ K) = conv(S_i ∪ K)); equal to the
   **mean width on flat sets** (≤: K = conv X(S); ≥: Θ ≥ W(conv(S_i ∪ K) ∪ conv(S_j ∪ K)) ≥ W(S) by the valuation
   property of W on the convex union in F_ij, the other pages contributing ≥ 0).
3. [R] For tips with arms a_i: Θ(tips; K) = √(2π)·E[ S + Σ_i (a_i g − S)₊ ], the chain value (4.1). Hence
   L(tips) = c_k^{(M)}·a for equal arms (the ball is optimal: Θ is convex under Minkowski averaging of K over
   rotations), and **L(tips) ≥ c_k·a = 2.7342a (k = 3) for every M** (Jensen, as in §4.5).
4. **Submodularity on intersecting sets: [N] for M = 1, [C] in general.** `booklaw4.py`: L computed by convex
   minimisation over the spine interval for all subsets of 15 random point sets (k = 3, 4, 5; n = 6, 7), all
   elemental inequalities L(S+x) + L(S+y) ≥ L(S+x+y) + L(S): largest violation 8·10⁻¹³ (optimiser tolerance).
   Monotone, flat and hull constraints: ≤ 4·10⁻¹². L never exceeds the LP maximum of `label_lp.py`, and equals it
   on the tips (2√2 for k = 3, 2√3 for k = 4).
5. [N, `booklaw5.py`] L satisfies the tripod inequality on 400 random triples with one point on each of three
   pages (min L/D\* = 1.0047), and on the H-configurations of §4.4 it has slope 0.951, 0.975, 0.988 at
   h/L = 0.2, 0.1, 0.05 (threshold ½ of #9).

So for M = 1 the function L satisfies #1, #5, #6, #7 and the consequence of #9 on every configuration tested, with
L(three tips) = 2√2·a. A set function with these properties is all that an LP "max δ(tips)" can see; therefore no
derivation from #5–#7 inside T_k × ℝ gives less than 2√2·a, and (if item 4 holds for all M) none inside T_k × ℝ^M
gives less than c_k^{(M)}·a ≥ 2.7342a > (8/3)a.

**Where the construction is delicate (what a proof of item 4 must handle).**
- The un-enveloped function S ↦ V₁(hull S) is **not** submodular [N, `booklaw2.py`: violations up to 0.08]: V₁ is
  not monotone on convex subsets of a book (the tripod has 3a, the tripod with a spine segment less).
- The envelope over supersets inside a fixed finite V₀ can fail submodularity when V₀ has too few spine points
  [N, `booklaw3.py`: 0.029, k = 4, no spine point in V₀]. The infimum over the spine body K is needed.
- Proof obligation: for A ∩ B ≠ ∅ and admissible K_A, K_B find admissible K_∪ for A ∪ B with
  Θ(A∪B; K_∪) + Θ(A∩B; K_A ∩ K_B) ≤ Θ(A; K_A) + Θ(B; K_B). Equivalently: for convex spine-saturated C_A, C_B with a
  common point, V₁(hull(C_A ∪ C_B)) ≤ V₁(C_A) + V₁(C_B) − V₁(C_A ∩ C_B). In a flat this is the classical
  submodularity of the mean width. In the book the new crossings X(A ∪ B) ∖ (X(A) ∪ X(B)) enlarge the spine part of
  the join, and the term −(k−1)W(K) has the wrong sign for a termwise argument; a direction-by-direction proof must
  use the dichotomy of item 1 ("at most one page has β_i > s"). Not done.
- For M ≥ 2 nothing was computed (it needs hulls in books with 3-dimensional pages and a minimisation over convex
  bodies K); items 1–3 are proved for all M.

**What this closes, and what would be next.**
- Closed (M = 1 [N]; all M [C]): refuting H_spec by label rates of pod tips, of any finite set in a book, including
  W5 (it lies in T₃ × ℝ) and a node line with its hubs (a pod). For such sets only *wire-level* statements remain
  (W5: the K_{2,3} rate, `ports/hull/notes.md`), and those are CAT(0).
- X₄'s twelve hubs: every hub triple is flat or a pod, and any two generic nodes span a flat tetrahedron; the
  ambient space is 𝒞₄(2) near a non-book point. No law is known there, but the label lower bounds available (#7 on
  collinear triples, #8 with ρ(K_m) = m²/4) are the same as for one pod, while the upper bounds are weaker than on a
  book (§4.4: 4.2 against 2.42 for seven coplanar points). I see no reason to expect a violation there. [C]
- The constraints that the law does not address are those of type M on **non-label tensors**: the decoder family
  of K-MM §8.2 (U_N on H-configurations) and the polynomial-multiplication tensors of K-MM §§9–11. They need a
  pricing calculus for those tensors on books (an analogue of #5/#6 for a label carried together with a short
  wire), which neither paper supplies outside flats. This is the next test if the route is continued; the label
  route itself should be considered exhausted on books.

### 10.3 The ω corollary, standalone

**Statement [D].** Let k be a field. Suppose the contracting hypothesis fails over k *in the OpenAI class*: for every
μ ≥ 2 and every s with s² < μ there is a metric on Mat_μ(F₂) that is the wire metric of a spectral space over k in
the sense of K-EG §2 and has D(μ) > s·D(1) (notation of K-AN Def. D.1). Then for every n ≥ 2

    R_k(⟨n,n,n⟩) ≥ n^{6/c₃},     c₃ = 3·exp(−t²/2) = 2.73423,  P(g > t) = 1/3,     6/c₃ = 2.19440,

so ω_k ≥ 2.1944. Contrapositive: **an upper bound ω_k < 2.1944 over a field k proves the contracting hypothesis over
k in the OpenAI class**, hence ports over k (K-EG §11.1.2–3 with `middle/notes.md` §2.4) and, in characteristic 0,
OpenAI's power-saving 3-SAT conclusion (K-HC 13.1 → IM 7.1).

**Dependencies.**
1. The dichotomy argument K-AN D.2 Steps 1–8 run for OA spectral metrics (needs compactness, scaling, pull-backs,
   K-EG (4.5), §4.4) ⇒ √rk on Mat_μ(F₂), μ ≥ 3, is OA-spectral. [D; same remark in `middle/notes.md` §2.4]
2. Thm B of `q1-notes.md` run in the OA class (K-EG Thm 4.3 in place of K-AN C.3) ⇒ every finite subset of
   𝒞_N(2^s) lies in a Hadamard spectral space; inverse limit ⇒ 𝒞_N itself. [D]
3. T₃ × ℝ^{N−1} ⊂ 𝒞_N(2), isometric and convex. [R]
4. K-EG Thm 5.3 (mean width on flats) and K-EG Prop. 5.2 (submodularity on intersecting sets). [K, unrefereed]
5. Theorem L (§4.1) and the limit N → ∞. [D] For a fixed N the constant is 6/c₃^{(N−1)}: 2.1213, 2.1510, 2.1637,
   2.1821 for N = 2, 3, 4, 9.
6. Monotonicity: ⟨n,n,n⟩ on the three tips costs 6a·log n and is a restriction of a label with R values. [R]

Not used: the tripod inequality, any statement of K-MM, K-EG Thm 1.2 (existence of flats), ports, K-AN beyond the
proof pattern of D.2. The statement concerns the OpenAI class only; C_AN ⇒ C_OA, so "contracting fails in the OA
class" is the stronger hypothesis, and the contrapositive yields C_OA, not C_AN (§1).

**Consistency with ω = 9/4.** 9/4 > 2.1944, so the corollary is compatible with K-MM Thm 1.1 and with the upper bound
ω ≤ 9/4. In a world where K-MM's lower bound is accepted the corollary carries no information about ω; its
contrapositive is of interest only to a reader who doubts that lower bound.

**What would give 9/4.** The argument turns an upper bound D ≤ x·a on the three-tip label of the √rk pod into
ω ≥ 6/x. So "contracting fails (OA class) ⇒ ω ≥ 9/4" follows from D ≤ (8/3)a on that pod, which by the tripod
inequality D ≥ D\* = (8/3)a is exactly **contact, D = D\***, on the √rk pod. Contact there is sufficient, not
necessary: ω ≥ 9/4 only says that *some* spectral point attains the ratio 6a/D = 9/4 (K-MM Cor. 11.1), not that the
filtration pod does. Three cases for the true value D of the pod under H_spec:
- D = (8/3)a: contact; ¬C_OA ⇒ ω ≥ 9/4 by the two-page argument of `hunch-triangle.md` Observation 3.1.
- (8/3)a < D ≤ 2.7342a: consistent with everything known; the pod is not K-MM's extremal point.
- a derivation of D < (8/3)a from valid constraints: contradiction with ω ≤ 9/4, hence C_OA.
By §10.2 the label constraints #5–#7 on books cannot produce the third case and cannot decide between the first two.
