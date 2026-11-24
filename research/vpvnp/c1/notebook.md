# c1 notebook: deciding the flat/contracting dichotomy of "VP ≠ VNP over every field"

Source: paper.txt (pdftotext), Def. 2.1 / D.1, Thm 2.2 / D.2 (thm_alt), Prop. A.7–A.8, B.3, C.3, Lemma C.4.
Tags: [R] proved here, [K] known (cited), [N] computed, [C] conjecture.
Code: `code/` (all scripts are small; run with python3, numpy/scipy).

## Verdict (short)

Undecided over ℂ. What I got:

1. The dichotomy comes down to one explicit finite object per μ: the **rank metric**
   ρ_μ(a,b) = √rk(a−b) on Mat_μ(F₂). ¬Contracting ⇔ ρ_μ is a price for every μ ≥ 3 (§1).
2. ρ_μ is, up to the factor √2, a set of vertices of the Bruhat–Tits building of
   GL_{2μ}(F₂((t))). So it is CAT(0) and satisfies every curvature constraint the paper proves (§2).
3. The axioms the paper uses about prices (closure, random points A.8, crossing inequality B.3,
   CAT(0)) have a model where **both** hypotheses hold (Hilbert-space pseudometrics, §4), and,
   if [C] B.3 holds in all CAT(0) spaces, also a model where Flat holds and Contracting fails
   (CAT(0) pull-backs, which contain ρ_μ). So the paper's toolkit cannot decide the dichotomy
   or prove that the two cases exclude each other. New tensor identities are needed.
4. The explicit spectral points over ℂ (flattening ranks, quantum functionals, support functionals)
   give only "partition-star" pseudometrics. All of them satisfy the contracting inequality with
   D(μ)²/D(1)² < 8, which is < μ for μ ≥ 8. They cannot approximate ρ_μ, nor any Euclidean set with
   a non-degenerate rectangle (§3). So the known explicit points give no evidence either way.

## §1. The dichotomy is the single test "is ρ_μ a price?"  [R]

Definitions as in the paper: D(r)² = mean over a and over W of rank r of |a, a+W|².

**Proposition 1.** For μ ≥ 3 the following are equivalent:
(i) the contracting hypothesis fails at μ, i.e. for every s < √μ some price on Mat_μ(F₂) has D(μ) > s·D(1);
(ii) ρ_μ is a price on Mat_μ(F₂).
Also, if ρ_μ is a price then ρ_{μ'} is a price for all μ' ≤ μ.
Hence **Contracting ⇔ ∃ μ ≥ 3 such that ρ_μ is not a price**, and **¬Contracting ⇔ ρ_μ is a price for
all μ** (equivalently, for infinitely many μ).

*Proof.* (i)⇒(ii) is Steps 2–7 of the proof of Thm D.2, which produce a price with |a,a'|² = rk(a−a').
(ii)⇒(i): ρ_μ has D(r)² = r, so D(μ) = √μ·D(1) > s·D(1). Monotonicity: pull back along the block
embedding a ↦ diag(a, 0), which preserves rank differences. Contracting at μ = 2 alone also counts, but
failure at all μ ≥ 3 implies failure at μ = 2 by the same pull-back. ∎

So the paper's Step 8 (filling a cube) is the only place where flatness enters. The dichotomy is
the question of whether the one explicit non-Euclidean metric ρ_μ is realised by spectral points.

**Characterisation of exact prices (by covers of the complete network)** [R, routine from A.5/A.7].
For a pseudometric d on a finite V, let p_d(t) = inf Σ_j Π_{e} q_{j,e}^{d(e)} over covers of t by
graph tensors G_j = Π_e ⟨q_{j,e}⟩_e. Then d = d_φ for some spectral point φ iff, for
C = Π_{u<v} ⟨2⟩_{uv} (the complete network), lim_m p_d(C^m)^{1/m} = 2^{Σ_e d(e)}.
In other words: no family of tensor networks that is cheaper in d-length asymptotically covers the
complete network with bond dimension 2^m.
*Proof.* p_d is an upper functional (p_d(1) = 1 because every nonzero graph tensor costs ≥ 1).
Prop. A.5 gives φ ≤ p_d, so d_φ ≤ d. The triple trick of Prop. A.7 with C gives φ(C) = 2^{Σd},
which forces equality on every edge. The converse follows because φ is subadditive on covers. ∎
So "ρ_μ is a price over k" is a pure tensor-network statement about the complete network on the
2^{μ²} parties Mat_μ(F₂), with ρ-weighted bonds. This is the same kind of object as f_{k,ℓ}.

## §2. ρ_μ lives in a Euclidean building, so curvature cannot decide  [R]+[K]

Let K = F₂((t)), O = F₂[[t]], L₀ = O^{2μ}. For a ∈ Mat_μ(F₂) let L_a = tL₀ + O·{(x, ax) : x ∈ F₂^μ}.
**Claim.** The relative position of L_a and L_b is (1^r, 0^{2μ−2r}, (−1)^r) with r = rk(a−b). So in the
Bruhat–Tits building of GL_{2μ}(K) (or PGL), with its standard Euclidean metric,
d(L_a, L_b) = √(2·rk(a−b)) = √2·ρ_μ(a,b).
*Proof.* The shear (x,y) ↦ (x, y−ax) lies in GL_{2μ}(O). It fixes L₀ and tL₀ and sends L_b to L_{b−a}.
Block maps (g,h) ∈ GL_μ(O)² send L_c to L_{hcg⁻¹}, so we may take c = diag(I_r, 0). This splits as
r copies of the case μ = 1, c = 1 plus trivial blocks. For μ = 1 with basis g₁ = (1,1/t)·..., one checks
L₀ = ⟨g₂, t g₁⟩ and L₁ = ⟨g₁, t g₂⟩ (g₁ = f₁ + t⁻¹f₂, g₂ = f₁, f₁ = (1,0), f₂ = (0,t)), which is the
relative position (1,−1), of length √2. ∎
Euclidean buildings are complete CAT(0) spaces [K: Bruhat–Tits; BH99 II.10A].
**Consequences.**
- ρ_μ satisfies every inequality that holds in all CAT(0) spaces: Reshetnyak/Enflo, CN, flat
  rectangles, Lemma C.4 (a)–(f). The paper's remark D.3 ("not every price is Euclidean") is
  consistent with this. The geometry under ¬C is that of a building.
- Hence no argument that uses only "prices are CAT(0)" can prove the contracting hypothesis.
- Quick-check heuristic in the other direction: ρ_μ is not Hilbert-embeddable. See §4: every Hilbert
  pull-back has D(μ)²/D(1)² ≤ R_μ < 2, while ρ_μ has ratio μ.

## §3. Explicit spectral points over ℂ: what pseudometrics they give  [K]+[R]+[N]

- Flattening rank across S|S^c: d(u,v) = 1 if S separates u, v, else 0 (cut metric).
- Quantum functional F^θ [K: CVZ23], θ a probability vector on the parties. On a wire the
  marginals at u and v are uniform of entropy log q and the other marginals are trivial. So
  F^θ(⟨q⟩_{uv}) = q^{θ_u+θ_v} and d(u,v) = θ_u + θ_v for u ≠ v (a star metric). The same holds for
  Strassen's support functionals ζ^θ on wires, which are tight.
- Allowed operations: φ^a with 0 < a ≤ 1 (scaling), pull-back along maps of parties (merges parties
  into blocks), and limits. All of these are single-point operations. **The paper proves no closure of
  prices under sums or maxima**, and products of spectral points are not spectral in general (the
  cover axiom fails: Hölder goes the wrong way).
- So the explicit prices are exactly the **partition-star metrics** d(u,v) = (w_{[u]} + w_{[v]})·1[[u] ≠ [v]]
  with w ≥ 0, a closed cone. [R] They satisfy the four-point equality d(u,v)+d(x,y) = d(u,x)+d(v,y)
  for points in 4 distinct blocks. A Euclidean unit square has 1+1 ≠ √2+√2 between sides and diagonals,
  and ρ_μ contains such squares (0, W, W', W+W' with W, W' transversal of rank 1). So neither ρ_μ nor
  any Euclidean set containing a non-degenerate rectangle is a limit of explicit points, and **the
  flat hypothesis cannot be verified with known explicit points**.
- Contracting ratio of explicit points [R]: u ↦ w_u·e_{[u]} ∈ ℓ² gives squared distance
  w_u² + w_v² on different blocks. So d² is between 1 and 2 times a Hilbert squared distance, and
  D(μ)²/D(1)² ≤ 2R_μ < 4·2 = 8 (R_μ from §4; numerically 2R_μ ≤ 3.75 for μ ≤ 4).
  So all explicit points satisfy the contracting inequality for μ ≥ 8, and (by [N]) for μ ≥ 4.
  Cut metrics alone have ratio ≤ R_μ < 2. This gives no information about Zorn-lemma spectral points.

## §4. Mutual exclusivity: the paper's axioms have models of both outcomes

**Fourier bound** [R]. For f: Mat_μ(F₂) → Hilbert space, E_{a, rk W = r}‖f(a+W) − f(a)‖² =
4 Σ_B ‖f̂(B)‖² p_r(rk B), where p_r(j) = P_{rk W = r}(⟨B,W⟩ = 1) depends only on j = rk B. So
D(μ)²/D(1)² ≤ R_μ := max_j p_μ(j)/p_1(j).
- p_1(j) = (2^μ − 2^{μ−j})·2^{μ−1}/(2^μ−1)² ≥ p_1(1) > 1/4 and p_μ ≤ 1, so R_μ < 4 for all μ. [R]
- [N] (`code/fourier_ratio.py`, exact enumeration): R_2 = 1.5, R_3 = 1.75, R_4 = 1.875, attained at
  rk B = 1, where the ratio is (2^μ−1)/2^{μ−1} = 2 − 2^{1−μ}. [C] R_μ = 2 − 2^{1−μ} for all μ.
- So under Flat, pulling Euclidean prices back to Mat_μ(F₂) never contradicts Contracting.
  "Flat ⇒ ¬Contracting" would need prices that are not Euclidean, namely ρ_μ itself.

**The crossing inequality B.3 in model spaces.** B.3 is the only tensor-specific input to Sections C–D.
In normalised form, with A = p|xv| + q|yu|, S₁ = p|xo|+q|yo|+p|vo'|+q|uo'|, S₂ = p|xw|+q|uw|+q|yw'|+p|vw'|,
it reads (A−S₁)₊²/|oo'|² + (A−S₂)₊²/|ww'|² ≤ 2(p²+q²).
- [R] **B.3 holds in every Hilbert space.** Let e₁, e₂ be the unit vectors along x→v and y→u. Then
  |xv| ≤ |xo| + ⟨e₁, o'−o⟩ + |o'v| and |yu| ≤ |yo| + ⟨e₂, o'−o⟩ + |o'u|, so A − S₁ ≤ |pe₁+qe₂|·|oo'|.
  Routing x→w→w'→v and y→w'→w→u gives A − S₂ ≤ |pe₁−qe₂|·|ww'|. The parallelogram law finishes it.
  (Numerically sharp: sup = 0 in `code/cross_euclid.py`, d = 1, 2, 3.)
- [N] Metric trees, hubs over all vertices, 3000 random trees: sup = 0 (`code/cross_tree.py`).
- [N] ρ_2, ρ_3 with all 8 points (ends and hubs) in Mat_μ(F₂), hill-climbing (μ = 2: 100 restarts;
  μ = 3: 180 restarts × 512 moves): sup = 0, no violation (`code/cross_rank.py`).
- [N] Hyperbolic plane H² at scales 0.3–10, 600 Nelder–Mead restarts: sup = 1.3e−12, no violation (`code/cross_hyp.py`).
- [C] B.3 holds in every CAT(0) space. Heuristic: A−S₁ ≈ (p+q)|oo'| needs both geodesics to run along
  [o,o'] in the same direction, and A−S₂ ≈ (p+q)|ww'| needs them to run along [w,w'] in opposite
  directions. In CAT(0) two geodesics meet in a single segment (a convex set), so this cannot happen
  in both places at once.

**Models** [R, given the B.3 facts]. Let 𝓗 be the pull-backs of subsets of Hilbert spaces and their limits.
𝓗 is closed under pull-back, scaling and limits. It satisfies A.8 (put each new point at the
barycentre E σ(o); Jensen gives |E σ(o) − E σ(o')| ≤ E|σ(o)σ(o')|), it satisfies B.3 (proved above),
and it is CAT(0). In 𝓗, Flat holds and, by the Fourier bound, Contracting holds with s² = 2 < μ for any μ ≥ 3.
**So no argument that uses only the properties of prices the paper uses in Sections A–D can show
that the two cases are mutually exclusive.** Symmetrically, let 𝓒 be the CAT(0) pull-backs. 𝓒 satisfies
A.8 (barycentres in CAT(0) are 1-Lipschitz for W₁; Lemma C.4(c), [K: Sturm 2003]) and contains ρ_μ (§2),
so ¬C and Flat hold in 𝓒. Hence, *if* [C] B.3 holds in CAT(0), the same toolkit cannot prove
Contracting either. (Sections F–K use further facts, but only under the contracting hypothesis.)

## §5. What remains (exactly)

- Decide whether ρ_μ (μ ≥ 3) is a price over ℂ. By §1 this is equivalent to the tensor-network question:
  can the complete network on Mat_μ(F₂), with bond 2^m, be covered asymptotically by graph tensors
  of total ρ-cost 2^{m(Σρ − ε)}?
  - A **cheap cover** (some new tensor identity beyond the crossing identity and contraction) proves
    Contracting over that field, and with it the stronger bound 2^{c(log m)²/log log m}.
  - A **lower bound** against all covers proves ¬C, and so makes the flat-case bound for f_{k,ℓ} unconditional.
  - Natural candidate identities to test: ones that would exploit the F₂-linear structure, e.g. the
    "two decompositions of one rank-2 matrix" u₁x₁ᵀ+u₂x₂ᵀ = u₁(x₁+x₂)ᵀ + (u₁+u₂)x₂ᵀ (Step 5 of D.2),
    which gives branching flats (two flat squares on a common diagonal, which buildings allow).
- Prove [C] B.3 for CAT(0) (this would make §4's 𝓒 model unconditional).
- Explicit spectral points cannot help (§3), so any decision needs non-explicit (Zorn-lemma) points or
  new identities.

## Run log
- cross_euclid.py: d=1,2,3, 300 Nelder–Mead restarts each, best 1.4e−13 (equality, no violation).
- cross_rank.py μ=2 (100 restarts) best 0.0; μ=3 seeds 1–3 (60 restarts each) best 0.0.
- cross_tree.py 3000 trees, best 2.4e−11.
- cross_hyp.py: best 1.3e−12.
- fourier_ratio.py: R_2 = 1.5, R_3 = 1.75, R_4 = 1.875.

## Comic
`comic.svg` (4 panels, made at the lead's request).
