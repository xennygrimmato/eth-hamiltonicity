# Referee report: Newton-polygon / sparse-test separations (ideas-span.md §§1–3, 7; pc1/notebook.md §§2–3)

24 Nov 2026. Adversarial referee. I read in full: `ideas-span.md` (including the new §7), `pc1/notebook.md` (final
version), `review-pc.md`, and the L1 section of `y2/notebook.md`. I checked the arguments line by line. I re-ran the key
numerical claims with my own scripts (scratchpad `ref/chk1.py`–`chk4.py`):
- Ryser valuations, both weightings, n ≤ 8;
- the §7.3 barrier polynomial, built as an actual polynomial, n ≤ 4;
- the base-r gadget of Theorem G;
- random sanity tests of Theorem 2T;
- the char-2 span count.

I also searched the literature (§9).

## 0. Verdicts

| Claim | Verdict |
|---|---|
| Lemma S1 (slopes of a product = union) | CORRECT |
| Lemma S2 (≤ t−1 slopes for t-sparse) | CORRECT (holds for "≤ t powers of y", any coefficients) |
| Lemma S3 (Ryser valuations distinct, w_ij = n^i((j−i) mod n)) | CORRECT; pc1's weights (2^i off the diagonal, 0 on it) are simpler and better |
| Lemma S4 (σ injective, preserves y-sparsity) | CORRECT |
| Theorem S | CORRECT WITH FIXES (the hypothesis is placed on a syntactic object; fix below). Superseded by pc1's Theorem A. |
| pc1 Lemma A.1 (Descartes, 2τ−2) | CORRECT |
| pc1 Lemma A.2 / Theorem A (τ−1 per factor; T·m(τ−1) ≥ 2^n−1) | CORRECT. This is **the statement to publish** (with the small strengthening in §2.3). |
| Lemma R (non-archimedean Rolle on annuli, residue char 0) | CORRECT (statement needs g ≢ const and an algebraically closed complete field) |
| Theorem 2T | CORRECT WITH FIXES: the bound as written assumes non-negative exponents; edge cases P ≡ 0; the field must be fixed |
| Special case a^D − c·b^D, sl ≤ (t+1)(2t−1) | CORRECT |
| Theorem kT | UNVERIFIED SKETCH. Not refereed as a theorem; must not be stated as proved. |
| Theorem S′ | CORRECT WITH FIXES: the path bound ∏_ℓ s_ℓ needs strict layering, else it is ∏(s_ℓ+1) ≤ (1+s/Δ)^Δ. Its core is a known lemma of Hrubeš–Yehudayoff. |
| Theorem G | CORRECT (re-verified). For r = 2 it is a known construction (Hrubeš–Yehudayoff CCC 2021, Thm 5.1). |
| Depth-hierarchy ranges (2^{Ω(n/Δ)}; exponential to Δ = n^{1−ε}; superpolynomial for Δ = o(n/log n)) | CORRECT for T = 2^{o(n)} tests. The "method stops at Θ(n/log n)" claim is upgraded below to a true barrier for A_g itself (base-r version of §7). |
| Hierarchy for sets in P_ℂ (Z(Q_{2,n})) | CORRECT; the parenthetical caveat is unnecessary (radical argument) |
| Part C(i): Span false in char p | CORRECT (proof given for p = 2; general p needs one more line, supplied in §6) |
| Part C(ii): Span ⇒ Knapsack multiples hard (char 0) | CORRECT |
| §7 Prop. 7.1, Cor. 7.2, Thm 7.3 | CORRECT (re-verified). Thm 7.3 extends to multiset/Newton-polygon containment at the cost of one power. |
| §7 Thm 7.4(a), (b) | CORRECT (the size bound in (a) is loose: O(b + log n) suffices) |
| §7 Thm 7.4(c) (real-weight chambers) | PLAUSIBLE SKETCH, not verified |
| pc1 Theorem B (trace + few extra roots) | CORRECT |
| pc1 Cor. B1 | CORRECT |
| pc1 Theorem B′ (tight machines) | CORRECT WITH FIXES: condition (ii) depends on the representation of the numerators, and the "unambiguous ⇒ μ = 1" gloss is false when divisors vanish on branches |
| pc1 Theorem AB (mixed) | CORRECT (μ = 0 case is trivial but should be mentioned) |
| pc1 Prop. σ | CORRECT |
| pc1 "Theorem B cannot be re-proved tropically" | HEURISTIC, correct as a remark. The attached [C] is now *answered for one weight or polynomially many weights* by §7, *open for all weights at once*. "No valuation-only argument can prove Gap G" overstates it. |

No claim is BROKEN. Two items are unproved and must be labelled so: Theorem kT and 7.4(c).

## 1. The model (for the paper)

**Definition M (trees).** Fix an algebraically closed field k (ℂ unless stated). An algebraic computation tree on inputs
z = (x, y) ∈ k^{m+1}:
- has operations +, −, ×, ÷ and constants from k;
- has equality tests "v = 0?";
- tests every divisor ≠ 0 before dividing by it.

A time-T BSS machine on inputs of size m + 1 unrolls into such a tree. "Depth" counts operations and tests.

**Generic path (L1, refereed in review-pc.md).**
- Follow "= 0" at a test iff the tested rational function is identically 0.
- Let v_1, …, v_r (r ≤ T) be the tested values on this path that are not identically 0.
- Write v_i = a_i/b_i in the representation of y2 L1. Then b_i is (up to a constant) a product of the earlier a_j, j < i, because divisors are tested first.
- Put P := ∏_i a_i. Then L(P) ≤ 5T, and Z(P) is exactly the set of inputs that leave the generic path.
- The generic leaf rejects, so A_g ⊆ Z(P) for any A_g ⊊ k^{m+1} that is decided.

**Catching lemma (pc1 §1, checked).** Let y − ρ ∈ k[x, y] with ρ ∈ k[x] and Z(y − ρ) ⊆ A. Then there is an i such that:
- y − ρ divides a_i;
- y − ρ does not divide b_i (take the least i with (y − ρ) | a_i);
- hence (y − ρ) divides **every** F_i with v_i = F_i/G_i, F_i, G_i ∈ k[x, y].

*Proof of the last point.* a_i G_i = F_i b_i, and y − ρ is prime and does not divide b_i. ∎

This lemma is the right interface: a hypothesis on the tested *function* (any fraction representation), not on y2's syntactic numerators.

**Ryser family.**
- g_E = (−1)^{n+|E|} ∏_{i=1}^n ℓ_{i,E}, with ℓ_{i,E} = Σ_{j∈E} x_ij, for E ⊆ [n].
- g_∅ = 0. The g_E are pairwise distinct (unique factorisation).
- N_g = ∏_E (y − g_E) and A_g = Z(N_g) ∈ NP_k (Boolean witness e with e_i² = e_i).

## 2. Theorem S versus pc1 Theorem A

### 2.1 Attack points, one by one

**(i) val g_E.** Under σ: x_ij ↦ u_ij τ^{w_ij}, with u_ij independent indeterminates and K = completion of the algebraic closure of k(u)((τ)):
- σℓ_{i,E} = Σ_{j∈E} u_ij τ^{w_ij}.
- *Idea file's weights* (ρ_i a bijection). The exponents in row i are distinct. The minimal one is attained at a unique j, with coefficient u_ij ≠ 0. So v(σℓ_{i,E}) = min_{j∈E} w_ij exactly.
- *pc1's weights.* The minimum 2^i (for i ∉ E) is attained by all j ∈ E. The coefficient is Σ_{j∈E} u_ij, a nonzero sum of distinct indeterminates. So there is again no cancellation.
- The sign (−1)^{n+|E|} has valuation 0.
- E = ∅ gives the root 0, which carries no valuation and is excluded. Exactly 2^n − 1 roots are counted.

**(ii) Distinctness.**
- Idea-file weights: the base-n digits m_i(E) ∈ {0..n−1} are determined by the value, and i ∈ E iff m_i(E) = 0. Correct.
- pc1 weights: v(σg_E) = Σ_{i∉E} 2^i (rows indexed 1..n). The binary expansion determines [n] ∖ E. Correct.
- Re-verified n ≤ 8 for both (`chk1.py`). With pc1's weights the set is exactly the even integers in [0, 2^{n+1} − 2). This is the fact §7 exploits.

**(iii) Newton-polygon step.**
- σ maps the monomial x^α y^b to u^α τ^{w·α} y^b. Distinct (α, b) give distinct u^α y^b, so σ is injective on monomials and σf ≠ 0 for f ≠ 0. Nothing becomes zero.
- Write f = Σ_{j≤τ} A_j(x) y^{β_j} with A_j ≠ 0 and distinct β_j. Then σf = Σ_j σ(A_j) y^{β_j} with σ(A_j) ≠ 0.
- Collisions of monomials in y-degree only lower the count. "t monomials in (x, y)" gives "≤ t powers of y".
- The lower Newton polygon in y has ≤ (#y-powers − 1) edges of finite slope. The nonzero roots in K have valuations equal to minus these slopes. This is standard (Newton-polygon theorem over a complete algebraically closed valued field; e.g. Robert, *A Course in p-adic Analysis*, GTM 198, Ch. 6; Neukirch, *ANT* II.6).
- Root valuations are ≤ τ − 1 in number. Fine.

**(iv) Tests that do not involve y.** Their y-sparsity is 1 and they catch no nonzero branch. Constants are harmless.

**(iv′) Divisions.** Here Theorem S as written is defective. Its hypothesis is placed on "the product of the numerators and all denominators as in y2 Lemma 1". Those numerators are *syntactic* (ad ± bc, …). They are not determined by the tested functions, and they are generally not sparse even when every tested function is.

Example: v = f₁/f₂ + f₃/f₄ with all f sparse. The y2-numerator is f₁f₄ + f₂f₃, which is not a product of sparse polynomials.

The "In particular" sentence (hypotheses on the tests and divisors themselves) does not follow from the displayed hypothesis as stated. It does follow from the Catching lemma (§1). Fix: put the hypothesis on a fraction representation of each tested value, as below. Divisors need no separate hypothesis: they are tested first, so they are among the v_i.

**(v) Model statement.**
- The substitution is applied to polynomials, after L1. It never enters the machine, so "generic path under σ" is not needed.
- The theorem is a statement about the polynomials F_i. Correct as an argument once (iv′) is fixed.

### 2.2 Which statement to publish

pc1's Theorem A strictly contains Theorem S:
- same constant;
- y-sparsity instead of total sparsity;
- every characteristic;
- simpler weights.

Publish Theorem A in the following form. The strengthening, "any fraction representation", is free by the Catching lemma.

> **Theorem A (y-sparse tests).** Let k be algebraically closed. Call a polynomial *τ-sparse in y* if it has at most τ
> distinct powers of y, with arbitrary coefficients in k[x]. Let a tree (Definition M) decide A_g for the Ryser family.
> Suppose every tested value v_i on the generic path can be written as F_i/G_i with F_i a product of at most m polynomials
> (arbitrary multiplicities), each τ-sparse in y. Then the number T of such tests satisfies **T·m·(τ − 1) ≥ 2^n − 1**.
> More generally Σ_i Σ_{factors φ of F_i} (sp_y(φ) − 1) ≥ 2^n − 1.
>
> *Key lemma.* A nonzero f that is τ-sparse in y is divisible by y − g_E for at most τ − 1 nonempty E.
> (Proof: σ with w_ij = 2^i for j ≠ i, w_ii = 0; Newton polygon in y over K.)

Corollaries to state:
- deg_y ≤ Δ tests: T ≥ (2^n − 1)/Δ.
- Tests y^D − u(x)^D and lacunary tests of any degree.
- Multiplicative Knapsack ∏_i x_i^{e_i}, with weights 2^i on x_i: 2^n valuations including e = 0, bound 2^n.
- Additive Knapsack: the valuation method gives only n. Use Lemma A.1 instead: ≤ 2τ − 2 branches per factor over ℂ, by Descartes.

### 2.3 Lemma A.1 (Descartes), checked

The argument goes as follows:
- G = A_{j0}·∏ρ_k·∏(ρ_k − ρ_{k'}) is a nonzero complex polynomial, so it does not vanish identically on ℝ^m.
- At X⁰ with G(X⁰) ≠ 0, the ρ_k(X⁰) are distinct, nonzero and real, and φ = f(X⁰, ·) ≠ 0 with ≤ τ terms.
- Re φ and Im φ are real τ-nomials, both vanish at the real points, and one is nonzero.
- Descartes: ≤ τ − 1 positive and ≤ τ − 1 negative roots. Total ≤ 2τ − 2.

Correct.

Applicability: real families of pairwise distinct polynomials. Ryser and additive Knapsack both qualify.

Distinctness, realness and nonvanishing at X⁰ are achievable: they are a nonempty Zariski-open condition on the real points.

## 3. Lemma R and Theorem 2T

### 3.1 Lemma R

**Setting.** K is complete and algebraically closed, with residue characteristic 0. Example: the completion of the algebraic closure of k(u)((τ)), char k = 0, value group ℚ.

**Statement (corrected).** Let J ⊂ ℝ be an open interval and g ∈ K(y) non-constant with no pole of valuation in J. Then
#(Sl(g) ∩ J) ≤ #(Sl(g′) ∩ J) + 2.

**Proof, checked.**
- On the open annulus {v(y) ∈ J}, g is a Laurent series Σ g_k y^k (partial fractions). Its zeros there have valuations equal to the breakpoints in J of φ_g(θ) = min_k (v(g_k) + kθ). This is the Newton-polygon theorem for Laurent series on annuli: Robert GTM 198 Ch. 6; Fresnel–van der Put, *Rigid analytic geometry and its applications*, Ch. 2.
- Residue characteristic 0 gives v(k) = 0 for every integer k ≠ 0, so φ_{yg′} = min_{k≠0}(v(g_k) + kθ) and φ_g = min(φ_{yg′}, v(g_0)).
- φ_{yg′} − v(g_0) is concave, so {φ_{yg′} > v(g_0)} is an interval. It contributes at most its 2 endpoints.
- Elsewhere the breakpoints of φ_g are breakpoints of φ_{yg′}. These have the same θ-positions as those of φ_{g′}, since multiplying by y adds θ.

Correct.

**Failure in residue characteristic p.** In ℂ_p take g = Σ_{j=0}^{N} p^{−j} y^{p^j}.
- The points (p^j, −j) lie on the convex curve −log_p, so g has N distinct root valuations.
- yg′ = Σ_j y^{p^j} has all coefficients of valuation 0, so g′ has only the root valuation 0 (besides y = 0).

So the lemma fails without bound (N versus 1, already for N ≥ 4). The authors' parenthetical remark is right.

**Citation status.** I found no published statement of exactly this annulus lemma.
- In residue characteristic p, the failure of Rolle's property is classical (Robert; Ballantine–Shemanske, "Rolle's theorem fails in local fields", gauss.dartmouth.edu/~trs/research-papers/rolles.pdf).
- In residue characteristic 0 the lemma is an elementary consequence of standard Newton-polygon theory.

Present it with its proof as "a standard argument", citing Robert for the Newton polygon of Laurent series.

### 3.2 Theorem 2T

**Statement (corrected).** In K[y] as above (residue characteristic 0), let
Q = c·∏_{j≤m} f_j^{a_j} − c′·∏_{j≤m} h_j^{b_j} ≠ 0, with c, c′ ∈ K^×, integers a_j, b_j ≥ 0, and every f_j, h_j having at most t powers of y. Then
**sl(Q) ≤ 2m·t^{2m} + 4m(t − 1) + 1.**
- The bound is independent of the exponents.
- With arbitrary integer exponents, clear denominators first. The same proof gives sl ≤ 2m·t^{2m} + 7m(t − 1) + 2 (cut at Sl(f) ∪ Sl(h)).

**Checks.**
- *Field.* The coefficients may be anything in K. So, as in Theorem A, f_j, h_j may be "t-sparse in y" with arbitrary coefficients in k[x] *before* σ. The idea file restricts to t-sparse in (x, y) unnecessarily.
- *Cuts.* Cut ℝ at all of S_h := ∪_j Sl(h_j), at most m(t − 1) points, and not only at the actual pole valuations of g = A/B − 1. This also handles common roots of A and B:
  - on each open piece J, B has no zeros, so zeros(Q) ∩ J = zeros(g) ∩ J;
  - zeros of Q with valuation in S_h are paid by the "endpoints" term.
  
  With that reading the count is right.
- *Derivative.* g′ = (A/B)·P/Π with Π = ∏ f_j h_j and P = Σ_j a_j f_j′ ∏_{l≠j} f_l ∏ h − Σ_j b_j h_j′ ∏ f ∏_{l≠j} h_l. Correct.
  - Zeros of g′ lie among zeros of A·P, so Sl(g′) ⊆ Sl(P) ∪ ∪Sl(f_j).
  - P is a sum of 2m products of 2m polynomials with ≤ t powers of y each, so ≤ 2m·t^{2m} powers and sl(P) ≤ 2m·t^{2m} − 1.
- *Edge case P ≡ 0.* Then A/B is constant, Q = (const)·B, and sl(Q) ≤ m(t − 1). The statement must exclude it or cover it. The bound above covers it.
- *Count.* Σ_J [#(Sl(g′) ∩ J) + 2] + |S_h| ≤ [sl(P) + m(t − 1)] + 2[m(t − 1) + 1] + m(t − 1). Correct.
- *Numerical sanity.* Random two-term instances with t = 2, m ∈ {1, 2} and exponents ≤ 9 had at most 3 and 5 valuations respectively. No violation was found; the search is weak and the bounds are far from tight.

**Special case a^D − c·b^D, checked.**
- v(ζ) = v(c)/D for every D-th root ζ of c.
- In a − ζb, a leading-term cancellation in the coefficient of y^e needs a specific ζ, one per e with a_e b_e ≠ 0.
- So all but ≤ t factors share one Newton polygon with ≤ 2t − 1 slopes. Total ≤ (t + 1)(2t − 1).

**Machine corollary (correct form).** If every generic-path tested value has a fraction representation F_i/G_i with F_i of the 2T shape (m bases, t powers of y, any c, c′ ∈ k[x]), then T·(2m t^{2m} + 4m(t−1) + 1) ≥ 2^n − 1. This is exponential for fixed m and t ≤ 2^{cn} with c < 1/(2m).

**Theorem kT.** The iteration is plausible: it is a Khovanskii-style descent. However:
- the bookkeeping of poles and enlarged families is not written;
- the bound t^{(2km)^k} is not derived.

It must be labelled a conjecture or sketch, and the "Corollary (machines)" for k > 2 must not be stated as proved.

**Prior art: must be cited.** Koiran–Portier–Rojas, "Counting tropically degenerate valuations and p-adic approaches to the hardness of the permanent" (arXiv:1309.0486):
- *Corollary 1.5.* For a sum of two products of powers of *binomials* (linear factors α + βx), the number of p-adic root valuations is ≤ m₁ + m₂, independent of the exponents, *under a tropical-genericity hypothesis* (the two products' Newton polygons share no vertex).
- *Lemma 1.18.* An O(k³mt) bound for SPS(k, m, t), again under tropical genericity.
- *Theorem 1.2 / 3.4.* Hypotheses on valuation counts of SPS polynomials imply permanent lower bounds.

Theorem 2T is the residue-characteristic-0 analogue: t-sparse factors, *no genericity hypothesis*, Rolle replacing genericity, and a worse (t^{2m}) bound. That is a genuine but modest addition. The paper must present it as such.

## 4. Theorem S′, Theorem G, and the depth hierarchy

### 4.1 Theorem S′

**Cancellation-freeness.** Non-negative real constants suffice.
- Every gate of σC is a polynomial in (u, τ, y) with positive real coefficients.
- Therefore supp(f + g) = supp f ∪ supp g and supp(fg) = supp f + supp g. No monomial can cancel, including leading-coefficient cancellations in u, since those are distinct monomials.
- The y-Newton polygon of σC_w is the lower hull of the projection of supp(σC_w) to the (τ-exponent, y-exponent) plane. Its Legendre function φ_w(θ) = min over the support of (k + bθ) is computed by the (min, +) circuit.
- No "generic η" is needed. Positivity in ℂ ⊂ K is the only requirement.

**Pieces bound.**
- Product gate: breakpoints are the union of the inputs' breakpoints; a power is one wire and keeps the breakpoints.
- Sum gate: on a linear piece ℓ of φ_i, the set {θ ∈ I : ℓ ≤ φ_l for all l} is an interval, because each ℓ − φ_l is convex.
- So p(min) ≤ Σ p(φ_i), and by induction p(output) ≤ #(input-to-output paths). Correct.
- This is the "monotone h.p.-formula" lemma of Hrubeš–Yehudayoff, *Shadows of Newton polytopes*, CCC 2021, Theorem 5.4: a monotone formula with high-powered inputs and k leaves has a bivariate Newton polygon with ≤ k vertices. Path counting is the same as unfolding the circuit into a formula. Cite it.

**Fix.** #paths ≤ ∏_ℓ s_ℓ holds only for strictly layered circuits, where inputs sit at layer 0 and wires join consecutive layers. If inputs or skip-wires may enter any layer, a path is an injective choice of "a wire or nothing" per layer, giving ≤ ∏_ℓ (s_ℓ + 1) ≤ (1 + s/Δ)^Δ.

**Corrected statement.**

> **Theorem S′.** Let C be a circuit over ℝ_{≥0} (gates: unbounded fan-in sums, and products with arbitrary non-negative
> integer powers on the wires) with Δ alternating layers and s wires, in inputs x, y and non-negative real constants.
> Then sl(σC) ≤ (1 + s/Δ)^Δ − 1, or (s/Δ)^Δ − 1 if strictly layered.
> If a tree (Definition M) decides A_g and every generic-path tested value is F_i/G_i with F_i computed by such a circuit
> (size ≤ s, depth ≤ Δ), then **T·(1 + s/Δ)^Δ ≥ 2^n − 1**, i.e. s ≥ Δ·(((2^n − 1)/T)^{1/Δ} − 1).

**Ranges (checked).** For T = 2^{o(n)}:
- size is 2^{Ω(n/Δ)}, i.e. 2^{n^{Ω(1)}} up to Δ = n^{1−ε};
- the bound is superpolynomial iff Δ = o(n/log n), given T = poly(n);
- polynomial size forces Δ = Ω(n/log n).

All correct. For T ≥ 2^n there is no bound, which is consistent.

### 4.2 Theorem G (re-derived and re-run)

**Mechanism.** The lines jδ + γ_j have breakpoints b_j equally spaced in (−ω, ω), decreasing in j.
- ψ_ev − ψ_od vanishes at each b_j. It is linear with slope ±1 on (b_j − ω/r, b_j + ω/r), and the signs alternate.
- Around each zero of δ_k, δ_{k+1} sweeps (−ω/r, ω/r) monotonically. So if the next level's breakpoints lie strictly inside (−ω/r, ω/r), each zero has r preimage zeros.
- The ratio ω′ = ω/(4r) in the file works. So does ω′ = ω/r: the extreme breakpoints ±ω′(r−1)/r are strictly inside.
- Size O(rL), depth 2L, y-degree r^L, so exactly r^L valuations.

**Re-run** (`chk2.py`, independent code): exactly r^L valuations for (r, L) = (2,4), (3,3), (4,2), (3,2), (5,2), with both ratios.

**New observation, needed for §5.** With ω′ = ω/r the root valuations form an *arithmetic progression* of r^L points (a balanced base-r expansion). I checked this exactly in all five cases: one common spacing (2/r^L, or 1/8 for (2,4), (4,2)).

**Prior art.** The r = 2 case, "a monotone bivariate polynomial of circuit size O(n) whose Newton polygon has 2^n vertices", is Hrubeš–Yehudayoff CCC 2021, Theorem 5.1 / Section 8. That construction resembles the classical univariate polynomials with circuit size s and 2^{Ω(s)} real roots. The idea file's §2 claim "decisive negative: an unbounded-degree τ-conjecture for Newton polygons is false" is therefore known. What is new is the depth/size trade-off (s/Δ)^{Θ(Δ)} and its use for A_g.

### 4.3 Hierarchy statement for sets in P_ℂ

- Z(Q_{2,n}) ⊂ ℂ² is decided by the single test Q_{2,n} = 0. That test is monotone, of depth 2n and size O(n), counting τ^{4^{n−k}} as one powered wire (or O(n) more gates by squaring).
- *Lower bound.* For a tree in the depth-Δ cancellation-free class, L1 gives rad(Q_{2,n}) | P. Each irreducible factor q of Q divides P, so Sl(Q) ⊆ Sl(P), working over ℂ((τ)) with τ an input (no σ needed).
- Hence T(1 + s/Δ)^Δ ≥ 2^n. The "generic constants" caveat in the file is unnecessary.
- The input dimension is fixed (2). The separation is in the parameter n; say so.

## 5. §7: the barrier (Prop. 7.1, Cor. 7.2, Thm 7.3, 7.4)

### 5.1 Proofs

**Prop. 7.1, checked.**
- δ_0 = pθ − η_0 and δ_{k+1} = ε_k − |δ_k|.
- By downward induction P_k is symmetric, equals {Σ_{l≥k} σ_l ε_l}, and |c| < ε_k for c ∈ P_{k+1} (superdecrease). This gives two preimages each.
- The slopes of δ_n are ±p ≠ 0, so every zero is a sign change and a breakpoint of min(g_n, h_n).
- Q ∈ K[y^p] has degree 2^n in y^p, and Q(0) ≠ 0 because G_k(0) ≠ 0 for k ≥ 1. So there are exactly 2^n valuations, each carried by p roots.

**Cor. 7.2, checked.** Σσ_k 2^{n−1−k} runs over the odd m with |m| ≤ 2^n − 1, which gives (2c/p)·{0, …, 2^n − 1}. The size claim is right.

**Thm 7.3, checked.**
- Under pc1's weights, v(σX_12) = w_12 = 2. With p = 2 and c = 2, Sl(σB) = {0, 2, …, 2^{n+1} − 2} ⊇ Sl(σN_g).
- I rebuilt B as an actual polynomial (u = 1, which is harmless since B has positive coefficients). Exact Newton polygons give exactly {2k : k < 2^n} for n = 1..4 (`chk1.py`).

**Thm 7.4(a), (b), checked.**
- (a): v(σg_E) = Σ_i min_{j∈E} w_ij is an integer in [0, Σ_i max_j w_ij]. With M = X_ij, w_ij = c > 0 and p = 2c, the slope set is {0, …, 2^L − 1}. The size is O(L + log c) = O(b + log n); the stated O(n(b + log n)) is a loose upper bound.
- (b) follows from S1.

**Thm 7.4(c)** (real-weight chambers via base-r gadgets with symmetric zero sets). The mechanism matches my §4.2 analysis: preimages of a symmetric set are translates. It is plausible, but the hierarchy conditions are not proved. Label it a sketch.

**"All weights at once" equivalence, checked.** With u indeterminates and B ∈ ℂ[x, y], Sl(σ_w B) = {θ : (w, θ) ∈ Trop(B)} for every real w. So "for all w" is literally Trop(B) ⊇ Trop(N_g) = ∪_E graph(h_E), not just generically. Trop(N_g) ⊆ Trop(M_n) also holds, by taking argmins.

### 5.2 Two strengthenings the authors should add

**(a) Multiset / full Newton-polygon containment.** For a weight with colliding valuations, a refined argument could use the full y-Newton polygon of σ_w P: NP(σ_w N_g) must be a Minkowski summand, i.e. each valuation must occur with multiplicity at least #{E : v(σ_w g_E) = θ} ≤ 2^n. This is still blocked: replace B_w by B_w^{2^n}, at n extra squarings.

**(b) Depth.** The base-r gadget with ratio r gives an arithmetic progression of r^L valuations (§4.2), at depth 2L and size O(rL).
- Take r = n and L = ⌈n/log n⌉.
- Shift and scale as in Cor. 7.2, with G_0 = y^p and H_0 a monomial in X_12.
- The result is a positive polynomial of size O(n²/log n) and depth O(n/log n) with Sl(σ_w B) ⊇ Sl(σ_w N_g).

So the lower-bound threshold Δ = Θ(n/log n) of S′ is a genuine barrier for A_g, not only for slope counting. The barrier is verified numerically for the AP property; the shift/scale step is routine.

### 5.3 The precise barrier statement (for the paper)

> **Barrier.** Fix q weight matrices w^{(1)}, …, w^{(q)} with non-negative integer entries of ≤ b bits (each row-sum
> bound positive). Call P ∈ ℂ[x, y] *w-saturated* if for every r the y-Newton polygon of σ_{w^{(r)}}P contains that of
> σ_{w^{(r)}}N_g as a Minkowski summand. Then there is a w-saturated polynomial B with non-negative integer coefficients
> and a monotone circuit of size O(q(n + b + log n)), and of depth O(n/log n) at size poly(n, b)·q, which is not a
> multiple of N_g.

**What it rules out.** Any proof that "every nonzero multiple of N_g has superpolynomial circuit size" which uses about the multiple only that it is w-saturated, for polynomially many integral weight vectors of polynomial bit size. This holds:
- whether the vectors are used one at a time or jointly through their slope sets;
- whether multiplicities are used or not;
- even against *monotone* circuits of depth Θ(n/log n).

Any such argument would equally lower-bound B.

**What it does not rule out.**
1. *Restricted test classes.* Theorems A/S, S′ and 2T are not contradicted. B has 2^n + 1 powers of y, so A does not apply. B has depth Θ(n/log n) or more, at the S′ threshold. As a two-term sum, B's inner polynomials are dense, so 2T does not apply. These theorems bound the slopes of the *tests*; B shows only that their restrictions cannot be dropped.
2. *All weights simultaneously.* The tropical containment Trop(P) ⊇ ∪_E graph(h_E) is open. It is Idea 7, the tropical cofactor problem.
3. *Residue data.* Arguments using the initial forms (leading coefficients of the roots under σ_w, which are monomials or sums of u's for N_g) are not covered. Using them amounts to working with the degenerate norm in_w(N_g), a border degeneration of the original problem (y2 §9(2)). It is not blocked, but it is not easier either.
4. *Coefficient or trace arguments* ([T26] via L3 / Theorem B).

## 6. Part C (§1.2)

**(i) Characteristic p.**
- M(w) = ∏_{v∈V}(w − v) has size O(n² log p) by the Moore recursion M_{k+1}(w) = M_k(w)^p − M_k(x_{k+1})^{p−1}M_k(w).
- Res_w(w^d − y, M(w)) = ±∏_{v∈V}(y − v^d) = ±det M(C_y). Its size is poly(n, d).
- p = 2, d = 2^k − 1: (e·x)^d = ∏_{a<k} Σ_i e_i x_i^{2^a}.
  - The monomials x_{i_0} x_{i_1}^2 ⋯ x_{i_{k−1}}^{2^{k−1}} are distinct for distinct tuples, because the binary digits of the exponent of x_i record {a : i_a = i}.
  - The coefficient of a monomial is e^S with S = {i_0, …, i_{k−1}}, and the functions e^S are independent on F_2^n.
  - So the dimension is Σ_{j=1}^k C(n, j). The count was re-run in `chk4.py`.
- *General p* (the missing line). Take d = p^k − 1, so (e·x)^d = ∏_a (Σ_i e_i x_i^{p^a})^{p−1}.
  - The multinomial coefficients are units mod p.
  - On F_p^n the coefficient functions reduce to ∏ e_i^{r_i} with 1 ≤ r_i ≤ p − 1, which are independent.
  - The choices with one index per digit already give ≥ Σ_{j≤k} C(n, j).

With k = log n, the span is n^{Θ(log n)} at cost poly(n). **CORRECT.**

**(ii) Characteristic 0.**
- det F(C_y), with C_y the companion of w^d − y, equals ∏_{λ^d = y} F(x, λ). Its roots include (e·x)^d, and its size is O(d³s).
- span{(e·x)^d : e ∈ {0,1}^n} has dimension #{S : 1 ≤ |S| ≤ min(d, n)}, since x^α has coefficient C(d, α)e^{supp α}.
- So Span with polynomial p implies that additive Knapsack has no poly-size multiple. Through L1 this gives P_ℂ(nu) ≠ NP_ℂ(nu) without [T26].

**CORRECT**, and it confirms review-pc's verdict that Span is a τ-type statement.

## 7. pc1 Theorems B, B1, B′, AB, σ

**Lemma B.1 (trace is border-easy), checked.**
- (−δ)^k Q(x, −1/δ) = Q_k ∏(1 + δρ)^{μ_ρ}.
- R/R₂ = 1 + δΣ(Q) + δ²(·).
- At a with Q_k(a) ≠ 0, R₂(a) is a unit of ℂ[[δ]], so Strassen division elimination applies. Use one homogenising variable λ, at O(d²) per gate; the multivariate truncation must be read this way, otherwise the cost is C(m+d, d).

**Lemma B.2 (one root at any multiplicity), checked.** This is Bürgisser's perturbation trick, re-checked in review-pc for y1.
- J = μU(a, y_0)ε^{μ−1} + O(ε^μ) ≠ 0 in characteristic 0.
- The chord iteration gains one z-order per step.
- The IFT for Θ is in (x, ε, Y): Θ(a, ε, y_0) ≡ 0 and ∂_YΘ = V(a, y_0) ≠ 0.
- Uniqueness of the Hensel lift identifies Y* with S(a + z, ε). Its coefficients lie in ℂ{ε}, and S(x, 0) = ρ(x).

**Theorem B and B1, checked.**
- Σ(Q) = Σ_E μ_E g_E + Σ_l e_l ρ_l. The left side has degree ≤ n and equals its truncation.
- The cost is O(n²(s + n²)) + h·O(n³(s + n²)). Exceptional branches cost O(n²) each.
- For μ ≥ 1, dividing by μ and applying [T26] gives B1. Correct.
- In B1's "in particular", roots of H that coincide with Ryser roots are among the h′ exceptions. Fine.

**Theorem B′: fix needed.**
- Condition (i) (false alarms) is semantic and correct: Z(P) is exactly the deviation set.
- Condition (ii) refers to the multiplicity of y − g_E in P = ∏ a_i, where a_i are y2's *syntactic* numerators. These multiplicities depend on the representation. ord_E(a_i) = ord_E(v_i) + ord_E(b_i), and b_i contains earlier divisor numerators.
- Counterexample to the gloss: test v, divide by it, then test (1/v)·v. y2's rule gives the representation (v, v). The second test's numerator a = v vanishes on every branch of v, although the tested value is 1 and vanishes nowhere. Every branch is "caught once, transversally", yet μ = 2.

Correct the gloss to:

> (ii) holds with μ = 1, h′ = 0 if no divisor vanishes identically on any Ryser branch (in particular for division-free
> trees) and each branch is a simple zero of exactly one tested value.

Alternatively, keep (ii) as an explicitly syntactic condition on P. Replacing P by the product of *reduced* numerators would make (ii) semantic, but it loses L(P) ≤ 5T. So it is not a fix.

**Theorem AB, checked.**
- A branch whose first catching test is in S divides a factor of that test's reduced numerator, so Lemma A.2 applies. Every other branch divides P_R.
- Branches with μ_E ≠ μ in P_R number ≤ h′ + Tm(τ − 1), each corrected at O(n²).
- If μ = 0, all but h′ branches are S-caught, so 2^n − 1 ≤ h′ + Tm(τ − 1). The inequality then holds trivially. Mention it.

**Prop. σ, checked.** Σ(Q) = per_n + Σ(H) when N_g is squarefree, so the bound follows from B.1.

**"Theorem B cannot be re-proved tropically."**
- As a remark it is fair: the slope set records which branches are present, never Σ_E μ_E g_E. And [T26] has no tropical shadow.
- Its conditional [C] ("if the gadget can contain {Σ_{i∉E}2^i}, then no valuation-only argument proves Gap G"): the hypothesis is now *true* (Thm 7.3, which is literally an arithmetic progression of even numbers). But the conclusion only follows for valuation arguments with one weight or polynomially many weights (§5.3).
- Rephrase it as "no argument based on the root valuations of poly(n) monomial substitutions can prove Gap G". Leave "all weights" open.

## 8. Corrected statements, ready for a paper

Use Definition M and the Catching lemma of §1 throughout. K denotes the completion of the algebraic closure of k(u)((τ)), and σ_w: x_ij ↦ u_ij τ^{w_ij}.

1. **Theorem A** (y-sparse tests): as boxed in §2.2. Valid over every algebraically closed field.
2. **Theorem A′** (real families, Descartes): for any family of pairwise distinct real polynomials ρ_k (Ryser, additive Knapsack), a polynomial with τ powers of y over ℂ[x] is divisible by y − ρ_k for at most 2τ − 2 indices. Hence T·m·(2τ − 2) ≥ #family.
3. **Theorem 2T** (two terms, cancellation, residue characteristic 0, k = ℂ): as in §3.2, with the machine corollary T·(2m t^{2m} + 4m(t − 1) + 1) ≥ 2^n − 1 for tests whose numerators have 2T shape, with y-sparsity t.
4. **Theorem S′** (monotone tests): as boxed in §4.1.
5. **Theorem G + barrier.**
   - For r ≥ 2 and L ≥ 1 there is a positive polynomial of depth 2L and size O(rL) with exactly r^L root valuations, forming an arithmetic progression.
   - Consequently, for the pc1 substitution, there is a positive polynomial in (X_12, y) of size poly(n) and depth O(n/log n) whose root valuations contain those of N_g.
   - So S′'s threshold Δ = Θ(n/log n) is tight for A_g.
6. **Hierarchy:** Z(Q_{2,n}) is decided by one monotone test of depth 2n and size O(n). Every tree with monotone tests of depth Δ and size s satisfies T(1 + s/Δ)^Δ ≥ 2^n.
7. **Barrier:** as boxed in §5.3.
8. **Theorem B / B1 / AB / σ:** as in pc1, with B′'s gloss corrected (§7).
9. **Part C:** as in §6, with the general-p line added.
10. **Theorem kT and 7.4(c):** conjecture or sketch only.

## 9. Prior art (web search, 24 Nov 2026)

**Directly overlapping (must cite).**
- **Hrubeš–Yehudayoff, "Shadows of Newton polytopes", CCC 2021 (ECCC TR20-189).**
  - Thm 5.1 / §8: a monotone bivariate polynomial with an O(n) circuit and 2^n Newton-polygon vertices. This is the r = 2 gadget, i.e. ideas §2 and Theorem G for r = 2.
  - Thm 5.4: a monotone high-powered formula with k leaves has ≤ k vertices. This is the core of S′.
  - Remark 7.1: a monotone ΣΠ of sparse polynomials has ≤ pqr vertices.
  - What is new here: the depth trade-off and the application to decision trees for A_g.
- **Koiran–Portier–Rojas, arXiv:1309.0486, "Counting tropically degenerate valuations and p-adic approaches to the hardness of the permanent".**
  - Exponent-independent bounds on the number of p-adic root valuations of sums of two products of powers of binomials, under tropical genericity (Cor. 1.5).
  - An O(k³mt) bound under genericity (Lemma 1.18).
  - Valuation-count hypotheses imply permanent hardness.
  - Theorem 2T is its residue-characteristic-0, genericity-free analogue for t-sparse factors.
- **Koiran–Portier–Tavenas–Thomassé, "A τ-conjecture for Newton polygons", FoCM 15 (2015) 185–197.**
  - The conjecture: Newton polygon of Σ_{i≤k}∏_{j≤m} f_ij has poly(kmt) edges.
  - Proved bounds: O(t^{4/3}) for fg + 1, and O(k t^{2m/3}) in general.
  - Their bivariate Newton polygon is exactly the τ/y polygon used here. It improves sl(P) inside 2T, as the idea file notes.
- **Koiran–Portier–Tavenas, "A Wronskian approach to the real τ-conjecture", JSC 68 (2015) 195–214.** The real-roots analogue for sums of products of powers of sparse polynomials; relevant to A′ and 2T.
- **Rojas, "A direct ultrametric approach to additive complexity and the Shub–Smale tau conjecture" (arXiv math/0304100).** p-adic root counts in terms of additive complexity.
- **Phillipson–Rojas, "Fewnomial systems with many roots, and an adelic tau conjecture" (arXiv 1011.4128).**

**Background on BSS lower bounds.**
- **Ben-Or 1983.** Milnor–Thom component counting, real case; it extends to ℂ via ℝ², but it counts components, which A_g does not have many of in the relevant sense.
- **Strassen's degree bound** and **Bürgisser–Lickteig–Shub, "Test complexity of generic polynomials" (1992).** They give only depth ≥ Ω(log deg) = Ω(n) for A_g.
- **Grigoriev–Vorobjov, "Complexity lower bounds for computation trees with elementary transcendental function gates", FOCS 1994 / TCS 157 (1996).** Pfaffian (Khovanskii fewnomial) trees, Ω(√log N) for polyhedra.
- **Meyer auf der Heide (1984).** Polynomial-depth linear decision trees for real Knapsack. This explains why additive Knapsack is out of reach of counting over ℝ with ≤ tests; over ℂ with = tests, A′ still gives the y-sparse bound.
- **Cucker–Shub, "Generalized Knapsack problems and fixed degree separations", TCS 161 (1996) 301–306.** This is NTIME(n^d) ≠ co-NTIME(n^d) over ℝ: "fixed degree" refers to the *time exponent*, not to test degree, so there is no overlap.
- **Meer, "A note on a P ≠ NP result for a restricted class of real machines", J. Complexity 8 (1992) 451–453.** A restricted real model. I could not retrieve the text; do not characterise it beyond the title without reading it.
- **Shub–Smale (Duke 1995).** τ-conjecture ⇒ P⁰_ℂ ≠ NP⁰_ℂ.
- **Koiran, "Shallow circuits with high-powered inputs" (ICS 2011).** The 2T model class.

**Is "NP_ℂ ⊄ P_ℂ for sparse-test machines" known?** I found no published statement of Theorem A or S′ for decision trees over ℂ deciding a Boolean-witness NP_ℂ set. Each is a short combination of:
- (a) the generic-path lemma (standard, L1);
- (b) the Newton-polygon count (standard) or the Hrubeš–Yehudayoff formula lemma.

So it is presumably new as stated, but elementary, and a referee will see it as folklore-level.

**Is the non-archimedean Rolle lemma standard?** Its ingredients are (Robert GTM 198 Ch. 6; Fresnel–van der Put). Its failure in residue characteristic p is classical (Ballantine–Shemanske). I found no reference for the annulus statement in residue characteristic 0. Present it with proof as "standard argument".

## 10. Significance (honest assessment)

**What is solid.** The results are correct, unconditional, degree-free and multiplicity-blind:
- Theorem A: y-sparse tests need 2^n/(mτ) of them.
- Theorem S′: monotone tests of depth Δ need size 2^{Ω(n/Δ)}.
- Theorem 2T: two-term cancellation needs exponentially many tests for fixed m.

That cofactor-blindness is the conceptual point: Newton polygons are the first invariant in this project that a cofactor cannot damage.

**Why it is weak.**
1. The models are much weaker than P_ℂ, and provably so. Theorem G and §4.3 put sets of P_ℂ outside the monotone low-depth class. The natural algorithm "evaluate N_g" is not in any of these classes, nor is any test with many powers of y.
2. The proofs reduce to "a restricted test has few root valuations". That is a fewnomial / KPTT-type statement about the tests, and the A_g side contributes only the elementary fact that N_g has 2^n − 1 valuations. Over the reals the analogue (Descartes / Khovanskii) is old. Over valued fields the S′ core and the gadget are in Hrubeš–Yehudayoff, and the 2T flavour is in Koiran–Portier–Rojas.
3. [T26] is not used. These are not "consequences of the permanent bound".
4. §7 proves that the valuation method cannot go further. One or polynomially many integral substitutions are blocked by easy monotone polynomials of depth Θ(n/log n). Progress needs all weights at once (the tropical cofactor problem, Idea 7) or non-valuation data.

**Fair positioning.** A short note: "Exponential lower bounds for BSS decision trees over ℂ with sparse, two-term, or monotone bounded-depth tests deciding a Boolean-witness NP_ℂ problem, and a barrier for valuation methods". Theorem 2T and the barrier are the most interesting parts. Theorem B/B′ (pc1) is the only result here that uses the permanent bound. Its model ("few false alarms, uniform multiplicities") is natural but still restrictive, and its open multiplicity caveat O1 is the real obstacle. None of this is progress on P_ℂ vs NP_ℂ itself, and the paper should say so in the abstract.

## 11. Files

Scratchpad `ref/` (not part of the repository):
- `chk1.py`: Ryser valuations for both weightings; §7.3 polynomial for n ≤ 4.
- `chk2.py`: base-r gadget; counts and arithmetic-progression property.
- `chk3.py`: 2T random sanity tests.
- `chk4.py`: char-2 span count.
