# Referee report: P_ℂ ≠ NP_ℂ notebooks (y1, y2, ideas-pc-npc §1)

24 Nov 2026. I read the following:
- y2/notebook.md, checks.py and checks.out;
- y1/notebook.md and lemmaL_det_check.py;
- ideas-pc-npc.md §0–§1;
- paper.txt §1.1–1.3 and App. N (Def. N.1, Lemma N.2, Thm N.5);
- Bürgisser, arXiv:1812.06828: full text fetched and read for the abstract, §1.1–1.2, §2 Def. 2.1, §3.1 outline, §4 and Lemma 5.6;
- the arXiv abstract page of 2606.25121.

**Verdicts at a glance**

| Claim | Verdict |
|---|---|
| L1 | CORRECT (constant fixes) |
| L2 | CORRECT |
| L3 | CORRECT |
| L4 | CORRECT WITH FIXES (colength must be small) |
| L6 reduction | CORRECT, but the threshold analysis is **BROKEN** and [T26] plays no role |
| Sanity checks | CORRECT |
| Degenerations (2b) | CORRECT WITH FIXES (one direction reversed, one citation not pinned) |
| B(a) | CORRECT WITH FIXES (proof sketch of step 1) |
| B(b) | CORRECT |
| C | CORRECT WITH FIXES (overclaims in ideas §0.4 and Idea 1) |

## A. y2 notebook

### L1: CORRECT. Two constants need fixing.

**The attack point fails.** The argument does not use the generic point of Z(N_g). It uses the generic path of the *ambient* space ℂ^{m+1}:
- Every z with P(z) ≠ 0 follows that one path. Here P is the product of the numerators of the tests answered "≠ 0" (each division is tested first).
- The path's leaf is reached by a dense open set. A_g is proper and closed, so that leaf rejects.
- So every point of A_g lies in Z(P). This holds for all of Z(N_g), not just the part reached along the path.
- Equivalently, every irreducible component y = g_e lies in the zero set of some test numerator on the ambient generic path, so (y − g_e) divides P.

Branching elsewhere in the tree is irrelevant. The only thing lost is the information in Remark (iii).

Fixes:
- (i) A ± step costs 4 operations (ad, bc, ad±bc, bd), not 3. Every denominator is a product of divisor numerators, which are already tested, so P = ∏(test numerators). This gives L(P) ≤ 4T + T = 5T, and the bound stands.
- (ii) The table says 5T+2n+O(1) but the lemma says 5T+n. Use 5T+n, or 5T for Ryser g. The Ryser roots ±∏_i Σ_{j∈E} X_ij are pairwise distinct (by unique factorisation), so N_g is squarefree and P^{2^n} is not needed.
- (iii) The nonuniform reduction (uniform P_ℂ = NP_ℂ ⇒ P_ℂ(nu) = NP_ℂ(nu)) is fine because HN_ℂ is complete for NP_ℂ(nu).

The model matches. Trees have arbitrary constants, divisions and =-tests, and nonuniform means one tree per input length. The degree 2^{O(T)} only enters deg Q.

### L2: CORRECT
- (b) (−δ)^D N_g(x,−1/δ) = ∏(1+δg_e) is exact. The degree enters only through a free constant.
- Composing border parameters: η = δ^K with K > 2^{L} works, because the output of any size-L circuit has y-degree ≤ 2^L.
- Constants in k((ε)) are allowed by paper Def. 1.3 / N.1. B04 Lemma 5.6(2) says Bürgisser's k(ε) model is equivalent.
- "+3" counts operations. In paper gates (constants count as gates), it is +O(1).
- (c) The ε-truncation needs g homogeneous in x, which holds for Ryser g. 2^n never enters.
- Corrected corollary: L(N_g) ≥ n^{c(log n)^{1/3}}/O(n²) − n² over ℂ.

### L3 (cofactor lemma): CORRECT
- The single division is exact (Q/H = N_g).
- Strassen truncation at a generic a ∈ ℂ^m needs only that H(a,−1/δ) ≠ 0 in ℂ((δ)). This holds because −1/δ is transcendental over ℂ.
- All degree-0 parts are elements of K, so they are hard-wired constants and no division gate remains.
- The output is S_g(a+z) + δ·(an element of ℂ[δ][z]), because F = ∏(1+δg_e) is a polynomial in δ.
- Only the output degree d enters, never 2^n or deg H.

Cor. 3.2 is correct as stated. It uses B04 Thm 1.3, which I verified: L̄(g) ≤ O(M(d)M(d⁴)EC(g) + d^{2γ}M(d)²), char 0, with exact EC. Apply it to the irreducible factors h_i.

### L4 (Artinian obstruction): CORRECT WITH FIXES
The proof is right. I checked the CRT split, N_p ∈ m_p^{deg}, m_p^{r_p} = 0, the full/saturated cases, and deg_y Q' ≤ r.

**Fix.** Q' is easy only if r(L(g)+2) is below the [T26] threshold, so the meta-claim ("no argument that looks only at Q mod I can prove Gap G") holds only for colength r ≤ n^{o((log n)^{1/3})}, polynomial in practice. Fat points of exponential colength are not covered.

Paper statement: "For every ideal I of colength r there is a product Q' of ≤ r branches with N_g·A = Q'·A. Hence no property of Q mod I with r = poly(n) separates easy multiples of N_g from easy non-multiples."

### L6 (Span Conjecture): reduction CORRECT, threshold analysis BROKEN

**[T26] is not needed at all.**
- For Ryser g, dim span{g_e} = 2^n − 1 by elementary linear algebra. Take the monomials ∏_i X_{iσ(i)} with im σ = F. Their coefficient in g_E is [F ⊆ E]. That is the zeta matrix of the Boolean lattice, which is unitriangular.
- I checked numerically that the rank is 2^n−1 for n = 2,3,4,5 (scratch script span.py).
- So the Boolean-indexed conjecture gives EC(N_g) ≥ p^{-1}(2^n−1). With polynomial p this is **exponential**, with no permanent lower bound involved.

Consequences:
- "p = (sd)^{o((log)^{1/3})} suffices" is true but far from sharp. Any p with p(n^k, n) < 2^n − 1 for every k suffices, e.g. p = 2^{(log sd)^{O(1)}}.
- The listed "not sufficient: N^{Ω((log N)^{1/3})}" is **false**: that bound is 2^{O((log n)^{4/3})} ≪ 2^n, so it suffices. Only m^{Θ(d)}-type bounds fail.
- The "matched to the [T26] exponent" remark (§9(1)) and "unconditional given [T26]" (§9(4)) should be deleted.
- Restricted to the one family that Lemma 6 needs, the Boolean-indexed form is literally a restatement of Gap G, in a stronger (exponential) form. It is not a reduction to anything else.
- The general conjecture also kills multiplicative Knapsack ∏_e(y − x^e) (span 2^n). That yields P_ℂ ≠ NP_ℂ without any VNP input.

Corrected statement: "Span(p) with p(n^{O(1)}, n) < 2^n − 1 ⇒ EC(N_g) superpolynomial for Ryser g (and for g = x^e) ⇒ P_ℂ(nu) ≠ NP_ℂ(nu). [T26] is not used."

### Sanity checks: CORRECT
- checks.out reproduces.
- The Moore recursion and the char-p Knapsack divisibility are standard.
- Res_T(T^M−1, y−Φ) = ±lc^M det(C^M−I) holds, with span ≤ deg_T Φ + 1.

The span ≤ cost heuristic was only tested for small deg_T Φ. I suggest a harder test case: Φ(x,T) = ∏_i(x_i + T^{2^{i−1}}). It has a small circuit and T-degree 2^n − 1, and its cyclic norm over μ_{2^n} has roots spanning all 2^n multilinear polynomials. If that norm, or a multiple of it, were easy, the conjecture would be refuted. I could not decide whether it is.

### Degenerations (2b): CORRECT WITH FIXES
- lt is multiplicative, and limits of products are products of limits. Fine.
- **Direction error.** "Gap G for the degenerate family is implied by Gap G for g" is reversed. An easy multiple of N_g degenerates to a border-easy multiple of the degenerate norm. So (border) Gap G for the degenerate family implies Gap G for g.
- **Citation not pinned.** "Factors of border-easy low-degree polynomials are border-easy" matches the B04 *abstract* ("in terms of the (approximative) complexity of f"). The theorem I located (Thm 1.3) is stated with exact EC. Pin the exact statement before use.

L5 and the rest: not contested.

## B. y1 notebook

### (a) T1–T3: CORRECT WITH FIXES
B04 statements verified verbatim:
- Lemma 1.1, and the remark that it holds for graphs over any infinite field;
- Thm 1.3, with char 0 assumed throughout;
- Remark 1.4(1): L̄ ≤ O(M(d²)EC) for graphs;
- Cor. 1.5: L̄(φ) ≤ O(M(d²)C(graph φ)), also with two-sided randomisation;
- Cor. 4.1 and Cor. 4.5 (VNP ⊄ V̄P ⇒ P_ℝ ≠ PAR_ℝ).

Definitions verified:
- C(·) counts arithmetic operations and tests of an algebraic computation tree, i.e. its depth. Constants are arbitrary, and ≤-tests are allowed over ℝ.
- L̄ is over k(ε), equivalently k((ε)) (Lemma 5.6(2)), with free constants.

The models match. [T26] has free constants, unbounded degree, and gates that count constants. Any B04 approximation is a [T26] approximation, so the lower bound transfers.

Quantitative bound: C ≥ L̄/O(m² log m), which gives depth ≥ m^{c'(log m)^{1/3}} for some c' > 0, i.e. 2^{Ω((log N)^{4/3})}. Correct.

**Fix.** The proof sketch of step 1 is garbled. It describes the generic point of the graph, and the sentence "every point off the graph … is also accepted, which is impossible" is incoherent. Replace it with the ambient generic-path argument from L1, or just cite Lemma 1.1.

I did not verify that P_ℂ ≠ PAR_ℂ was open. I rely on y1's quotes of [KP07] and [B24].

### (b) Lemma L, κ = 0 and κ = 1: CORRECT
I checked line by line:
- slicing preserves the defect, because the fibre directions lie in ker Jac;
- Ŵ is a component of V(G);
- the rank equality, which gives corank = κ;
- chord iteration with a constant J^{-1};
- the κ = 1 perturbation: Θ, the IFT in (x,ε,s), and det = det(D_{y'}G')·eUε^{e−1} (char 0);
- uniqueness of the Hensel lift over ℂ((ε)), so the coefficients lie in ℂ[[ε]].

**Fix.** The notation overloads m (witness length versus matrix size) in T6; rename one of them.

T6, T7 and C1 are correctly labelled. The §6 "does not follow" list is accurate.

## C. Dependency map (ideas §1)

The implication directions in B1–B13 are correct as stated. I did not re-verify B3, B12 or B13.

**Bürgisser's conjecture: verified.** arXiv:2606.25121 exists: Bürgisser, *Intractability of Hilbert's Nullstellensatz implies algebraic hardness of permanent*, v1 23 Jun 2026, v2 19 Oct 2026. The abstract says: "In the reverse direction, we conjecture that VNP_C ⊄ V̄P_C implies that P_C(nu) ≠ NP_C(nu)." It is a conjecture, and the proved direction is the converse.

Not verified:
- B9 (a private communication);
- "Conj. 8.2 of the 2000 book";
- B13 (Zhang).

**Fixes:**
- (1) **Overclaims.** §0.4 and Idea 1 say "every hypersurface of polynomial degree in NP_ℂ(nu) is border-easy … gives graph(per) ∉ NP_ℂ(nu)". This is false as stated. It is proved only for verifiers of defect ≤ 1 (y1 T5–T7), and the general case is y1's open C1.
- (2) §1.3 "if A ∈ P_ℂ(nu) has closure containing Z(g) …" also needs ℂ^n∖A to be dense (Z(g) ⊆ cl A ∩ cl A^c).

## Assessment

**Genuine new content:**
- An unconditional P_ℂ ≠ PAR_ℂ and P_ℝ ≠ PAR_ℝ. This is a one-line corollary of B04 Cor. 4.5 + [T26].
- Lemma L for defect ≤ 1, a modest new lemma.
- L3 (the cofactor of any easy multiple is border-hard). Correct, but by the notebook's own admission not contradictory by itself.
- L4, a clean barrier for local methods with small colength.

L1 and L2 are standard reformulations: generic path, coefficient extraction, Strassen.

**Progress on P_ℂ ≠ NP_ℂ itself: essentially none beyond localisation.** The border bound enters only through L3, which does not close the gap.

**The Span Conjecture is harder than the target, not easier:**
- Its needed instance is Gap G, restated in a stronger form.
- [T26] is irrelevant to it.
- With polynomial p it implies *exponential* BSS lower bounds (EC(N_g) ≥ 2^{Ω(n)}), and hardness of multiples for multiplicative-Knapsack and q-Pochhammer-type norms. That is τ-conjecture territory.

It is a reasonable organising conjecture, but it should not be presented as a reduction.
