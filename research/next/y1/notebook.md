# y1 notebook: BSS over ℂ after the border bound VNP ⊄ V̄P (idea 1 of ideas-pc-npc.md)

24 Nov 2026. Executor y1. Tags: **[K]** known, source read (quoted below); **[K→R]** a known *conditional* theorem
whose hypothesis is now the 2026 theorem, so the conclusion now holds unconditionally (immediate corollary, credit belongs to the
original author together with [T26]); **[R]** derived here with a full proof (given [T26]); **[C]** conjecture or open.
**[T26]** = Anthropic, *VP ≠ VNP over every field* (paper.txt), Thm 1.1 / Thm N.5. No human has checked [T26].

Sources downloaded and read (text in the scratchpad `y1src/`):
- [B04] Bürgisser, *The complexity of factors of multivariate polynomials*, FoCM 4 (2004) 369–396; arXiv:1812.06828 (corrected
  version). Read: §1–§4.
- [B26] Bürgisser, *Intractability of Hilbert's Nullstellensatz implies algebraic hardness of permanent*, arXiv:2606.25121v2
  (19 Oct 2026). Read: §1, §2.1–2.3, §5.2, §6.
- [B24] Bürgisser, *Completeness classes in algebraic complexity theory*, arXiv:2406.06217 (2024). Read: §4.4 (p. 25).
- [KP07] Koiran–Perifel, *VPSPACE and a transfer theorem over the complex field*, arXiv:0706.1477. Read: abstract, §2–3.
- [FK97] Fournier–Koiran, *Are lower bounds easier over the reals?*, LIP RR-97-38 / STOC 1998. Read: abstract only.
- [CKKLW95] Cucker–Karpinski–Koiran–Lickteig–Werther, *On real Turing machines that toss coins*, STOC 1995. **Abstract only
  (via search snippet): BPP ⊆ P/poly generalised to the real model.** [K, unverified wording.]
- BCSS 1998 (book) and Koiran 1997 (elimination of constants): not re-read; used only via the quotations in [B26] §1.3, §2.1.

Sanity script: `research/next/y1/lemmaL_det_check.py` (Lemma L, reduced case, on det_3; see §4.6).

---------------------------------------------------------------------------------------------------------------------

## 0. Results in one screen

| # | Statement | Tag |
|---|---|---|
| T1 | Every algebraic computation tree (equality tests, divisions allowed, any complex constants) that decides graph(per_m) = {(X,y) ∈ ℂ^{m²+1} : y = per X} has depth > m^{c(log m)^{1/3} − 3} for all large m. The same holds over ℝ (with ≤-tests), over every field of characteristic 0 (with =-tests), and for randomized trees with two-sided error. Same for HC_m. | **[K→R]** ([B04] Cor. 1.5 + [T26] Thm N.5) |
| T2 | Same for the hypersurface PERZERO_m = {X : per X = 0} over ℂ (bound m^{c(log m)^{1/3}}/poly(m)). | **[K→R]** ([B04] Cor. 4.1 + [T26]) |
| T3 | **P_ℂ ≠ PAR_ℂ**; indeed PAR⁰_ℂ ⊄ P_ℂ(nu). Likewise **P_ℝ ≠ PAR_ℝ**, and P_K ≠ PAR_K for every algebraically closed K of characteristic 0. | **[K→R]** — this is *exactly* [B04] Cor. 4.5 (stated as conditional on VNP ⊄ V̄P; [B24] §4.4 restates it for ℝ and ℂ) |
| T4 | **Lemma L, reduced case**: if Z(h) (irreducible, degree d) is a component of the closure of A ∈ NP_ℂ(nu), via a size-s verifier one of whose leaf varieties is generically reduced along a witness component dominating Z(h), then L(h) ≤ O(d³ log d · s²) — *exact*, not border. | **[R]** |
| T5 | **Lemma L, curvilinear case** (Jacobian defect κ ≤ 1 along that component; includes T4 and all deterministic trees): L̄(h) ≤ O(d³ log d · s²). | **[R]** |
| T6 | Corollary of T4–T5 + [T26]: every NP_ℂ verifier of size s < m^{(c/2)(log m)^{1/3}−2} for graph(per_m) (or PERZERO_m) has Jacobian defect ≥ 2 along *every* witness component (of every leaf) that dominates the hypersurface. | **[R]** |
| C1 | Lemma L in general (defect ≥ 2); hence graph(per) ∉ NP_ℂ(nu) and NP_ℂ ≠ PAR_ℂ. | **[C]** (open; the naive perturbation provably fails, §4.5) |
| — | P_ℂ ≠ NP_ℂ | **does not follow** (§6) |

Novelty, plainly. T1–T3 are immediate corollaries of Bürgisser 2004 and [T26]; Bürgisser stated the implication explicitly
("Hypothesis (12) implies a separation of complexity classes in the Blum-Shub-Smale model ... Corollary 4.5: If VNP ⊄ V̄P is true,
then P_R ≠ PAR_R"). They are worth recording because they are, as far as we can find, the first unconditional separations of
P from PAR in the full BSS model (with multiplication) over ℝ or ℂ. Koiran–Perifel 2007 had shown these separations *require*
VPSPACE lower bounds, which [T26] now supplies. A web search (23–24 Nov 2026) found nobody who has posted this corollary.
T4–T6 appear to be new; they are the natural NP-verifier version of [B04] Prop. 3.4. I have not found them in the literature.
The reduced case (T4) gives *exact* complexity, which is stronger than [B04].

---------------------------------------------------------------------------------------------------------------------

## 1. Definitions and exact cited statements

### 1.1 Models
- **Algebraic circuit with selector/test gates** (Koiran–Perifel §2, [B26] §2.1): a DAG with input gates, constant gates,
  gates for +, −, ×, and test gates "= 0?" that output 1 if the input is 0 and 0 otherwise. It decides a set A ⊆ ℂ^n.
  BSS machines may also divide; a division can be replaced by numerator–denominator pairs at a cost factor of at most 3.
  A size-s circuit unrolls into an **algebraic computation tree** of depth ≤ s: evaluate the gates in order and branch at
  each test. Conversely, a time-T BSS machine gives a tree of depth ≤ T on each input length.
- **P_ℂ** ([KP07] §2): A is in P_ℂ if there are a constant tuple ā ∈ ℂ^p and a P-uniform family of polynomial-size circuits C_n
  with x ∈ A ⇔ C_n(x, ā) = 1. This is equivalent to polynomial-time BSS machines with constants.
- **P_ℂ(nu)** ([B26] §2.1, with arbitrary constants): families of polynomial-size circuits with no uniformity condition and any
  constants; equivalently P_ℂ/poly. P⁰ means constant-free (only 0 and 1). Inclusions: P⁰_ℂ ⊆ P_ℂ ⊆ P_ℂ(nu).
- **NP_ℂ(nu)** ([B26] §2.1): A is in NP_ℂ(nu) if x ∈ A ⇔ ∃y ∈ ℂ^{p(n)} (x,y) ∈ B, for some B ∈ P_ℂ(nu). NP_ℂ is the uniform
  version. HN_ℂ is complete for both.
- **PAR_ℂ** ([KP07] §2, after BCSS §18.2 Def. 4): languages recognised by a PSPACE-uniform (equivalently P-uniform) family of
  algebraic circuits of polynomial depth and possibly exponential size, with constants ā. Known inclusions: P_ℂ ⊆ NP_ℂ ⊆ PAR_ℂ.
  The inclusion NP_ℂ ⊆ PAR_ℂ is a theorem of BCSS that uses parallel quantifier elimination ([KP07] intro: "it contains NP_C
  [1] (but the proof of this inclusion is much more involved than in the discrete case)").
- **Complexity measures** ([B04] §1.1). L(g) is the straight-line complexity: the number of arithmetic operations of a
  division-free SLP with free constants. C(g) is the decision complexity: the number of operations and tests of an algebraic
  computation tree deciding {g = 0} (over ℝ, ≤-tests are also allowed). EC(g) = min{L(f) : f ≠ 0, g | f}. **L̄** is
  approximative complexity ([B04] Def. 2.1): the least r such that some F ∈ R[X] with F_{ε=0} = f has L(F) ≤ r over
  K = k(ε), where R is the local ring at ε = 0.
- **Compatibility with [T26] Def. N.1.** [T26] uses circuits over k((ε)) computing f + εg with g ∈ k[[ε]][x]. Since k(ε) ⊂ k((ε))
  and R ⊂ k[[ε]], every [B04]-approximation is a [T26]-approximation. [T26] counts gates, including inputs and constants,
  while [B04] counts operations; a [B04] SLP with r operations has at most 3r + (number of variables) gates. So [T26] Thm N.5
  gives **L̄(per_m) ≥ (m^{c(log m)^{1/3}} − m²)/3** over every field of characteristic ≠ 2, and the same for HC_m over every field.

### 1.2 Bürgisser 2004, verbatim (arXiv v1 of 1812.06828)
- *Lemma 1.1.* "Let g be the irreducible generator of a hypersurface in R^n or C^n. Then EC(g) ≤ C(g)." Remark after it:
  "the conclusion of this lemma remains true over any infinite field k if g is the generator of the graph of a polynomial ϕ,
  that is, g = Y − ϕ(X_1,…,X_n)."
- *Theorem 1.3* (char 0, matrix multiplication exponent γ): "L̄(g) ≤ O(M(d)M(d⁴)EC(g) + d^{2γ}M(d)²)."
- *Remark 1.4.* (1) If g generates the graph of ϕ, then L̄(g) ≤ O(M(d²)EC(g)). (2) L̄(g) ≤ O(M(d⁴)EC(g) + d^{2γ}M(d)) if g is the
  irreducible generator of a hypersurface in ℝ^n or ℂ^n.
- **Corollary 1.5.** "The approximative complexity L̄(ϕ) of a polynomial ϕ is polynomially bounded in the decision complexity
  of the graph of ϕ and the degree d of ϕ, namely L̄(ϕ) ≤ O(M(d²) C(graph(ϕ))). This remains true if we allow randomization
  with two-sided error." Here M(d) = O(d log d) is the cost of multiplying univariate polynomials, and "unless stated otherwise,
  k denotes a fixed field of characteristic zero". The proof of Prop. 3.4 uses char 0 in "e λ^e h(0,0) ε^{e−1} ≠ 0".
- *Corollary 4.1.* "Let g be the generator of an irreducible hypersurface in R^n or C^n of degree d ... L̄(g) ≤ O(M(d⁴)C(g) +
  d^{2γ}M(d))." The randomized claim "follows easily by the results in [33, 11, 14]".
- *Corollary 4.4.* "Assume VNP ⊄ V̄P over a field k of characteristic zero. Then for any VNP-complete family (g_n), checking
  the value y = g_n(x) cannot be done by deterministic or randomized algebraic computation trees with a polynomial number of
  arithmetic operations and tests in n."
- **Corollary 4.5.** "If VNP ⊄ V̄P is true, then we have P_R ≠ PAR_R in the Blum-Shub-Smale model over the reals. (For the
  proof use Corollary 4.1 with the permanent polynomial g.)" [B24] p. 25: "[Bür04, Cor. 4.5] proved that the separation
  VNP_C ⊄ V̄P_C in Valiant's model implies the separations P_R ≠ PAR_R as well as P_C ≠ PAR_C in the BSS-model."
- **Bürgisser 2026 ([B26]) Conjecture 1.1:** "If VNP_C ⊄ V̄P_C, then P_C(nu) ≠ NP_C(nu)." It is still a conjecture.
  [B26] Thm 1.1 is the converse direction (P⁰_ℂ(nu) ≠ NP⁰_ℂ(nu) ⇒ VP⁰ ≠ VNP⁰).
- **Koiran–Perifel [KP07], Thm 2:** "If Uniform VPSPACE⁰ = Uniform VP⁰_nb then PAR⁰_C = P⁰_C. ... one must first be able to show
  that there are VPSPACE families which are hard to evaluate in order to separate P_C from NP_C, or even from PAR_C."

### 1.3 Where graph(per) sits
GRAPH-PER := ⋃_m {(X, y) ∈ ℂ^{m²+1} : y = per_m(X)}. Inputs of any other length are rejected.

- **Upper bound: GRAPH-PER ∈ PAR⁰_ℂ** (constant-free, P-uniform). Proof: Ryser's formula
  per X = (−1)^m Σ_{S⊆[m]} (−1)^{|S|} ∏_{i=1}^m Σ_{j∈S} x_{ij}. The circuit computes each inner sum (depth ⌈log m⌉), each
  product (depth ⌈log m⌉) and the outer sum of 2^m terms by a balanced tree (depth m). It then computes per X − y and ends with
  one test gate. Depth O(m) = O(√N) for N = m²+1, size O(2^m m²), and no constants other than 0, 1 (−1 = 0 − 1). The gate list
  is generated in polynomial time by a Turing machine: gate names encode S as an m-bit string. ∎ The same works for PERZERO and
  for HC_m (sum over cyclic permutations: depth O(m log m)).
  GRAPH-PER also lies in EXP⁰_ℂ, and in P_ℂ relative to a per-oracle (trivially).
- **Lower bound: GRAPH-PER ∉ P_ℂ(nu)** (T1). It is **unknown** whether GRAPH-PER ∈ NP_ℂ, coNP_ℂ or PH_ℂ. Conjecture C1 is
  that it is not in NP_ℂ(nu); T6 is the partial result.

---------------------------------------------------------------------------------------------------------------------

## 2. Claim (a): proof of T1–T3

**Theorem T1 [K→R].** Let k be a field of characteristic 0 (trees with =-tests) or k = ℝ (=- and ≤-tests). There are c > 0 and
m₀ such that for all m ≥ m₀ every algebraic computation tree over k (any constants from k, divisions allowed) that decides
graph(per_m) has depth at least m^{c(log m)^{1/3} − 3}. The same holds for trees with two-sided-error randomization (in the
sense of [B04] Cor. 1.5), and for graph(HC_m) over every field of characteristic 0.

*Proof.* Let C = C(graph(per_m)) be the depth of an optimal tree. Here ϕ = per_m has degree d = m in n = m² variables.
1. *Lemma 1.1 for graphs* (any infinite field): EC(Y − per_m) ≤ C. The reason is the generic path. Follow the path of a
   generic point of the irreducible hypersurface graph(per). The tests answered "≠ 0" along it are nonzero rational functions
   on the graph. Their numerators q₁, …, q_r are not divisible by Y − per (otherwise they would vanish on the graph). Every
   point of graph(per) outside {∏ q_i = 0} follows this path and is accepted. Every point off the graph that follows this path
   is also accepted, which is impossible. So the path's "= 0" tests define, on the open set ∏ q_i ≠ 0, exactly the graph. The
   product of the numerators of the "≠ 0"-tested functions, together with the "= 0" tests, gives a nonzero multiple of Y − per
   of complexity O(C) (Lemma 1.1, [B04]). I did not re-derive the constant; [B04] states EC ≤ C.
2. *Remark 1.4(1) / Cor. 1.5*: L̄(per_m) = L̄(Y − per_m restricted to Y = 0) ≤ L̄(Y − per_m) ≤ O(M(d²)·EC) ≤ K₁·m² log m · C
   for an absolute constant K₁. This uses M(d) = O(d log d) and char k = 0.
3. *[T26] Thm N.5* with §1.1 compatibility: L̄(per_m) ≥ (m^{c(log m)^{1/3}} − m²)/3.
4. Combining: C ≥ (m^{c(log m)^{1/3}} − m²)/(3K₁ m² log m) ≥ m^{c(log m)^{1/3} − 3} for m large.
   The randomized version is the randomized part of Cor. 1.5. ∎

In terms of the input length N = m² + 1: depth ≥ N^{(c/2)(½ log N)^{1/3} − 3/2} = 2^{Ω((log N)^{4/3})}, quasi-polynomial.
The best upper bound (Ryser) is 2^{O(√N)}.

**Theorem T2 [K→R].** Over ℂ, C({per_m = 0}) ≥ m^{c(log m)^{1/3}}/O(m⁴ log m) for large m.
Proof. per_m is irreducible for m ≥ 1. It is multilinear, so in any factorization each variable occurs in exactly one factor.
If x_{ij} and x_{ij'} (same row) were in different factors f and g, the coefficient of x_{ij}x_{ij'} in fg would be
(∂f/∂x_{ij})(∂g/∂x_{ij'}) ≠ 0, but per has no monomial containing two entries of one row. The same holds for columns, so the
row–column graph connects all variables and one factor is constant. Apply Cor. 4.1 with d = m:
L̄ ≤ O(M(m⁴)C + m^{2γ}M(m)), so C ≥ (L̄ − O(m^{2γ+1} log m))/O(m⁴ log m). Then use [T26]. ∎
Over ℝ use the graph, or note that per_m has a smooth real zero. Take real X with P₁₁ = per(minor₁₁) ≠ 0 and solve for x₁₁.
So {per = 0} is a real hypersurface and Cor. 4.1 applies there too.

**Theorem T3 [K→R].** P_ℂ ≠ PAR_ℂ. More precisely, PAR⁰_ℂ ⊄ P_ℂ(nu). Likewise P_ℝ ≠ PAR_ℝ, and P_K ≠ PAR_K for every
algebraically closed K of characteristic 0 (the graph version of Lemma 1.1 and Prop. 3.4 work over any field of char 0).
Proof. GRAPH-PER ∈ PAR⁰_ℂ by §1.3. If it were in P_ℂ(nu), a size-s(N) circuit family would give trees of depth ≤ s(N) = poly(N),
contradicting T1. ∎
Also BPP_ℂ ≠ PAR_ℂ, in Bürgisser's randomized-tree sense. The constant-free version P⁰_ℂ ≠ PAR⁰_ℂ follows as well.

**Hypotheses checklist.**
- Characteristic: char 0 is needed by [B04]. [T26] holds in every characteristic (HC_m), but in char p [B04] Prop. 3.4 breaks
  when p | e, the multiplicity of the graph factor in the exclusion polynomial. So P_{F̄_p} ≠ PAR_{F̄_p} is **[C]** (it would
  follow from a char-p version of [B04] for graphs).
- Uniform vs nonuniform: the lower bound is nonuniform (trees with arbitrary constants) and the upper bound is uniform and
  constant-free. That is the strongest combination.
- Degree: d = m is polynomial, which is exactly what [B04] needs.
- Over ℝ: [B04] Lemma 1.1 holds for real hypersurfaces with ≤-tests, and graphs are real hypersurfaces.

**Prior status.** [KP07] (2007): separating P_ℂ from PAR_ℂ requires VPSPACE lower bounds. [B04] Cor. 4.5 (2004): VNP ⊄ V̄P ⇒
P_ℝ ≠ PAR_ℝ. [B24] (2024) restates this for ℂ and still treats it as conditional. Degree arguments cannot separate P from PAR,
because polynomial depth already allows degree 2^{poly}. That is why the problem was open even though P_ℂ ≠ EXP_ℂ and
NC_ℂ ≠ P_ℂ are easy degree arguments. **So T3 is new as an unconditional theorem, but it is an immediate corollary.** Credit
goes to Bürgisser 2004 and [T26].

---------------------------------------------------------------------------------------------------------------------

## 3. Setting for Lemma L

A ∈ NP_ℂ(nu) via a verifier circuit V of size s on inputs (x, w) ∈ ℂ^n × ℂ^m. We may assume m ≤ s and use no divisions
(numerator–denominator pairs cost a factor 3). The accepted set of V is a finite union of leaf sets
S_λ = {q_{λ,1} = … = q_{λ,r} = 0, q'_λ ≠ 0}, where r ≤ s and all q_{λ,i} together have L ≤ 3s (they are computed by
one straight-line program, the path). There may be 2^s leaves, but each one is cheap. A = ⋃_λ π(S_λ), with π the projection
to x.

Hypothesis (H): Z(h) ⊂ ℂ^n is irreducible of degree d (h reduced) and is an **irreducible component of the Zariski closure
of A**. Examples: A = Z(h), or A = graph(ϕ).

*Choice of witness component.* Z(h) ⊆ ⋃_λ cl π(S_λ) ⊆ cl A. By irreducibility and (H), some leaf λ and some irreducible
component W of cl S_λ have cl π(W) = Z(h). Then W is a component of V(q_λ) not contained in V(q'_λ). Let n − 1 + k = dim W,
so k is the generic fibre dimension.

*Defect.* Let ρ be the rank of the Jacobian of (q_{λ,1}, …, q_{λ,r}) with respect to (x, w) at a generic point of W.
Define **κ(W) := codim W − ρ = (m + 1 − k) − ρ ≥ 0**. In char 0, κ = 0 ⇔ the scheme V(q_λ) is generically reduced along W.
κ ≤ 1 means **curvilinear**: the fibre of V(q_λ) at a generic point of W, transverse to W, has embedding dimension ≤ 1.

*Deterministic trees have κ ≤ 1 automatically.* With m = 0, the slicing below leaves one fibre variable t. So T5 contains
[B04]'s decision-complexity theorem as the special case m = 0.

---------------------------------------------------------------------------------------------------------------------

## 4. Lemma L

**Theorem T4–T5 (Lemma L, curvilinear form) [R].** Assume (H) and κ(W) ≤ 1 for some leaf λ and component W as in §3. Then
L̄(h) ≤ O(d³ log(d+1) · m s). If κ(W) = 0, then L(h) ≤ O(d³ log(d+1) · m s), which is exact complexity.

The proof uses no bound on the degree of W, of the fibres, or of the q's, which can be 2^s. Newton's method only needs the
cost of evaluating the q's and the truncation order d. The constants that appear are complex numbers (advice), which is fine
in the nonuniform model.

### 4.1 Generic choices, in this order
1. **Slicing.** Choose generic affine forms ℓ₁, …, ℓ_k in w alone. Let W' be a component of W ∩ {ℓ = 0} that dominates Z(h).
   - Dimension count on the incidence variety I = {(y, Λ) : y ∈ Y, y_w ∈ Λ}: for each of the finitely many varieties Y in play,
     dim(Y ∩ {ℓ = 0}) ≤ dim Y − k. So dim W' = n − 1, W' → Z(h) is generically finite, and W' is an irreducible component of
     V(q_λ, ℓ).
   - A generic codim-k affine slice of a k-dimensional affine fibre is nonempty, so some component of the slice dominates.
   - Slicing does not change the defect, because the ℓ's are linear and generic in w.
2. **Direction.** Choose a generic direction b with h_d(b) ≠ 0, where h_d is the top-degree part of h. Coordinates are
   (x, t, w), and Ŵ := {(x, t, w) : (x + tb, w) ∈ W'}. Then Ŵ ≅ W' × ℂ is irreducible of dimension n and Ŵ → ℂ^n_x is dominant
   and generically finite.
   Ŵ is a component of V(Q), where Q(x, t, w) := (q_λ(x + tb, w), ℓ(w)) consists of r + k polynomials with L ≤ 3s + 2km.
3. **Combinations.** Choose m + 1 generic linear combinations G = (G₁, …, G_{m+1}) of the entries of Q. Then
   L(G) ≤ 3s + 2(m+1)(r + k) = O(ms). Two facts:
   - (a) [standard; Krull plus choosing each G_i to avoid the components not inside V(Q)] every component of V(G) either lies
     in V(Q) or has dimension exactly n. So Ŵ is an irreducible component of V(G), and every other component meets Ŵ in
     dimension ≤ n − 1.
   - (b) For generic λ-coefficients, rank D_y G(p) = rank D_y Q(p) on a dense open subset of Ŵ, where y = (t, w) are the m + 1
     fibre variables. The bad set of (coefficients, p) is a proper closed subset of the product.
4. **Base point.** Choose a generic a ∈ ℂ^n.
   - The line a + tb meets Z(h) transversally in d distinct points x_j = a + t_j b.
   - It avoids the codim-≥2 set Z(h) ∖ U, where U ⊆ π(W') is open dense. This works because b is fixed and generic, so the
     union of lines parallel to b through a set of dimension ≤ n − 2 has dimension ≤ n − 1.
   - Every point of Ŵ over a avoids any prescribed proper closed subset of Ŵ, since its image has dimension < n. Pick one
     point p̂_j = (a, t_j, w_j) ∈ Ŵ over each x_j. So p̂_j is a smooth point of Ŵ, Ŵ → ℂ^n is étale there (char 0, generic),
     p̂_j lies on no other component of V(G), and (b) holds at p̂_j.
5. **Rank equality.** Fibre rank equals full rank at p̂_j. dπ: T Ŵ → T ℂ^n is an isomorphism, and the Zariski tangent space
   of V(Q) maps onto T ℂ^n. Hence dim T_{p̂}V(Q) = n + dim(T_{p̂}V(Q) ∩ vertical), so rank D_y Q = rank D_{(x,y)} Q at p̂_j.
   With dim Ŵ = n this gives **corank D_y G(p̂_j) = κ**.

### 4.2 Reduced case κ = 0 (exact)
D_y G(a; t_j, w_j) =: J_j is invertible.
- By the implicit function theorem, V(G) near p̂_j is a smooth n-dimensional graph over x. It contains the smooth
  n-dimensional germ of Ŵ, so the two germs are equal.
- By Hensel's lemma in ℂ[u][[T]] (substitute x = a + Tu, u a vector of new variables) there is a unique formal solution
  y_j(T) = (t_j(a + Tu), w_j(a + Tu)) with y_j(0) = (t_j, w_j). It is the expansion of the analytic branch, so
  a + Tu + t_j(·) b ∈ Z(h).
- **Chord iteration** y ← y − J_j^{−1} G(a + Tu, y), started at the constants (t_j, w_j). With e_ν = y_ν − y_j:
  e_{ν+1} = (I − J_j^{−1} D_y G(x, y_j)) e_ν + O(e_ν²) = O(T) e_ν + O(e_ν²), and e₀ = O(T). So e_ν = O(T^{ν+1}).
  There are no divisions: J_j^{−1} is a constant matrix. After d + 1 steps, t_j(a + Tu) is correct modulo T^{d+1}.
- **Product.** h(x + tb) has degree d in t, leading coefficient h_d(b), and the d distinct roots t_j(x). Hence
  h(a + Tu) ≡ h_d(b) ∏_j (−t_j(a + Tu)) mod T^{d+1}.
- Since h(a + Tu) has T-degree d, its T^i coefficient is the degree-i homogeneous part H_i(u). So h(x) = Σ_{i≤d} H_i(x − a).

*Cost.* Represent truncated series by their d + 1 coefficients, each a polynomial in u computed by the circuit.
- One evaluation of G costs O(M(d) L(G)) = O(d log d · ms), and the matrix–vector product costs O(m²d).
- d + 1 iterations for each of d branches, plus O(dM(d)) for the product and n + d for reassembly.
- Total: L(h) ≤ O(d² (d log d · ms + m² d)) = O(d³ log d · ms), using m ≤ s. ∎

### 4.3 Curvilinear case κ = 1 (border)
At p̂_j, D_y G has rank m. After a linear change of fibre coordinates y = (y', s) with s ∈ ℂ, split G = (G', g), where G' has m
equations and D_{y'} G' is invertible at p̂_j.
- **Local structure.** By the implicit function theorem G'(x, y', s) = 0 ⇔ y' = Y'(x, s) near (a, s_j). Put
  ψ(x, s) := g(x, Y'(x, s), s).
  - ψ ≢ 0: otherwise V(G) would contain an (n+1)-dimensional germ.
  - Its zero set near (a, s_j) is the germ of Ŵ, which is {s = σ(x)} with σ analytic (Ŵ is étale over x).
  - By Weierstrass preparation, ψ = U(x, s)·(s − σ(x))^e with U(a, s_j) ≠ 0 and e ≥ 1: a monic Weierstrass polynomial whose
    only root is σ(x) is (s − σ)^e.
  This is exactly [B04]'s situation (f = g^e h), with analytic instead of polynomial functions.
- **Perturbation** (Bürgisser's trick). Unknowns (y', s); equations
  Ĝ_ε := ( G'(x, y', s + ε),  g(x, y', s + ε) − c_ε ),  where c_ε := ψ(a, s_j + ε) ∈ ℂ{ε} ⊂ ℂ[[ε]].
  The base point at x = a is (Y'(a, s_j + ε), s_j), also in ℂ{ε}.
  - *Joint analyticity.* Let V := U^{1/e}. The equation ψ(x, s + ε) = c_ε becomes
    Θ := V(x, s+ε)(s + ε − σ(x)) − V(a, s_j+ε)·ε = 0, choosing the branch ω = 1 of the e-th root, which is consistent at x = a.
    Θ(a, ε, s_j) ≡ 0 and ∂_s Θ(a, 0, s_j) = V(a, s_j) ≠ 0. By the implicit function theorem in (x, ε, s) there is a jointly
    analytic S(x, ε) with S(a, ε) = s_j and S(x, 0) = σ(x).
    So every T-coefficient of S(a + Tu, ε), and of the corresponding t-coordinate t_j^ε(a + Tu) (a linear function of
    (Y'(x, S + ε), S + ε)), lies in ℂ{ε}[u] ⊂ ℂ[[ε]][u]. At ε = 0 it equals the coefficient of t_j(a + Tu).
  - *Regularity over ℂ((ε)).* det D Ĝ_ε at the base point = det(D_{y'} G') · ∂_s ψ(a, s_j + ε), and
    ∂_s ψ(a, s_j + ε) = e·U(a, s_j)·ε^{e−1} + O(ε^e) ≠ 0 in ℂ((ε)). This uses char 0.
    So the chord iteration with the constant J_ε^{−1} ∈ ℂ((ε))^{(m+1)×(m+1)} converges T-adically, as in §4.2. The T-adic
    contraction does not depend on ε-valuations.
    By uniqueness of Hensel lifting in ℂ((ε))[u][[T]], the truncated iterates equal the truncation of the analytic branch.
    Their coefficients therefore lie in ℂ[[ε]][u], although intermediate quantities (J_ε^{−1}) have poles.
  - *Output.* h_d(b) ∏_j (−t_j^ε) reassembled at u = x − a gives h(x) + ε·g̃(x) with g̃ ∈ ℂ[[ε]][x]. This is an approximating
    circuit in the sense of [T26] Def. N.1, which allows k((ε)) constants. By [T26] Lemma N.2 these can be replaced by Laurent
    polynomials, and Bürgisser's k(ε) model is equivalent for the present purpose. The cost is as in §4.2. ∎
- **Does the conclusion hold for h itself or only for a multiple?** For h itself. In low degree there is no cofactor problem:
  the product of the d tracked branches is h, up to the constant h_d(b)(−1)^d.

### 4.4 The general case κ ≥ 2: what fails, and the precise open problem
**The naive multi-dimensional perturbation provably fails.** Take
G(x; y₁, y₂) = (y₁² − x y₂, y₂), with Ŵ = {y = 0}, perturbed as G(x, y) = G(a, z + εv) at a = 0. The branch is
y₁ = ε v₁ (1 + x v₂/(ε v₁²))^{1/2}, whose x²-coefficient is −v₂²/(8 ε v₁³) ∉ ℂ[[ε]]. (This example actually has κ = 1, and the
method of §4.3 handles it by first solving y₂ = 0.)

The general reason: for κ ≥ 2 the discriminant Δ_x ⊂ ℂ^κ of the fibre map moves with x. A perturbation curve ε ↦ c_ε meets
Δ_x at parameters ε(x) → 0 as x → a, so the radius of analyticity in x shrinks to 0 and Taylor coefficients acquire ε-poles.
For κ = 1, Δ_x = {0} for all x, which is why Bürgisser's trick works there.

Exactly what remains: **Problem L\***. Let G : ℂ^n × ℂ^{m+1} → ℂ^{m+1} have L(G) ≤ s. Let Ŵ be a component of V(G) that is
étale of degree 1 locally over x, along which the fibre scheme is a complete-intersection fat point of embedding dimension
κ ≥ 2 and arbitrary length μ (μ can be 2^{Ω(s)}). Is the branch ζ(a + Tu) mod T^{d+1} border-computable with poly(s, d)
operations?

What I can say about it:
- (i) The **trace** μ·t_j(x) = Tr_{A_x}(t) is analytic in x and is the sum of the t-values over the μ branches of
  G = εc. That gives L̄ ≤ poly(s, d, μ) **if** the branches can be tracked individually with bounded ε-poles. I could not
  prove even this.
- (ii) Iterated **deflation** (Leykin–Verschelde–Zhao) makes the root regular in fewer than μ steps, but each step roughly
  doubles the system. That gives a bound exponential in μ (from memory; not pursued).
- (iii) No reformulation of the verifier changes the scheme. Tseitin-style auxiliary gate variables give an isomorphic
  scheme, and squaring a test raises the defect for free. So the defect is a property of the verifier, not of A. A proof of C1
  must handle κ ≥ 2 or show how to reduce the defect of any verifier at polynomial cost.

**Conjecture C1 [C].** Lemma L holds without the defect hypothesis. Then graph(per) ∉ NP_ℂ(nu), NP_ℂ ≠ PAR_ℂ, and
coNP_ℂ ≠ PAR_ℂ (complements). I believe it, but this notebook contains no proof.

### 4.5 Danger points from the brief, resolved
- **Witnesses of unbounded algebraic degree.** Harmless: Newton never uses deg W or deg q, only L(q) and the truncation
  order d.
- **Reducible fibres.** Harmless: choose one dominating component W and one fibre point over each x_j. Extra components are
  avoided by genericity (§4.1, (a)).
- **Non-reduced fibres.** Harmless when κ ≤ 1. Multiplicity e enters only through ε^{e−1} in J_ε and costs nothing. Open
  when κ ≥ 2 (§4.4).
- **h versus a multiple.** We get h itself (§4.3).
- **Inequations.** Harmless: W ⊄ V(q') and generic points avoid V(q').
- **Advice.** d complex fibre points, J^{−1}, and c_ε ∈ ℂ{ε} are constants. That is legitimate in nonuniform and border
  models, with constants in k((ε)) per [T26].

### 4.6 Sanity check (det)
A = Z(det_N) is in NP_ℂ via the verifier "∃w : Xw = 0, c·w = 1". It is reduced: the w-Jacobian [X; cᵀ] has rank N at a
generic corank-1 matrix, so κ = 0.
- Script `lemmaL_det_check.py` (numpy; N = 4, d = 4; random complex A, B and direction U; random real c) runs the
  chord iteration of §4.2 (d + 1 steps, constant J_j^{−1}) for each of the d branches in ℂ[[T]]/T^{d+1}. It compares
  det(B)·∏(−t_j) with det(A + TU).
- **Result: max |coefficient difference| = 1.0e−10, for coefficients of size about 38.** The reduced-case construction
  works as claimed on det. This is a numerical check of the algebra, not a proof. Since the identity is polynomial in U, a
  random U tests it generically.

---------------------------------------------------------------------------------------------------------------------

## 5. Corollaries, numbered

**T6 [R].** If a verifier of size s for graph(per_m) or PERZERO_m has, at some leaf, a dominating witness component of
defect ≤ 1, then s ≥ m^{(c/2)(log m)^{1/3} − 2} for large m.
Proof. T5 gives L̄(y − per) ≤ K d³ log d · m s ≤ K m³ log m · s², since m_wit ≤ s. Setting y = 0 gives L̄(per) ≤ that. Then
use [T26]. ∎
In words: any small NP_ℂ verifier for the permanent's graph must be "fat" (defect ≥ 2) on every dominating witness
component. In particular graph(per) ∉ **NP_ℂ^{reg}(nu)**, the subclass of verifiers whose leaf varieties are generically
reduced. This subclass contains every verifier that certifies nondegenerate solutions, for example by also checking that a
maximal minor of the Jacobian is nonzero. An example is the natural verifier "∃ eigen/kernel data" that works for det.

**T7 [R] (barrier).** A hypersurface family Z(h_n) of polynomially bounded degree that lies in NP_ℂ(nu) with a
defect-≤ 1 verifier is border-easy (exactly easy if defect 0). So a "generic-path" proof of P_ℂ ≠ NP_ℂ cannot use a
low-degree border-hard hypersurface with such a verifier. It must use hypersurfaces of superpolynomial degree, which is
precisely where the cofactor problem (idea 2) lives, or verifiers with defect ≥ 2. Under C1 the barrier is unconditional.

**T8 [K→R]** (the T1–T3 analogues). Every one of the following follows from T1:
- (i) PAR⁰_ℂ ⊄ P_ℂ(nu).
- (ii) EXP_ℂ ⊄ P_ℂ(nu). P_ℂ ≠ EXP_ℂ was already known by degree arguments; the nonuniform version with polynomial-degree
  hard instances is new by the same corollary.
- (iii) The same over ℝ.
- (iv) Randomized versions (BPP_ℂ ⊉ PAR_ℂ in the tree sense of [B04] Cor. 1.5). CKKLW (BPP_ℝ ⊆ P_ℝ/poly) gives the
  same for coin-tossing machines over ℝ [K, wording unverified].
- (v) The function problem: per ∉ FP_ℂ(nu) is trivially weaker than [T26]. The new content is that even *checking* is hard.

**T9 [C].** In char p > 0: P_{F̄_p} ≠ PAR_{F̄_p} via graph(HC_m). This needs a char-p version of [B04] Prop. 3.4 for graphs.
The obstruction is multiplicities divisible by p, where (Y − ϕ)^{p^a} = Y^{p^a} − ϕ^{(p^a)}(X^{p^a}).

---------------------------------------------------------------------------------------------------------------------

## 6. What does NOT follow, and why

1. **P_ℂ ≠ NP_ℂ does not follow.**
   - [B04]'s bridge from decision to computation is polynomial in the degree of the hypersurface. NP_ℂ-sets not known to be in
     P_ℂ (HN_ℂ, Twenty Questions, knapsack norms N_g, resultants) have exclusion polynomials of exponential degree.
   - P_ℂ(nu) = NP_ℂ(nu) would only produce an easy *multiple* of an exponential-degree polynomial (the resultant or N_g).
     [T26] says nothing about multiples: x^{2^n} − 1 is easy but has hard factors.
   - Lemma L shows the low-degree route is closed for curvilinear verifiers (T7). This is Bürgisser's Conjecture 1.1, still
     open.
2. **NP_ℂ ≠ PAR_ℂ is not proved.** It needs C1.
3. **No Boolean consequences.** Nothing about P vs NP, P/poly vs PSPACE, or NP ⊄ BPP. Separations of P from PAR in
   *additive* real models are tied to Boolean P/poly vs PSPACE-type statements (Fournier–Koiran 1997/98, abstract: a
   superpolynomial lower bound for real knapsack circuits would imply P ≠ PSPACE). Our separation uses multiplication
   essentially, through the permanent, and does not touch the additive model.
4. **Nothing about the τ-conjecture, factorials, or HN_ℂ ∉ P_ℂ.** [T26] makes [B26]'s Theorem 1.1 vacuous; it does not invert
   it.
5. **Uniform consequences beyond T3** are not claimed. For example, P_ℂ ≠ NC^?_ℂ-type separations inside PAR need nothing
   new, and PH_ℂ vs PAR_ℂ is open.

---------------------------------------------------------------------------------------------------------------------

## 7. Run log
- §4.6 script: `python3 -I research/next/y1/lemmaL_det_check.py` gives "max |coef diff| = 1.014e-10 (coef sizes ~ 3.8e+01)".
- Web searches (24 Nov 2026): no posting of the unconditional P_ℂ ≠ PAR_ℂ / P_ℝ ≠ PAR_ℝ corollary was found, and no claim
  of graph(per) ∉ NP_ℂ was found. The arXiv abstract pages of [B04], [B26], [B24] and [KP07] were read in full text.
- Not verified first-hand: the CKKLW theorem statement (abstract only); BCSS's proof of NP_ℂ ⊆ PAR_ℂ (cited through [KP07]);
  the proof of [B04] Lemma 1.1 (statement only).
