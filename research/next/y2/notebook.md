# y2 notebook: P_ℂ ≠ NP_ℂ via the cofactor problem for Boolean norms

24 Nov 2026. Input: `research/next/ideas-pc-npc.md` (§1.3–1.4, Idea 2). Tags: **[R]** proved here (full proof given),
**[K]** known (cited), **[N]** checked by computer (`checks.py`, sympy, exact), **[C]** conjecture / heuristic.
[T26] = the Nov 2026 border bound (paper.txt Thm 1.4 = Thm N.5): over every field, every circuit over k((ε)) that
*approximates* HC_m (resp. PERM_m when char ≠ 2) in the sense of Def. 1.3 has more than m^{c(log m)^{1/3}} gates.
Circuits use +, −, ×, and constants are free. Degree is unbounded.

## 0. Summary

| # | statement | status |
|---|---|---|
| L1 | P_ℂ(nu)=NP_ℂ(nu) ⇒ EC(N_g) ≤ 5T+2n+O(1) for every p-family g. No irreducibility is needed, because every component y=g_e(x) is a graph. | [R] §1 |
| L2 | L̄(S_g) ≤ L(N_g)+3 (border, via one constant δ^D). Exactly: L(S_g) ≤ O(d²)(L(N_g)+m) for g homogeneous of x-degree d. The reversal y ↦ −1/t costs nothing in the border model, and the homogeneity trick avoids the degree 2^n in the exact model. | [R] §2, [N] |
| L3 | **Cofactor lemma.** If Q = N_g·H ≠ 0, then L̄(S_g) ≤ O(d²)(L(Q)+L(H)+m). No condition on H(0,·), on ord H or on deg H. Ryser g + [T26]: **every easy multiple of N_g has a border-hard cofactor.** | [R] §3, [N] |
| L4 | **Artinian obstruction.** Let I be any ideal of finite colength r. Then N_g·(ℂ[x,y]/I) = Q'·(ℂ[x,y]/I) for an *easy* product Q' of ≤ r branches. So no argument that only looks at Q mod I (Hensel/Newton at points, fat points, truncations) can prove Gap G. | [R] §4 |
| L5 | Along the collapse line {x=0} (non-Artinian truncation), the hard information *is* present: the Weierstrass polynomial of Q at the origin equals N_g whenever H(0,0)≠0. Reading it off is a residue / high-order coefficient extraction, which is a VNP-type operation. | [R] (statement) + [C] (cost) §5 |
| L6 | **Span reduction.** Gap G (hence P_ℂ(nu) ≠ NP_ℂ(nu)) follows from the *Span Conjecture*: the polynomial roots in y of degree ≤ d of a size-s polynomial Q(x,y) span a space of dimension ≤ poly(s,d). The Boolean-indexed form suffices. It passes all sanity checks: char-2 Knapsack/Moore, roots of unity, cyclic and Dickson norms, and companion-power resultants all have span ≤ cost. | [R] reduction, [C] conjecture §6 |
| — | Weakest separation target asked by lead: explicit families all of whose multiples are hard. | §7 |

Directions are always "hypothesis ⇒ conclusion" as written. Nothing here proves P_ℂ ≠ NP_ℂ. The gap is restated in §6 as one
clean conjecture of τ type over ℂ[x].

## 1. The reduction (task 1)

**Setting.** g = (g_n(x,e)), x ∈ ℂ^m, e ∈ ℂ^n, m = n^{O(1)}, g_n with circuits of size n^{O(1)} (constant-free and uniform in
the Ryser case below). D = 2^n, g_e := g_n(x,e) for e ∈ {0,1}^n, N_g := ∏_e (y − g_e) ∈ ℂ[x,y].
A_g := {(x,y) ∈ ℂ^{m+1} : ∃e ∈ {0,1}^n, y = g(x,e)} = Z(N_g).

**A_g ∈ NP_ℂ** [R]: witness e ∈ ℂ^n. The verifier checks e_i² − e_i = 0 for all i (forcing e ∈ {0,1}^n) and y − g(x,e) = 0.
That is n+1 equality tests after a poly-size evaluation. It is digital (Boolean witness), uniform and constant-free when g is.
So uniform P_ℂ = NP_ℂ ⇒ P_ℂ(nu) = NP_ℂ(nu) ⇒ A_g decided by algebraic computation trees of depth T = n^{O(1)}. A circuit
with selection gates, or a time-T BSS machine on inputs of size m+1, unrolls into such a tree. Ops are +, −, ×, ÷, constants
from ℂ and tests "f = 0?". WLOG every divisor is tested ≠ 0 before division (this at most doubles the depth).

**Lemma 1 [R].** Let a computation tree of depth T decide A_g. Then there is a nonzero P ∈ ℂ[x,y] with L(P) ≤ 5T and
N_g^{red} | P, where N_g^{red} = ∏ over distinct g_e. Hence Q := P^{2^{n}} ≠ 0 satisfies N_g | Q, with L(Q) ≤ 5T + n and
deg Q ≤ 2^{O(T)}. In particular EC(N_g) ≤ 5T + n.

*Proof.* Define the *generic path*: start at the root and carry along each node's value as a rational function of the input
z = (x,y). At a test node with value f: if f ≡ 0, follow "= 0", otherwise follow "≠ 0". Division only happens by f ≢ 0. So
the values along the path are well-defined rational functions. Write each one as num/den with polynomials, using
(a,b)±(c,d) = (ad±bc, bd), (a,b)·(c,d) = (ac,bd), (a,b)/(c,d) = (ad,bc). Every den is a product of nonzero polynomials, so
it is nonzero. This uses ≤ 3 multiplications/additions per node, so ≤ 3T gates for all numerators and denominators. Let
P := ∏ (numerators of the tested f ≢ 0) · ∏ (all denominators). That adds ≤ 2T gates, P ≠ 0, and L(P) ≤ 5T.

Every input z with P(z) ≠ 0 follows the generic path. Its values are defined (dens ≠ 0), tests with f ≢ 0 give f(z) ≠ 0,
and tests with f ≡ 0 give 0. So all of ℂ^{m+1} ∖ Z(P) reaches one leaf. That leaf rejects: otherwise the dense set
ℂ^{m+1}∖Z(P) would lie in the proper closed set A_g. Hence A_g ∩ (ℂ^{m+1}∖Z(P)) = ∅, i.e. Z(N_g) ⊆ Z(P). Each factor y − g_e
is irreducible (degree 1 in y, monic), so by the Nullstellensatz each one divides P, and the distinct ones divide P
together. The multiplicity of any factor in N_g is ≤ D = 2^n, so N_g | P^{D}, at the cost of n squarings. □

*Remarks.* (i) Irreducibility of N_g over ℂ(x) plays no role: N_g splits into linear factors over ℂ[x] by construction.
The idea file's requirement "make the monodromy transitive" is only relevant if one uses resultants instead of Boolean
norms. (ii) The same proof gives a multiple of the norm of *any* poly-time-describable subset {e : φ(e)}. (iii) What is
thrown away: the tree must also *reject* Z(H) ∖ Z(N_g) off the generic path. Lemma 1 does not use that.

**Choice of g (Ryser).** g(X,e) := (−1)^n ∏_j(1 − 2e_j) · ∏_i (Σ_j X_ij e_j), with x = X ∈ ℂ^{n×n}, m = n², d = n.
This is constant-free, of size O(n²), and homogeneous of degree n in X. Its sum is S_g := Σ_e g_e = per_n, by Ryser's
formula ([N] n = 2,3). The distinct nonzero roots are ±∏_i(Σ_{j∈E}X_ij) for E ≠ ∅ (g_0 = 0). In characteristic 2 use instead
a homogeneous VNP-representation of HC_n: take the degree-n homogeneous part in x of Valiant's g, which costs poly(n).

## 2. N_g is hard (task 2)

**Lemma 2 [R].** Let S_g := Σ_e g_e.
(a) The coefficient of y^{D−1} in N_g is −S_g.
(b) (border) L̄(S_g) ≤ L(N_g) + 3, and more generally L̄(S_g) ≤ L̄(N_g) + 3.
(c) (exact) If g is homogeneous of degree d in x, then L(S_g) ≤ c·d²·(L(N_g) + m).

*Proof.* (b) Over ℂ[δ^{±1}], evaluate the circuit Γ for N_g at y = −1/δ (a constant) and multiply by the constant (−δ)^D. The
result is exactly F(x,δ) := ∏_e(1 + δg_e) = 1 + δS_g + δ²(…), a polynomial in δ and x. Subtract 1 and multiply by the
constant δ^{−1}. That gives S_g + δ·G with G ∈ ℂ[δ][x], i.e. an approximating circuit in the sense of [T26] Def. 1.3, with
3 extra gates. The degree D only enters through the single constant (−δ)^D, which is free. If Γ itself approximates N_g with
parameter η, substitute η = δ^K for K larger than the order of the poles. This is the standard composition of border
parameters. (c) By homogeneity N_g(εx, 1) = ∏_e(1 − ε^d g_e(x)) = 1 − ε^d S_g + O(ε^{2d}). Evaluate Γ at (εx, 1) in
ℂ[x][ε]/(ε^{d+1}). Each gate becomes d+1 polynomials, at O(d²) cost per multiplication, and scaling the inputs costs m.
Read off the ε^d coefficient. □ [N]: (a),(b),(c) checked exactly for n = 2, 3.

**Correction to the idea file (R1).** "y = −1/t … a circuit for F gives one for S_g" needs a circuit for the *reversed*
polynomial F. In the exact model, reversing a circuit for N_g costs the degree. (b) shows the reversal is free *only in the
border model*, and (c) gives an exact alternative of cost O(d²). Both suffice with [T26].

**Corollary [R + T26].** For Ryser g: L̄(N_g) ≥ n^{c(log n)^{1/3}} − 3, and exactly L(N_g) ≥ n^{c(log n)^{1/3}}/O(n²) − n².

## 3. The cofactor lemma (task 3(i), R4 made rigorous)

**Lemma 3 [R].** Let Q = N_g·H with H ≠ 0. Let g be homogeneous of degree d in x, or more generally let S_g have degree ≤ d.
Then L̄(S_g) ≤ c·d²·(L(Q) + L(H) + m). The same holds with L̄(Q), L̄(H) in place of L(Q), L(H) (compose border parameters).

*Proof.* Let K = ℂ((δ)). Over K, consider the rational function

  R_δ(x) := ((−δ)^D Q(x,−1/δ) / H(x,−1/δ) − 1)/δ = (F(x,δ) − 1)/δ = S_g + δ·G(x,δ),  G ∈ ℂ[δ][x].

It is computed by the circuits for Q and H, with the constants −1/δ, (−δ)^D, δ^{−1} and one division, in L(Q)+L(H)+O(1)
gates. The division is exact as rational functions, because Q/H = N_g. H(x,y) ≠ 0, so H(a,y) ≢ 0 for generic a ∈ ℂ^m,
hence H(a,−1/δ) ≠ 0 in K. Fix such an a and apply Strassen's division elimination around a (Strassen 1973, Vermeidung von
Divisionen; Bürgisser–Clausen–Shokrollahi Thm 7.1). Carry every gate as its Taylor expansion in z = x − a, truncated at total
degree d. A ± or × costs O(d²) operations on homogeneous components, and division by a series whose constant term is a
nonzero element of K costs O(d²). The output is the degree-≤d truncation of R_δ(a+z), which is
trunc_d(S_g(a+z)) + δ·trunc_d(G(a+z,δ)) = S_g(a+z) + δ·G̃ with G̃ ∈ ℂ[δ][z]. So S_g is approximated with
O(d²(L(Q)+L(H)+m)) gates. Re-substitute z = x − a with m gates. The intermediate degrees (up to 2^{L}) never enter: only the
*output* degree d does, which is the point of Strassen's method. □ [N] n = 2 with a random H.

**Corollary 3.1 [R + T26].** For Ryser g and every nonzero multiple Q = N_g·H:
L(Q) + L̄(H) ≥ n^{c(log n)^{1/3}}/O(n²) − n². So if P_ℂ(nu) = NP_ℂ(nu), the cofactor H from Lemma 1 is border-hard
(superpolynomial L̄), while Q is easy.

**Corollary 3.2 [R + K].** In the same situation, H is not a product ∏_{i≤r} h_i^{a_i} with r and all deg h_i polynomial.
*Proof:* each h_i | Q. By Bürgisser, FoCM 4 (2004), Thm 1.3 (as recorded in ideas file B11: L̄(h) ≤ poly(EC(h), deg h)
in char 0, independent of the multiplicity), L̄(h_i) ≤ poly(L(Q), deg h_i). Powers cost log a_i ≤ log deg Q ≤ O(T), so
L̄(H) ≤ r·poly. □ So an easy multiple needs a "complementary hard" cofactor with superpolynomially many factors, or one
factor of superpolynomial degree, as for X^D − 1 versus half its roots.

**What survives multiplication by an arbitrary H (task 3(i)).** Every quantity computed from Q by a cheap *linear* or
*local* operation is additive in log: log Q = log N_g + log H. Power sums p_k(N) = Σ_e g_e^k appear only as
p_k(roots of Q) − p_k(roots of H). Symmetric functions of the roots of N_g alone are *not* functions of Q. The only
invariants of Q that do not depend on H are ideal-theoretic: Z(N_g) ⊆ Z(Q), and orders of vanishing along each branch.
Newton tracking of one branch y = g_e(x) from Q is possible: Newton iteration on Q at a simple point of the branch gives
g_e in poly(L(Q),d). Bürgisser's theorem gives it even at multiple points. But one root is in VP anyway (§0 of the task),
so that is no contradiction. The contradiction has to come from the whole root *set*. §6 turns this into a statement about
its linear span.

## 4. Obstruction: Artinian truncations cannot work (task 3(ii), negative half)

The suggested route was: "restrict Q to a subvariety W where the multiple has polynomial degree / truncate modulo a power of
an ideal / Hensel at a point". It splits as follows.

**(a) No positive-dimensional W works [R].** If dim W ≥ 1, pick ℓ ∈ ℂ[x,y] that is nonconstant on W. Then
Q·(1 + ℓ^{2^s}) is again an easy multiple of N_g, of size s + O(s), and its degree on W is ≥ 2^s. So "deg(Q|_W) polynomially
bounded for every small-circuit Q" holds only for dim W = 0. The finite-dimensional quotients ℂ[x,y]/I (fat points) are
exactly the cases where cheap evaluation is possible: computing Q mod I costs poly(colength)·L(Q).

**Lemma 4 (Artinian obstruction) [R].** Let I ⊂ ℂ[x,y] have finite colength r, with A := ℂ[x,y]/I. Then there is
E' ⊆ {0,1}^n with |E'| ≤ r such that Q' := ∏_{e∈E'}(y − g_e) satisfies N_g·A = Q'·A. In particular
L(Q') ≤ r(L(g)+2). So every property of Q that depends only on the ideal (Q mod I)·A, or on membership Q mod I ∈ N_g·A, is
shared by an easy polynomial Q'. Q' is not a multiple of N_g, but it is indistinguishable from one modulo I.

*Proof.* By CRT, A = ∏_p A_p over the finitely many support points p. Each A_p is local Artinian with maximal ideal
m_p and length r_p, with Σ r_p = r and m_p^{r_p} = 0. Group equal roots: N_g = ∏_ρ (y − ρ)^{ν(ρ)} over the distinct
polynomials ρ among the g_e. Let E_p := {ρ : ρ(x_p) = y_p}. For ρ ∉ E_p, y − ρ is a unit in A_p. So
N_g·A_p = N_p·A_p with N_p := ∏_{ρ∈E_p}(y−ρ)^{ν(ρ)}, and N_p ∈ m_p^{deg_y N_p}.

Choose exponents μ_p(ρ) ≤ ν(ρ) for ρ ∈ E_p as follows.
- If Σ_{E_p} ν < r_p, take μ_p = ν on E_p ("full" at p).
- Otherwise take any μ_p with Σ μ_p = r_p ("saturated" at p).

Put μ(ρ) := max_p μ_p(ρ) ≤ ν(ρ) and Q' := ∏_ρ (y−ρ)^{μ(ρ)}. Then deg_y Q' ≤ Σ_p r_p = r, and L(Q') ≤ r(L(g)+2), since
each ρ is some g_e. At a point p:
- If p is full, then μ(ρ) = ν(ρ) on E_p, so Q' = N_p·(unit) in A_p.
- If p is saturated, Q' has ≥ r_p factors in m_p, so Q' = 0 = N_p in A_p, since N_p ∈ m_p^{r_p}.

Hence N_g·A_p = Q'·A_p for every p, and N_g·A = Q'·A. □

**Reading.** Locally, a multiple of N_g carries exactly the information "which ≤ r branches pass through the support,
with multiplicity". That is a product of ≤ r VP polynomials. The hard part (S_g = sum over *all* 2^n branches) is invisible
to any finite-colength truncation. This strengthens the idea file's §1.4(c), which only covered points where N_g is a unit.
Any proof of Gap G must use the *global polynomiality* of H at degree ≥ D.

## 5. The collapse line: where the information is, and why it is expensive

g is homogeneous, so all branches meet at x = 0: N_g(0,y) = y^D. Truncate along the line {x = 0} only, i.e. work in
R[y] with R := ℂ[x]/(x)^k. This ideal does not have finite colength.

**Lemma 5 [R].** (a) In R[y], N_g ≡ y^{D−J}·Ñ with J = ⌊(k−1)/d⌋ and Ñ = Σ_{j≤J}(−1)^j e_j(g) y^{J−j} monic. The ideal
(N_g mod x^k) ⊂ R[y] has a *unique* monic generator of minimal degree, namely y^{D−J}Ñ. So the ideal determines
e_1(g) = S_g, …, e_J(g) mod x^k: hard information, unlike in Lemma 4. (b) If H(0,0) ≠ 0, then N_g is the Weierstrass
polynomial (in y, over ℂ[[x]]) of Q = N_g·H at the origin. If ord_y H(0,y) = a > 0, the Weierstrass polynomial of Q is
N_g·W_H with deg W_H = a.

*Proof.* (a) g_e ∈ (x)^d, so products of > J roots vanish mod x^k. If two monic generators u, u' of the same degree J'
generate the same ideal, then u − u' has degree < J' and lies in (u), and every nonzero multiple of a monic u has degree
≥ J'. (b) N_g is monic in y and its lower coefficients lie in (x), so it is a Weierstrass polynomial. H(0,0) ≠ 0 makes H a
unit in ℂ[[x,y]], and Weierstrass preparation is unique. □

**[C] Cost.** Extracting e_1 of the Weierstrass factor of an easy Q is the trace over the "small" roots. That is the
coefficient of y^{−2} in the Laurent expansion of ∂_y log Q in an annulus, i.e. a residue or high-order coefficient
extraction. Valiant-style coefficient extraction is VNP-complete in general. So the hard information sits behind exactly
the VNP-type operation one cannot afford. This is the precise sense of "the cofactor is the whole problem": for N_g itself
(H = 1), Lemma 2 reads the same coefficient off cheaply, because N_g is a unit at (0, ∞), i.e. at y = −1/δ. For Q, the point
y = ∞ is contaminated by H's large roots, and the origin by H's small roots, unless H(0,0) ≠ 0. Even then the separation
costs the exponential order D.

## 6. Span reduction: one clean sufficient conjecture (task 4, positive half)

For Q ∈ ℂ[x,y] let Roots_d(Q) := {r ∈ ℂ[x]_{≤d} : Q(x, r(x)) = 0}.

**Span Conjecture [C].** There is a polynomial p with dim_ℂ span Roots_d(Q) ≤ p(L(Q), d) for all Q ≠ 0.
**Boolean-indexed form [C].** If L(Q) ≤ s, g has size ≤ s and g_e ∈ Roots_d(Q) for all e ∈ {0,1}^n, then
dim span{g_e} ≤ p(s, d, n).

**Lemma 6 [R].** The Boolean-indexed Span Conjecture + [T26] ⇒ EC(N_g) is superpolynomial for Ryser g ⇒ (Lemma 1)
P_ℂ(nu) ≠ NP_ℂ(nu) ⇒ P_ℂ ≠ NP_ℂ.
*Proof.* Suppose N_g | Q with Q ≠ 0 and L(Q) = s. Then every g_e ∈ Roots_n(Q). Pick a basis g_{e_1},…,g_{e_r} of
span{g_e} from among the g_e, with r ≤ p(s+O(n²), n, n). Then per_n = S_g = Σ_k λ_k g_{e_k}, so
L(per_n) ≤ r·(L(g) + 2) = poly(s, n). This contradicts [T26] (even its exact, non-border form) unless s is superpolynomial. □

Conversely, [T26] already forces dim span{g_e} ≥ L(per_n)/O(n²): the root set of the Ryser norm has superpolynomially
large span. The conjecture says only easy polynomials have "small-span root sets".

**Sanity checks (lead's steer: test char 2 first).**
- (a) Char 2 Knapsack: N = ∏_{e∈F_2^n}(y − e·x) is a subspace (Moore) polynomial, easy [N for n = 3]. In char p,
  Knapsack divides the Moore polynomial of V = F_p-span(x_1..x_n), easy by P_{V+F_p v} = P_V^p − P_V(v)^{p−1}P_V
  [N, p = 3]. So Knapsack-norm multiples are easy in *every* positive characteristic, not only p = 2. Span: the
  K-span of V is n-dimensional ≤ cost. **The conjecture predicts nothing about Knapsack and is consistent.** Lemma 3 is
  likewise silent: S_knap = 2^{n−1}Σx_i, which is 0 in char 2 and easy in general. Where the char-≠2 / choice-of-g
  enters: only through S_g being hard ([T26] for per needs char ≠ 2; HC works in every char) and through span{g_e}
  being large. Neither Lemma 3 nor Lemma 6 can be fooled by Knapsack: both need dim span{g_e} superpolynomial,
  which Knapsack violates. The proof route **does not go through for char-2 Knapsack, as required.**
- (b) Roots of unity y^D − u^D: span 1.
- (c) Cyclic norms ∏_{j<M}(y − Φ(x,ζ^j)) with deg_T Φ = d': equal to ±Res_T(T^M−1, y−Φ(x,T)) = ±lc^M det(C^M − I),
  with C the d'×d' companion matrix. Cost poly(d')·log M [N for M = 8, d' = 2]. Span ≤ d'+1 ≤ cost.
  Dickson D_M(y, vw) − v^M − w^M (roots ζ^j v + ζ^{−j} w): span 2. Torus-weighted norms ∏_j(y − r(σ^j x)) with
  σ = diag(ζ^{w_i}): span ≤ number of distinct weights ≤ T-degree = cost parameter.
  Resultants Res_T(f(T), y − Σ_{i<m} x_i T^i) with f easy and of high degree (polynomial roots Σ x_i k^i at the roots k
  of f): easy via f(companion), span ≤ m.
  In every known construction, **span ≤ the cost parameter**. Spans are not counts: the counts of roots are exponential
  (y^D − x^D, Moore), so the naive "number of polynomial roots ≤ poly" analogue of τ is false over ℂ[x]. Span is the
  right analogue.
- (d) Test case where the conjecture says more than Gap G: the multiplicative Knapsack ∏_e(y − x^e) has span 2^n, but
  S = ∏(1+x_i) is easy. The conjecture predicts that it has no easy multiple. Its easy-multiple question contains the
  q-Pochhammer question ∏_{a<M}(y − q^a) (n = 1, box of exponents), a q-analogue of Shub–Smale. So the conjecture is
  strictly stronger than needed, and probably as hard as τ-type statements. It is not refuted by anything I found.

**Status of Gap G after this notebook.** Remaining = Span Conjecture (Boolean-indexed), or any statement forcing the roots
of an easy polynomial into a low-dimensional linear space. Lemma 3 alone narrows the gap only to "the cofactor is border-hard",
which is not contradictory by itself: X^D − 1 = (hard)·(hard) shows hard·hard = easy is possible.

## 7. Lead's question: explicit families all of whose multiples are provably hard

- **[R from K + T26]** Any family with a low-degree hard irreducible factor works: EC(f) ≥ L̄(h)/poly(deg h) for each
  irreducible factor h | f (Bürgisser 2004 Thm 1.3 / B11). Example: f = per_n·(anything). So EC(per_n) is superpolynomial.
  With Lemma 1's argument this gives {per = 0} ∉ P_ℂ(nu), hence P_ℂ ≠ PAR_ℂ (= ideas file R2). That is the known-route
  answer, and it is all polynomial-degree.
- **Exponential degree, unconditional?** Hardness of every multiple is lower-bounded by the hardness of each factor up to
  poly(degree). So for a family all of whose irreducible factors are easy (like N_g, whose factors are linear in y), *no*
  factor argument applies, and nothing in this notebook proves it. A cheap candidate: N_g·per? Trivial (it has a hard
  low-degree factor). The non-trivial target is exactly a family whose irreducible factors are all in VP but whose
  multiples are all hard. I know of **no** such explicit family over ℂ, even conditionally on [T26]. Shub–Smale's twenty
  questions (∏_{k≤K}(y−k)) is the τ-conjecture case. Lemma 6 shows such a family would follow from the Span Conjecture.
- Weak positive: by Lemma 3, for Ryser g the *pair* (Q, H) cannot both be easy. Equivalently, the 2-output problem
  "compute a nonzero multiple of N_g together with the cofactor" is hard. That separates P_ℂ(nu) from nothing by itself,
  because a decision machine is not obliged to know H.

## 8. Files

- `checks.py`: exact sympy checks of Lemma 2(a)(b)(c) for n = 2, 3; Lemma 3 for n = 2 (one division plus truncation
  around a random point); span dimensions; the Moore divisibility in char 2 and 3; the cyclic norm via companion powering.

## 9. Lead's brainstorm (1)–(5)

**(1) Calibrating the Span Conjecture [R].** Trivially dim span Roots_d(Q) ≤ dim ℂ[x]_{≤d} = C(m+d, d). For Ryser g
(m = n², d = n) this is n^{Θ(n)}, so for fixed d the conjecture holds with p = m^d, and all its content is at growing d.

*Weakest sufficient growth.* The proof of Lemma 6 gives L(per_n) ≤ r·(L(g)+2), with r ≤ p(s', n), s' = s + O(n²),
L(g) = O(n²). [T26] (exact form suffices) gives L(per_n) > n^{c(log n)^{1/3}}. So a contradiction for s = n^{k} follows from
p(n^{k}, n) ≤ n^{c(log n)^{1/3} − 3}. For example p(s,d) ≤ 2^{ε (log s)^{4/3}} · poly(d) works for every fixed k, once
ε < c/k^{4/3}. More cleanly, **p(s,d) = s^{o((log s)^{1/3})} · d^{O(1)} is enough**, so polynomial is not needed. A bound
of the form d^{o(d)} or m^{o(d)}, of shape like the trivial one, is **not** enough: with d = n, m = n², even
m^{(log n)^{1/3}} = n^{2(log n)^{1/3}} would be enough, but only for constant c > 2. The d-dependence must therefore be
sub-(log d)^{1/3}-in-the-exponent, i.e. barely above polynomial. Exponentially large spans (Moore-type, ≥ 2^{Ω(s)}) are the
thing to exclude.

**(2) Degenerations [R; one citation from memory].** Facts:
- (i) For any family Q_ε ∈ ℂ[ε][x,y], the lowest ε-order term is multiplicative, since ℂ[x,y][ε] is a domain:
  lt(Q_ε) = lt(N_ε)·lt(H_ε).
- (ii) In the border model, lt(Q∘A_ε) for a substitution A_ε (linear in (x,y) with entries in ℂ[ε^{±1}], or a torus
  weight) costs L(Q) + O((m+1)²), whatever the degree: ε^{−k}·Q(A_ε(x,y)) with the constant ε^{−k}.

So "N_g has a border-easy multiple" is preserved under every such degeneration, as the lead says. Also:
- (2a) **WLOG Q and H are multi-homogeneous** for every grading under which N_g is homogeneous. For Ryser g: one grading
  per row of X (y has weight 1 in each), plus the weighted grading (x:1, y:d). Take in_w for a generic weight. Column
  scalings do *not* stabilise Z(N_g), because row sums mix columns. So H may be assumed a semi-invariant of the
  (n+1)-dim torus. Semi-invariants of a torus are just multi-homogeneous polynomials, so this constrains almost nothing.
- (2b) **No degeneration produces a hard low-degree factor [R mod K].** By (i), lt(N_g∘A_ε) = ∏_e lt((y − g_e)∘A_ε).
  Each factor ℓ_e⁰ := lt((y−g_e)∘A_ε) has degree ≤ d (≥1) and L̄(ℓ_e⁰) ≤ L(g) + O(m²). By the closure of border-VP
  under factors of polynomial degree (Bürgisser, FoCM 2004, approximative version of Kaltofen; *from memory, to be
  checked*), every irreducible factor of the degenerate norm is border-easy. The degenerate hypersurface may stop being
  a union of graphs (an ℓ_e⁰ may lose y, or become non-reduced when branches merge). But its equation is still a product
  of 2^n limits of individually easy low-degree polynomials. **So the "merge branches into a hard irreducible limit"
  lever is closed**, for torus *and* non-torus one-parameter families: limits of products are products of limits. The
  only effect of a degeneration is to replace g_e by ℓ_e⁰. Simplest target: with the weight that keeps only one entry per
  row… every in_w(g_e) is a product of initial forms of row sums. Choosing w to single out column j_i(E) in row i gives
  ±∏_i X_{i,max(E)} = ±m_E, which is monomial-type. The norm then degenerates to products of (y ∓ monomial) factors with
  huge multiplicities. Its S is computable from the degeneration of per, which is a monomial/easy. *The degeneration
  kills the hardness of S along with everything else.* A degeneration in_w(N_g) whose S_{in_w g} is still hard (this
  needs in_w(per) hard) keeps Gap G for the degenerate g. No simplification was found that keeps S hard and makes the
  root set structured (e.g. ℂ-Knapsack needs S = linear, which is easy).

**(3) Symmetrisation [R, negative].** The stabiliser of Z(N_g) for Ryser g contains S_n (rows) × S_n (columns, acting on e)
× the row torus. Torus isotypic projection = initial forms is free in border (2a). Finite-group projections
Σ_σ χ(σ)σQ cost |G| = (n!)² gates: **not free**. In general they need not even be nonzero for a given χ. So invariant
theory can only use the torus, and torus semi-invariants are all multi-homogeneous H. **H = N_g^k·(monomial) cannot be
forced.** The "power" version of L3 does hold and needs only L(Q) [R]: if Q = c·x^β y^a N_g^k, then
(−δ)^{Dk+a}Q(x,−1/δ) = c x^β (1+δS+…)^k, so S ≈ ((…)/(c x^β) − 1)/(kδ). Division by the monomial is removed by Strassen
at a point with x ≠ 0, so L̄(S) ≤ O(d²)(L(Q)+m). It is useless unless the cofactor is forced to be of this shape.

**(4) Restricted models / function fields [C, partial].**
- *Curves kill the lever [R].* After x = γ(t), roots live in ℂ[t]_{≤d·deg γ}, which has span ≤ d·deg γ + 1. per∘γ is a
  univariate polynomial of polynomial degree with free constants, so it has L ≤ O(n deg γ). Restricting to curves
  destroys both the span and the hardness.
- *Restricted model where the Span route closes the loop.* Let SPARSE-BSS be the BSS machines whose **test polynomials**
  (as functions of the input) are t-sparse in (x,y) for t = poly, with arbitrary (exponential) exponents. In Lemma 1,
  P = ∏ tests and Roots(∏ f_i) = ∪ Roots(f_i), so span Roots_d(P) ≤ Σ_i span Roots_d(f_i). Hence:
  **sparse Span bound ⇒ A_g ∉ SPARSE-BSS-P for Ryser g (unconditional given [T26]), while A_g ∈ NP_ℂ.** The needed bound
  is: a t-sparse Q has dim span Roots_d(Q) ≤ (t d m)^{o((log)^{1/3})}.
- *Why counting fails and spans are needed:* y^D − x_1^D is 2-sparse with D roots ζ^j x_1, all of span 1.
- *Proof attempt via Brownawell–Masser (function-field S-unit equation, genus 0, over k(x_1) with
  k = closure of ℂ(x_2..x_m)).* For a root r, split Σ_k c_k x^{α_k} r^{a_k} = 0 into minimal vanishing blocks. B–M bounds
  the projective height of each block by C(t)·(|S|−2), with |S| ≤ deg r + #(zeros of the coefficients) + 1 ≤ d + O(t)
  for monomial coefficients. So each ratio u_k/u_l is an S-unit of height ≤ C(t)(d+t). Unique factorisation then gives:
  if a_k − a_l > C(t)(d+t), then r = λ·x^γ is a *monomial* with λ^{a_k−a_l} fixed, hence one ℂ-line per γ.
  Low-spread blocks give polynomials in y of degree ≤ C(t)(d+t), each with that many roots, over ≤ 2^t blocks.
  **Obstacle:** the number of admissible γ (|γ| ≤ d) is bounded only by the number of S-units of bounded height, i.e.
  by C(m+d,d)-type counts. Also λ ∈ k may depend on x_2..x_m, which is only controlled up to roots of unity. So the
  sketch gives span ≤ 2^t·C(t)(d+t) + #{monomial classes}. The second term needs an extra argument: each monomial class is
  determined by the pair (k,l) and the bounded-height exponent of the ratio, so plausibly ≤ t²·(C(t)(d+t))^{O(1)}. I did
  not close this within the time-box. **[C]: the sparse Span bound is true with p = 2^{O(t)}·poly(d); proving it would
  give the unconditional SPARSE-BSS separation above.** The 2^{O(t)} is fine only for t = O(log n). For t = poly one needs
  the Wronskian-type polynomial-in-t versions (Koiran–Portier–Tavenas style; not checked here).

**(5) §7 negative, updated.** (2b) cannot produce a family with all factors easy and all multiples hard, since
degenerations preserve "all irreducible factors border-easy". So the honest frontier statement stands: **no explicit
family is known (even given [T26]) whose irreducible factors are all border-easy and whose nonzero multiples are all
superpolynomially hard.** Gap G for Ryser g is exactly such a statement. The Span Conjecture is a sufficient structural
reason, verified on every known easy-multiple mechanism.
