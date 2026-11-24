# c2 notebook: corollaries of the "VP ≠ VNP over every field" bound

Helper c2. Date 2026-11-24. Files here: `notebook.md` (this file, the deliverable), `params.py` (parameter
checks; run `python3 -I params.py`), `params_output.txt` (its output), `comic.svg`.

Tags: **[R]** proved here, given the paper's Theorems 1.1/1.4. **[K]** known. **[C]** conjecture or open.

## 0. Input and conventions

**Hardness hypothesis (H)** is the paper's Thm 1.1 plus Thm 1.4 (= Thm M.3, N.5). It says there is an
absolute c > 0, and for each characteristic p an m0(p), such that over every field k of characteristic p and
for all m ≥ m0:

  L(HC_m) > S(m) := 2^{c (log m)^{4/3}} = m^{c (log m)^{1/3}},

and the same holds for PERM_m when p ≠ 2, and for approximating circuits (Def. 1.3: circuits over k((ε)) whose
output is f + εg with g ∈ k[[ε]][x]). Here L is the number of gates, counting inputs and constants; constants
are arbitrary, and there is no restriction on depth or on intermediate degree. log means log₂.

Facts about the constants, read from the paper:
- An explicit admissible value is c = 1600^{-4/3} ≈ 5.34·10⁻⁵ (Thm E.11 gives L > 2^{(log m/1600)^{4/3}} in the
  flat case). The contracting case gives the larger bound 2^{c'(log m)²/log log m} for large m (Thm K.7), so
  this c works in both cases for m ≥ m0. The paper itself prints the weaker 1/1600², and Thm M.3 says c is
  absolute.
- **m0 is ineffective** (§2.2, App. L remarks: it is not known which case holds, and in the contracting case μ
  has no value). Every corollary below therefore holds "for all sizes ≥ an ineffective threshold". The
  *constructions* (hitting sets, algorithms) are explicit; only the point from which they are correct is
  unknown.
- HC_m has m² variables (m² − m of them used), degree m, is multilinear with 0/1 coefficients, and is
  evaluable with O(2^m m²) field operations (Held–Karp dynamic programme over (subset, endpoint) with vertex 1
  fixed). Using HC instead of PERM makes everything work in characteristic 2 too.

## 1. Prior-art check (web search, 24 Nov 2026)

Searched: general web, Exa (arXiv/ECCC/blogs), Hexagon (hexagonmath.org/2611.00954v1), alphaXiv listing,
news coverage (kingy.ai, aiweekly, casrai, fourweekmba, anchorterminal, lilting.ch, interestingengineering).
- **No follow-up** deriving PIT, hitting-set, Noether-normalisation, or explicit dc / formula / depth
  corollaries was found. kingy.ai restates Remark N.6 qualitatively ("superpolynomial lower bound on the size of
  determinants ... including formal limits"). anchorterminal notes that the derandomisation question is open
  in the paper.
- **Concurrent claim:** OpenAI posted "VP and VNP are different" (openai/math repo, 24 Nov 2026 01:14 UTC,
  30 pp.), with a border-circuit bound exp(Ω((log n)^{5/4})) that is Lean-verified only for exact circuits.
  I have seen it only through news reports and have not read it. If it is correct, its exponent 5/4 is a weaker
  form than (log m)^{4/3}; all templates below take any hardness S(m) as input (see §2.6).
- Relevant recent work: Chukhin–Gajulapalli–Golovnev–Mihajlin, arXiv 2611.07972 (5 Nov 2026), "either
  NE ⊄ SIZE[2ⁿ/2n] or VP⁰_Z ≠ VNP⁰_Z". (H) makes its second disjunct true, so that theorem becomes vacuous;
  see Cor 9. Sheshadri 2610.40484 gives a cubic (border) dc in odd characteristic.
- Andrews, CCC 2020 (arXiv 2005.10885): the KI reconstruction in characteristic p returns g^{p^k}, not g.
  Taking p-th roots of multivariate circuits is stated there as open. This is the small-characteristic obstacle
  in §2.4.

Novelty verdict: the *method* in §2 is Kabanets–Impagliazzo 2004 (KI) with a standard root-finding lemma. That
is folklore once a hardness bound is available, so no single step is new. What is new is the instantiation:
an unconditional (given (H)) subexponential black-box PIT for general circuits, with explicit exponents and
with the all-fields and border variants. As far as the search shows, nobody has written this down.

## 2. PIT derandomisation

Notation: C(s,n,d; k) is the set of polynomials in k[x₁..x_n] of total degree ≤ d computed by some circuit over
k with ≤ s gates. The circuit may have huge intermediate degree; only the output degree is bounded.
\bar C(s,n,d; k) is the same with approximating circuits over k((ε)), where the ε⁰-part has degree ≤ d.

### 2.1 Generator

Let m be a parameter, ℓ = m², and q a prime with m² ≤ q ≤ 2m² (Bertrand). Let a = ⌈log n / log q⌉. Take the
universe [q]×[q], so t = q² ≤ 4m⁴ seed variables y. The design consists of the graphs
S_p = {(u, p(u)) : u ∈ F_q} of polynomials p ∈ F_q[u] with deg p ≤ a. There are q^{a+1} ≥ n of them,
|S_p| = q ≥ ℓ, and |S_p ∩ S_{p'}| ≤ a. Truncate each to its first ℓ points and pick n of them, S₁..S_n. Then

  G_m(y) := (HC_m(y|S₁), …, HC_m(y|S_n)),  deg G_m = m.

### 2.2 Reconstruction lemmas

**Lemma 1 (hybrid; [K], KI04).** Let 0 ≠ C ∈ C(s,n,d; k) with C∘G_m = 0, and let K ⊇ k be an infinite extension.
Then there are i ∈ [n] and a polynomial P(z, x) ∈ K[z, x], with z the ℓ variables y|S_i and x one variable,
such that:
- P ≠ 0 and P(z, HC_m(z)) = 0;
- deg_x P ≤ deg_{x_i} C ≤ d;
- P has a circuit with L_P ≤ s + n(a+2)2^a gates.

*Proof.* Let H_j = C(G₁..G_j, x_{j+1}..x_n). Then H₀ = C ≠ 0 and H_n = 0, so pick i with H_{i−1} ≠ 0 and
H_i = 0. Fix x_{j>i} and the y outside S_i to values in K that keep H_{i−1} ≠ 0 (Schwartz–Zippel over infinite
K). Then G_j for j < i becomes a multilinear polynomial in the ≤ a variables of S_i ∩ S_j. Such a polynomial has
≤ 2^a monomials, so a circuit with ≤ (a+2)2^a gates. Substituting x_i ↦ HC_m(z) gives the restriction of
H_i = 0. ∎

**Lemma 2 (simple-root extraction; [K] in essence, explicit form here).** Let P ∈ K[z,x] have a circuit of size L
and deg_x P ≤ e₀. Let f ∈ K[z] with deg f = D, P(z,f) = 0, and P ≠ 0. Suppose that the multiplicity e of the
factor (x − f) in P is not divisible by char K; this holds automatically if char K = 0 or char K > e₀. Then f
has a circuit over an extension of K with at most

  L_f ≤ 2(D+1)² ( D (L_Q + 3) + 1 ) + 2D²,  where L_Q = (e₀+1)L + 3(e₀+1)²,

gates.

*Proof.*
1. *Make the root simple.* Write P = (x−f)^e R with R(z,f) ≠ 0. The Hasse derivative Q = D_x^{(e−1)}P equals
   e(x−f)R + (x−f)²(…), so Q(z,f) = 0 and ∂_xQ(z,f) = e·R(z,f) ≠ 0. To compute Q, interpolate P in x at e₀+1
   distinct points of K: this needs (e₀+1) copies of P plus a (e₀+1)² linear map, then Horner. That gives
   L_Q gates.
2. *Recentre.* Choose b ∈ K^ℓ with ∂_xQ(b, f(b)) ≠ 0, set g(w) = f(w+b), u₀ = f(b), and
   γ = ∂_xQ(b,u₀)^{−1} ∈ K.
3. *Simplified Newton.* Set u_{j+1} = u_j − γ Q(w+b, u_j). If u_j ≡ g mod (w)^{j+1}, write u_j = g + h with
   h ∈ (w)^{j+1}. Then Q(w+b, g+h) = ∂_xQ(w+b,g)·h + O(h²), and ∂_xQ(w+b,g) ∈ γ^{−1} + (w). Hence
   u_{j+1} ≡ g mod (w)^{j+2}. After D steps, u_D ≡ g mod (w)^{D+1}, using D(L_Q+3)+1 gates. No degree control
   is needed, because the model does not restrict intermediate degrees.
4. *Truncate.* Strassen's homogenisation computes the homogeneous parts of degree ≤ D of every gate. It
   multiplies the size by ≤ 2(D+1)² and works for circuits of any degree. Summing them gives g; shifting back
   costs ℓ ≤ D² more gates. ∎

**Lemma 3 (border version; [R]).** Lemmas 1–2 hold verbatim for approximating circuits. If C_ε approximates C ≠ 0
and C∘G_m = 0, then HC_m is approximated by a circuit with the same bound L_f.

*Proof.* After Lemma N.2 of the paper, all outputs lie in k[[ε]][…]. Substituting exact polynomials, fixing
variables in K, interpolating with constants from K, and running the Newton map with γ computed from the ε⁰-part
are all k[[ε]]-linear or multiplicative operations. They preserve k[[ε]][…] and commute with reduction mod ε.
Mod ε the computation is exactly the one in Lemma 2, so the final output lies in HC_m + ε k[[ε]][z].
Interpolation is used only through its value mod ε, where deg_x ≤ e₀ holds. ∎

### 2.3 Main PIT corollary

**Corollary 1 [R] (hitting sets for VP in characteristic 0 and in large characteristic).** Assume (H).
- Fix n, d ≤ s, and choose m = m(s,d) as the least integer with
  c(log m)^{4/3} > log L_f(m,s,n,d). Here L_f is Lemma 2's bound with L = s + n(a+2)2^a, e₀ = d and D = m.
- Then log m = (1+o(1)) ((log s + log d)/c)^{3/4}.
- Let K be a field with char K = 0 or char K > d, and let A ⊆ K have |A| = dm+1 (pass to a finite extension if
  necessary).
- Then there is s₀ (ineffective) such that for all s ≥ s₀ the set H_s = G_m(A^t) ⊆ K^n is a hitting set for
  C(s,n,d; K) and for \bar C(s,n,d; K).

Its size is

  |H_s| = (dm+1)^t ≤ 2^{4m⁴ log(dm+1)} = 2^{2^{(4+o(1)) ((log s + log d)/c)^{3/4}}},

and for d ≤ s this is 2^{2^{(4·2^{3/4}+o(1)) c^{-3/4} (log s)^{3/4}}}. With c = 1600^{-4/3} the inner constant
is 4(2/c)^{3/4} ≈ 10763; `params.py` confirms the ratio to the asymptotic formula tends to 1.0001 at
log s = 10³⁰.

H_s is listed with |H_s| · n · O(2^m m²) field operations, and 2^m = |H_s|^{o(1)}. Consequently:

- **Black-box PIT** for size-s circuits of degree ≤ s in characteristic 0 or > s, with arbitrary constants, in
  deterministic time 2^{2^{O((log s)^{3/4})}} = 2^{s^{O((log s)^{−1/4})}} ⊆ ∩_{ε>0} DTIME(2^{s^ε}). Time is
  counted as field operations, times a polylog factor for extension arithmetic over finite fields.
- Over Q in the Boolean model this holds for circuits of formal degree ≤ s with s-bit constants (bit lengths
  stay poly(s, m)).

*Proof.* Suppose C ≠ 0 vanishes on H_s. Since deg(C∘G_m) ≤ dm < |A|, Schwartz–Zippel on the grid gives
C∘G_m = 0. By Lemma 1, applied over an infinite extension K' of K, there is P with deg_x P ≤ d < char K or
char K = 0, so the multiplicity is not divisible by the characteristic. Lemma 2 (resp. Lemma 3) gives an
(approximating) circuit for HC_m over K' with ≤ L_f < S(m) gates. If m ≥ m0, this contradicts (H) over K'.
Finally, m(s) → ∞, so m ≥ m0 for s ≥ s₀. ∎

*Numerics (`params_output.txt`, n = d = s):*
- H_s first beats the trivial (s+1)^s grid once log s > 3.5·10¹⁶.
- For smaller s the requirement is dominated by the m³ factor: the bound needs (log m)^{1/3} > 3/c, so
  log m ≳ 1.8·10¹⁴.

The statement is asymptotic and, because of m0, ineffective.

*Remarks.*
- The exponent 3/4 equals 1/(4/3): if L(HC_m) ≥ 2^{(log m)^{α}}, the same proof gives
  |H| = 2^{2^{O((log s)^{1/α})}}. With OpenAI's claimed α = 5/4 one gets (log s)^{4/5}.
- The factor 4 in front comes from seed length t ≈ ℓ² = m⁴. A design with t = O(ℓ²/a) changes only lower-order
  terms. A hard family with fewer variables per degree would lower it **[C]**.
- KI04 proved only "Perm ∉ VP ⇒ formula-PIT in subexponential time" (and gave nondeterministic converses). This
  corollary is the unconditional (mod (H)) instance with explicit exponents, for circuits, black-box, and for all
  fields of characteristic 0 or > d.
- GKSS19 (Guo–Kumar–Saptharishi–Solomon) and Andrews 2020 give much better hitting sets, but they need hardness
  d^δ for *constant-variate* polynomials. HC_m has only quasi-polynomial hardness in m, against 2^{Θ(m log m)}
  monomials. Kronecker-substituting it to a constant number of variables gives degree 2^{Θ(m² log m)} and
  hardness 2^{O((log m)^{4/3})}, far below d^δ. **So those generators do not apply.** KST19 bootstrapping needs
  barely non-trivial hitting sets for *constant* n, which Cor 1 does not provide either.

### 2.4 Positive characteristic

**Corollary 2 [R] (all characteristics, individual degree < p).** Let char K = p > 0, and let C^{<p}(s,n,d; K) be
the polynomials in C(s,n,d; K) of individual degree ≤ p−1 in every variable. This includes all multilinear
polynomials, for every p including 2.

Then the H_s of Corollary 1, built over an extension K' with |K'| > dm, is a hitting set for C^{<p}(s,n,d; K) and
its border analogue, for s ≥ s₀(p). The size bound is the same with e₀ = p−1 in place of d, so it is no worse.

*Proof.* In Lemma 1, deg_x P ≤ deg_{x_i} C ≤ p−1, so the multiplicity e ≤ p−1 is prime to p and Lemma 2 applies.
Interpolation uses the p points of F_p. Use HC_m, which needs no characteristic restriction. ∎

**Open [C] (general circuits in small characteristic).** For p ≤ d the reconstruction gives only a circuit for
HC_m^{p^k}(z) = HC_m(z^{p^k}) with p^k ≤ d (Andrews 2020, Lemma 4.2). (H) says nothing about HC_m(z^{p^k}), and
passing from a circuit for g^p to one for g is open for multivariate g. So **I could not derive hitting sets for
general degree-d circuits over F_p with d ≥ p.**

Two things would suffice:
- a lower bound S(m)/poly for HC_m(z^{q}) with q ≤ poly(m); or
- a VNP-hardness statement for a p-th-power-closed hard family.

Over finite fields the paper's bound is syntactic, so the "functional" route of Andrews (where g^{q^r} equals g
as a function) does not apply either.

### 2.5 Closure of VP: robust PIT and explicit Noether normalisation

**Corollary 3 [R].** Let K be algebraically closed with char 0 or > d. Let V_{s,n,d} be the Zariski closure in
K[x]_{≤d} of the cone K·C(s,n,d; K). This cone lies in C(s+2,n,d), and V is closed, irreducible components
aside.

Then for s ≥ s₀ the evaluation map ev_H : V_{s,n,d} → K^{H}, with H = H_{s+2}, satisfies
ev_H^{−1}(0) ∩ V = {0}. Equivalently, since V is an affine cone and ev_H is linear (graded Nakayama), the
coordinate ring K[V] is a finite module over the subalgebra generated by the |H| linear functionals
f ↦ f(h), h ∈ H. In words: an **explicit Noether-type normalising family of size 2^{2^{O((log s)^{3/4})}}**,
computable in time poly(|H|).

*Proof.* Over algebraically closed K, f ∈ V iff f is approximated (Def. 1.3) by a size-(s+2) circuit, by
Alder 1984 and Bürgisser 2004 (the curve-selection fact the paper quotes after Def. N.1). Then apply Lemma 3 /
Cor 1. ∎

*Special case (Mulmuley GCT V).* The variety Δ[det_w; n] is the closure of {det(A(x)) : A a w×w affine matrix
in n variables}. It lies in V_{s,n,w} with s = O(w^{2.70} + w²n). So it gets an explicit normalising set of
evaluation points of size 2^{2^{O((log wn)^{3/4})}}, constructible in deterministic time of the same order.

Comparison:
- Mulmuley (JAMS 2017) gave PSPACE (exponential time) unconditionally, and quasi-polynomial time conditional on
  black-box derandomisation of symbolic-determinant PIT.
- Forbes–Shpilka 2013 treat simultaneous conjugation.
- Guo–Saxena–Sinhababu 2018 construct poly-size hitting sets for \bar{VP} in PSPACE.

Cor 3 is the first *subexponential-time* explicit construction, given (H) **[R]**. It does not reach Mulmuley's
quasi-polynomial target **[C]**.

**Corollary 4 [R] (Edmonds' problem).**
- Given a w×w matrix A(x) of affine forms in n variables over K (char 0 or > w), its commutative rank,
  max_{x} rk A(x), is computable deterministically in time 2^{2^{O((log wn)^{3/4})}}.
- In particular SDIT (Edmonds' problem: is det A ≢ 0?) lies in deterministic time 2^{N^{o(1)}}, with
  N = w + n.

*Proof.* Every r×r minor has a circuit of size O(r^{2.70} + r²n) and degree r ≤ w. Take H hitting all of them;
then max_{h∈H} rk A(h) is the generic rank. ∎

Before this, the best deterministic algorithm for general SDIT was exponential **[K]**. Bipartite matching
and other special cases already have polynomial or quasi-NC algorithms, so Cor 4 is no improvement there.

### 2.6 Template for other hardness

**Template 5 [R].** If L(HC_m) ≥ T(m) for m ≥ m0 over K (char 0 or > d), then for s ≥ s₀,
H = G_m(A^t) with m = min{m : T(m) > L_f(m,s,n,d)} is a hitting set of size (dm+1)^{4m⁴}. Examples:
- T = 2^{c(log m)^{4/3}} (this paper) gives log log|H| ~ 4((log sd)/c)^{3/4};
- T = 2^{(log m)^{5/4}} (OpenAI claim) gives log log|H| ~ 4(log sd)^{4/5};
- an exponential T = 2^{m^δ} gives quasi-polynomial |H| = 2^{O((log s)^{4/δ}·log s)} [K, KI04].

## 3. Determinantal complexity

**Corollary 6 [R] (explicit form of Remark N.6).** Let k be a field and e_det the exponent of a division-free
determinant circuit valid over all commutative rings. One can take e_det = 2.697263 (Kaltofen–Villard 2004) or,
elementarily, e_det = 4 (Berkowitz 1984). Assume (H). Then for every ε > 0 and m ≥ m₁(ε, char k)
(ineffective):

  \bar{dc}(PERM_m) ≥ m^{(c/e_det − ε)(log m)^{1/3}}  (char k ≠ 2),
  \bar{dc}(HC_m) ≥ m^{(c/e_det − ε)(log m)^{1/3}}  (every k),

and the same for dc ≥ \bar{dc}. With c = 1600^{-4/3} and Kaltofen–Villard, the coefficient is
c/e_det ≈ 1.98·10⁻⁵.

*Proof.* Suppose PERM_m + εg = det A, where A is n×n over k((ε)) with affine entries in m² variables. The
entries cost ≤ n²(2m²+1) gates, and det costs C·n^{e_det} gates over the ring k((ε))[x]. So PERM_m is
approximated with ≤ 3n²m² + C n^{e_det} gates. Since (H) forces n ≥ m^{ω(1)}, the first term is ≤ n^{2+o(1)},
and the total is ≤ C' n^{e_det}. Hence n ≥ (S(m)/C')^{1/e_det}. ∎

**Corollary 6' [R] (Mulmuley–Sohoni, quantitative).** Over C, for n < m^{(c/e_det − ε)(log m)^{1/3}} and m large:

  z^{n−m} PERM_m ∉ \overline{GL_{n²}·det_n}.

This is the orbit-closure conjecture of MS01, for padding up to quasi-polynomial n.

*Proof.* A point of an orbit closure is a formal-curve limit. Setting z = 1 turns linear forms into affine
ones, giving \bar{dc}(PERM_m) ≤ n, which contradicts Cor 6. ∎

Comparison:
- Known effective bounds: dc ≥ m²/2 (MR04; CCL10 in all characteristics ≠ 2), and \bar{dc} ≥ m²/2 (LMR13).
- A cubic bound was announced (OAI26; odd characteristic in Sheshadri 2610.40484).
- Cor 6 is asymptotically far stronger (quasi-polynomial), but ineffective. Even ignoring m0, it beats m³ only
  for log m > (3e_det/c)³ ≈ 3.5·10¹⁵ (`params.py`). **For every concrete m the quadratic and cubic bounds remain
  the best known.**

Novelty: the qualitative statement is the paper's Remark N.6. The explicit exponent, the HC/all-fields
variant and the padded-orbit form are spelled out here.

## 4. Other models and families

**Corollary 7 [R] (formulas, ABPs, depth, division).** Assume (H), m ≥ m0, char ≠ 2 (or HC_m for all k).
- (a) **Formulas.** Formula size of PERM_m is > S(m). The previous best was polynomial, at most quadratic in the
  number of variables (Kalorkoti 1985, CKSV22). Border formulas: the same.
- (b) **ABPs.** An ABP with E edges gives a circuit with ≤ 2E + |V| gates, so ABP size ≥ S(m)/3. This gives
  **VBP ≠ VNP and \bar{VBP} ⊉ VNP over every field.**
- (c) **Depth.** A fan-in-2 circuit of depth Δ has ≤ 2^{Δ+1} gates, so every circuit for PERM_m has depth
  > c(log m)^{4/3} − 1. This is the first ω(log m) depth lower bound for unrestricted fan-in-2 circuits; degree
  gives only log m. It exceeds 2 log m once log m > (2/c)³ ≈ 5·10¹³. Consequently PERM ∉ VNC¹, and the family
  is not in "VQP_α" (size 2^{(log m)^{α}}) for α < 4/3. **VNP ⊄ VQP remains open [C]**: the bound is only
  quasi-polynomial with exponent 4/3.
- (d) **Circuits with division.** A circuit with divisions of size L computing PERM_m can be converted to a
  division-free one of size ≤ C·m²·L. This is Strassen 1973: shift to a point where all denominators are nonzero,
  over an extension, then work with power series truncated at degree m. So L > S(m)/(Cm²) = m^{(c−o(1))(log m)^{1/3}}.
  This replaces the m² log m bound of [Guo26] that the paper cites, asymptotically and ineffectively. The border
  version is the same.

**Corollary 8 [R] (other complete families, explicit loss).** Let (f_N) be any family with PERM_m ≤_proj f_{q(m)}
(resp. HC_m ≤_proj f_{q(m)}) and q(m) ≤ C m^{a}. Projections do not increase gate count, so
L(f_{q(m)}) ≥ L(PERM_m) > S(m), that is

  L(f_N) > 2^{(c a^{−4/3} − o(1)) (log N)^{4/3}}  for all N = q(m), m ≥ m0.

The bound holds for all large N if (f_N) is projection-monotone (f_N ≤ f_{N+1}). Examples:
- PERM in terms of its n = m² variables: a = 2, giving L > 2^{c·2^{−4/3}(log n)^{4/3}}.
- Any VNP-complete family, with a = its p-projection exponent from HC (Valiant 1979; Bürgisser 2000 Ch. 2–3).
- Border versions follow from border projections.

**Raz 2010/2013 (elusive functions, tensor rank).** Nothing new follows **[K/negative]**.
- Raz 2013 goes from tensor rank to formulas, the wrong direction.
- Raz 2010 goes from elusive maps to lower bounds. Read backwards, the coefficient vector of HC_m is a point
  outside the image of the universal size-S(m) degree-m circuit map. That is only the constant map, a
  degenerate "elusive function" that merely restates (H).

## 5. Boolean consequences (GRH etc.)

**Corollary 9 [R, mostly negative].**
- (a) The known links all point Boolean ⇒ algebraic:
  - Valiant: over F_q, VP = VNP ⇒ NC/poly = #_pP/poly, unconditionally.
  - Bürgisser 2000: in characteristic 0, VP_C = VNP_C ⇒ the same collapse, **assuming GRH** (used through
    Koiran's Nullstellensatz analysis, which needs GRH for Dedekind zeta functions of number fields, not just
    Dirichlet L-functions).
  
  The contrapositives say Boolean separation ⇒ algebraic separation. So (H) **implies no Boolean lower bound**,
  with or without GRH. A proof of GRH for Dirichlet L-functions would not change this.
- (b) (H) implies VP⁰_Z ≠ VNP⁰_Z. The reason: constant-free poly-size circuits with poly formal degree are
  circuits over Q, and PERM ∈ VNP⁰_Z. Hence the following PIT⇒Boolean "win–win" theorems now have a true
  arithmetic disjunct and **no longer yield Boolean consequences**:
  - KI04: PIT ∈ NSUBEXP ⇒ NEXP ⊄ P/poly ∨ PERM ∉ VP_Z;
  - Chukhin–Gajulapalli–Golovnev–Mihajlin 2611.07972, Thm 1, Cor 4, Thm 8;
  - Chatterjee–Tengse (succinct hitting sets ⇒ VP ≠ VNP ∨ TC⁰ bounds under GRH).

  This is worth flagging to the community **[R]**.
- (c) Nothing Boolean follows from Cor 1 either. Black-box PIT in SUBEXP was already known to follow from
  Boolean hardness assumptions, and it is not known to imply Boolean lower bounds beyond what (b) kills.

## 6. Status table

| # | Statement | Tag | Novelty |
|---|---|---|---|
| 1 | Black-box hitting sets of size 2^{2^{(4+o(1))((log sd)/c)^{3/4}}} for C(s,n,d), char 0 or > d, including border | R | KI method folklore; unconditional instance + exponents new (no prior claim found) |
| 2 | Same, all characteristics, individual degree < p | R | new, small |
| – | General circuits, char p ≤ d | C/open | blocked by p-th roots (Andrews 2020) |
| 3 | Explicit Noether normalisation of closures of VP, Δ[det]: subexp time | R | new given (H) |
| 4 | Edmonds' problem / commutative rank in time 2^{N^{o(1)}} | R | new given (H) |
| 5 | Template for any hardness T(m) | R | standard |
| 6, 6' | dc, \bar{dc} ≥ m^{(c/2.697−ε)(log m)^{1/3}}; padded orbit-closure form | R | explicit form of the paper's Rem N.6 |
| 7 | Formula, ABP, depth > c(log m)^{4/3}−1, division circuits | R | easy; depth and division items not in the paper |
| 8 | Complete families with loss a^{−4/3} | R | routine |
| 9 | No Boolean consequences; KI / CGGM / CT win–wins become vacuous | R | observation |

Caveats that apply to everything above:
1. Everything is conditional on the unrefereed (H).
2. All thresholds are ineffective because of m0.
3. The numbers are astronomically far from practical: nontrivial only once log s > 3.5·10¹⁶.
