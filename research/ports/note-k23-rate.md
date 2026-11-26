# Tensor rates of the networks K_{2,m}: 3/√10 ≤ f* for the Okamura–Seymour network K_{2,3}, and 2m/√(m²(m−1)²+4w²) ≤ f* in general, with equality unless the contracting hypothesis holds; and the exact rate 3/(2+w) in the cut regime

*Draft note, 26 November 2026; revised version. Self-contained. Status tags are defined in §0.3 and collected in
§8.*

---

## 0. Statement, scope, provenance

### 0.1 The result

Parties u₁, u₂, v₁, v₂, v₃. Over a field k, let ⟨q⟩_{xy} be the wire of dimension q between parties x and y (the
q×q identity matrix in the indices of x and y; every other party holds a one-element index set). Put

    S = ⊗_{i∈{1,2}, j∈{1,2,3}} ⟨2⟩_{u_i v_j}          (supply: the six edges of K_{2,3}),
    T = ⟨2⟩_{v₁v₂} ⟨2⟩_{v₂v₃} ⟨2⟩_{v₁v₃} ⟨2⟩_{u₁u₂}     (demand: the three pairs on the 3-side, the pair on the 2-side),

and, with ≤ meaning restriction (s ≤ t iff s = (⊗_p A_p) t for linear maps A_p, one per party),

    f*(k) = f*(K_{2,3}; k) = sup { f : there are m_n with T^{⊗m_n} ≤ S^{⊗n} over k and m_n/n → f }.

The same rate f is required on all four demand wires. Write κ = 3/√10 = 0.948683298…

> **Theorem K.**
> 1. *(Unconditional.)* f*(k) ≥ 3/√10 for every field k.
> 2. *(Conditional upper bound.)* If the contracting hypothesis of [AN] (Def. D.1) fails over k, then
>    f*(k) = 3/√10. Over an infinite field k the upper bound also holds for border protocols whose
>    approximation degree is 2^{o(n)}.
> 3. *(Consequence.)* Let k have characteristic 0. A protocol over k of rate > 3/√10 implies that the
>    contracting hypothesis holds over k. By the companion note [CE] this implies that 3-SAT on n variables is
>    decidable in time 2^{O(n^{1−δ})}·poly for some δ > 0. Hence, under the weak exponential-time hypothesis,
>    f*(k) = 3/√10. The status of this step is that of [CE]; see §5.
> 4. *(Small exact facts.)*
>    - No exact single-shot restriction achieves rate 1: wires of dimension D ≥ 2 cannot be converted into demand
>      wires of dimension D, over any field.
>    - At supply dimension 2, demand with all three v–v wires of dimension 2 is impossible, even as a border
>      restriction over ℂ.
>    - Every ℓ₁-embeddable pseudometric d has R(d) ≥ 1 (R as in §1.1). So none of the spectral points whose wire
>      metrics are explicitly known certifies any upper bound below 1.

Item 1 is no longer computer-assisted: its last step, the inequality (CL*), has a six-line analytic proof (Theorem
D, §3.3), checked in Lean. The interval certificates of the first version remain as a confirmation (§3.5).

**The general statement.** For m ≥ 3 and w > 0 let K_{2,m}(w) be the network with parties u₁, u₂, v₁, …, v_m,
supply the 2m binary wires u_kv_i, and demand all C(m,2) wires v_iv_j at rate f together with u₁u₂ at rate w·f
(§1.1). Theorem K is the case m = 3, w = 1. Put

    R_m(w) = 2m/√(m²(m−1)² + 4w²),       κ(w) := R_3(w) = 3/√(9+w²),       R_3(1) = κ.

> **Theorem K_m.** Let m ≥ 3 and let k be any field.
> 1. *(Unconditional.)* f*(K_{2,m}(w); k) ≥ R_m(w) for 0 < w ≤ m(m−1)/6. The range contains w = 1 for every m.
> 2. *(Conditional upper bound.)* If contracting fails over k, then f*(K_{2,m}(w); k) ≤ R_m(w) for every w > 0
>    (also for border protocols as in item K.2). So f* = R_m(w) in the range of item 1.
> 3. *(Comparison.)* Routing achieves exactly 2m/(m(m−1)+2w). The cut bound is min(2/(m−1), m/(⌊m²/4⌋+w)). In
>    the range of item 1, routing < R_m(w) < cut bound.
> 4. *(Consequence.)* A protocol over k of rate above R_m(w) implies that contracting holds over k (§5).
> 5. *(Cut regime, unconditional; Theorem E, §4.4.)* For every field k, f*(K_{2,3}(w); k) = 3/(2+w) for all
>    w ≥ w₀ and f*(K_{2,4}(w); k) = 4/(4+w) for all w ≥ 2w₀, where the threshold w₀ depends on the support:
>    - (a) w₀ = w₁ = 1.9134429… (λ₁ = 3/(2+w₁) = 0.7665884…, the real root of 4λ³ − 8λ² + 9λ − 4): proof by hand,
>      refereed;
>    - (b) w₀ = 4/3: in addition one computer-assisted six-variable inequality, S(9/10);
>    - (c) w₀ = 5/4: in addition a second one, (CL\*\*₀), which yields the five-point inequality
>      13Σ_S ≥ 12Σ_vv + 15D.
>
>    Routing gives 3/(3+w) and 4/(6+w).

Item 5 is unconditional: the upper bound is one flattening rank, the lower bound uses only what item K.1 uses. At
w = 2 the rate is exactly 3/4 (routing 3/5). For 1 < w < 5/4 only bounds are known (§4.4).

For comparison:
- routing gives exactly 3/4;
- classical network coding also gives exactly 3/4: the instance is the Okamura–Seymour example [OS81], the standard
  case where the cut condition holds but flows fail, and its network coding rate is 3/4 [HKL06, Thm 27; also
  AHJKL06]. The same result was obtained concurrently by Jain–Vazirani–Yuval (SODA 2006) and by Kramer–Savari; we
  know these two only from their citation in arXiv:2610.09367 and arXiv:2610.33655;
- the cut bound is 1, and it is attained by a flattening rank, so f* ≤ 1 unconditionally;
- the quadrilateral inequality for prices alone gives only the strict inequality f* > 3/4 (an earlier step of this
  project).

We found no prior study of this instance for tensor restriction and no occurrence of the constants 3/√10 or
6/(4+√10) (search of 26 November 2026). We also found no treatment of it for SLOCC or LOCC entanglement conversion.
The restriction framework for networks of wires is that of [CLSWW24]; for GHZ- or broadcast-type demands tensors are
known to reach the cut bound [VC17], whereas our demand is multiple-unicast. The networks K_{2,m} with m ≥ 4 were not
searched separately.

Item 1 says that the tensor restriction rate of these five parties exceeds the routing rate by at least the factor
4/√10 ≈ 1.265, and exceeds by the same factor the classical network-coding rate of the same graph instance [HKL06].
This is a comparison between different resource models, not a like-for-like improvement: f* is exact asymptotic
restriction (SLOCC-type, with post-selection and no fidelity requirement), whereas network coding concerns
classical information, and LOCC and channel models with fidelity constraints ([JV20; LOW10]) are different again
(§0.2).

*Context.* In October 2026 two preprints claimed refutations of the undirected multiple-unicast conjecture (that
network coding gives no gain over routing in undirected networks): Z. Li, B. Li, arXiv:2610.09367, and Zhongtian He,
arXiv:2610.10108. Liu–Que–Li–Li, arXiv:2608.06070, prove the conjecture for networks with at most five terminal
locations, which covers K_{2,3} and is consistent with [HKL06]. So K_{2,3} remains an instance where coding equals
routing classically. (These items were read at the level of abstracts.)

### 0.2 What is not claimed

- **Scope.** f* is the rate of exact asymptotic restriction. Items K.1 and K_m.1 are non-constructive.
- **Not LOCC, not a coding improvement.** f* is SLOCC-type, a different resource model from classical network
  coding [HKL06] and from LOCC or fidelity-based models ([JV20]: LOCC with success probability 2^{−rn}; that the
  restriction rate is the r → ∞ end is the literature check's inference, not checked against the paper; [LOW10]:
  k-pair quantum communication). For LOCC on this instance we know no result and no upper bound below 1.
- **No explicit protocol near 3/√10.** An explicit family above routing is described in §7: rate ≥ 0.83671 with
  exact certificates, and 6/(4+√10) ≈ 0.83772 in the limit under one numerical claim. It is not part of the
  theorems, and its smallest instances are far beyond direct computation. Nothing explicit is known for m ≥ 4.
- **Unconditional values only in the cut regime.** What is unconditional: the lower bounds K.1, K_m.1, the cut
  upper bounds, and the exact values of item K_m.5 (m = 3, 4, w ≥ w₀). What is conditional on the failure of
  contracting: every exact value below the cut bound, in particular f*(k) = 3/√10. If contracting holds over k, we
  know only f*(k) ∈ [3/√10, 1], and for K_{2,m}(w) outside item K_m.5 only f* ∈ [proved lower bound, cut bound].
- **No claim that contracting holds or fails** over any field.
- **Border protocols** over finite fields, or of exponential approximation degree: nothing is claimed.
- **Non-uniform demands.** Only the demands of K_{2,m}(w) are treated: one weight on u₁u₂, one rate on all v_iv_j.
  For m = 3 the lower bound κ(w) covers w ≤ 1 only; for w > 1 Theorem D fails (§3.3, remark 3), the range
  1 < w < 5/4 is open, and from w₀ on the rate is the cut value (§4.4). Other demand vectors are different linear
  tests (§1.2); a few are treated in §4.5.
- **No unconditional algorithm or lower bound in complexity.** Item 3 is an implication between hypotheses.

### 0.3 Provenance and tags

**[AN]** is Anthropic, "VP ≠ VNP over every field" (November 2026), with a Lean development.
- The paper is machine-generated and has not been refereed by people. Its §3 says: "The proofs in this paper were
  found and written by AI. No human mathematician has checked the proofs."
- The OpenAI papers cited here ([EG], [MM], and those used in [CE]) are likewise machine-generated and not refereed
  by people. We have built neither lab's Lean development. We read the statements we use, and in places their Lean
  counterparts.
- Line numbers "l." refer to our pdftotext copy of the paper.

The imported facts are used as follows:
- **Items K.1, K_m.1** use only Strassen 1988 [Str88] and the CAT(0) property of prices: [AN] Theorem C.1
  (`thm_cn`), packaged as Prop. C.3 (`prop_space`), used through Lemma C.4(a).
- **Items K.2, K_m.2** additionally use `thm_alt_rank_price` (from the proof of Theorem D.2) and Lemma C.4(f).
- **Item K_m.5** uses the same imports as K.1 and a flattening rank; levels (b), (c) also the interval
  certificates of §4.4.
- **Items 1–2 use nothing from OpenAI's papers**; [EG] Thm 4.3 is an alternative source for the CAT(0) input (§1.3).
- **Item 3** uses the companion note [CE] (`note-contracting-eth.md`), one of whose two routes uses OpenAI results
  (§5).

Tags:
- **[P]**: proved here by hand, completely.
- **[P-ref]**: [P], and also checked by an internal referee (a named report).
- **[L]**: machine-checked in Lean in `research/ports/lean/` (Lean v4.36.0 with Mathlib). The project was rebuilt
  for this version: it compiles with no `sorry`, and `#print axioms` shows only `propext`, `Classical.choice` and
  `Quot.sound`. The Lean statement is named each time.
- **[IV]**: verified by the interval certifiers of §3.5 and §4.4.
- **[N]**: numerical evidence only.
- **[AN]**: quoted from [AN].
- **[cl]**: classical.
- **[C]**: conjecture.

---

## 1. Setup

### 1.1 Strassen duality for this instance [cl]

The tensors on the m+2 parties over k, with direct sum, tensor product and restriction, form a preordered
semiring that satisfies Strassen's conditions. Let 𝒳 be its asymptotic spectrum: the functions F ≥ 0 on tensors
that are monotone under restriction, multiplicative under ⊗, additive under ⊕, and normalised by F(⟨r⟩) = r on unit
tensors. Strassen [Str88] proved that a^{⊗n} ≤ b^{⊗(n+o(n))} iff F(a) ≤ F(b) for all F ∈ 𝒳.

For F ∈ 𝒳 put d_F(x,y) = log₂ F(⟨2⟩_{xy}). This is a pseudometric on the parties: F(⟨q⟩_{xy}) = q^{d_F(x,y)},
and ⟨2⟩_{xz} ≤ ⟨2⟩_{xy}⟨2⟩_{yz}. For a pseudometric d write

    Σ_S d = Σ_{k,i} d(u_k, v_i),    Σ_vv d = Σ_{i<j} d(v_i, v_j),    D = d(u₁,u₂),    Σ_T d = Σ_vv d + D,
    R(d) := Σ_S d / Σ_T d,           R_w(d) := Σ_S d / (Σ_vv d + w·D).

By multiplicativity log₂ F(S) = Σ_S d_F and log₂ F(T) = Σ_T d_F. Applying Strassen's theorem to a = T^{⊗p} and
b = S^{⊗q} gives the rate formula

    f*(k) = inf_{F ∈ 𝒳, F(T) > 1} R(d_F).                                                              (1.1)

The formula is an infimum, not a minimum. 𝒳 is compact, but it is not closed under F ↦ F^a. So
log F(S)/log F(T) may approach its infimum along points with F(T) → 1, and we do not know that the infimum is
attained in 𝒳 (review-fivepoint §0.3). Over the larger AN class of §1.2 the infimum is a minimum.

From rational rates to the sup in the definition of f*: take rationals p/q ↑ the infimum; S^{⊗n} ≥ S^{⊗n′} for
n ≥ n′; S ≥ ⟨2⟩ on all parties (via a spanning tree), so ≤ S^{⊗(n+o(n))} and ≤ S^{⊗n} ⊗ ⟨2^{o(n)}⟩ mean the same;
choose sequences diagonally. Strassen's theorem can be replaced by [AN] Theorem A.6 (`thm_duality`, l. 1164–1167),
since a cover is a restriction of a direct sum and ⟨2^{εN}⟩ ≤ S^{⊗εN}.

**Weighted demand.** For m ≥ 3 and w > 0, f*(K_{2,m}(w); k) is the supremum of f such that there are restrictions
over k

    ⊗_{i<j} ⟨2^{a_n}⟩_{v_iv_j} ⊗ ⟨2^{b_n}⟩_{u₁u₂}  ≤  S^{⊗n},      a_n/n → f,   b_n/n → w·f.

For m = 3 and w = 1 this is f*(k). Its dual description is §1.2(d).

### 1.2 Prices, and why the AN class is enough in both directions [P-ref]

[AN] Def. A.1 (l. 1058–1061): "A spectral point on I is a function φ ≥ 0 on the tensors on I such that φ(1) = 1,
such that φ(st) = φ(s)φ(t) for all tensors s and t, and such that φ(s) ≤ Σ_{j=1}^r φ(t_j) whenever s is covered
by t₁,…,t_r." Here "covered" means s = s₁ + ⋯ + s_r with s_j a restriction of t_j (l. 1028–1030).

By [AN] Lemma A.2, φ(⟨q⟩_{uv}) = q^{d_φ(u,v)}.

[AN] Def. A.4 (l. 1121–1129): "A price on a finite set V is a limit of functions c·d_φ, where c ≥ 0 is a real
number and φ is a spectral point on V. A function on the pairs of elements of an arbitrary set Y is a price if all
its pull-backs to finite sets are prices. […] Pull-backs, nonnegative multiples and pointwise limits of prices
are prices."

*(a) Every F ∈ 𝒳 is an AN spectral point.* If s = Σ_j s_j with s_j ≤ t_j, then s ≤ ⊕_j s_j (each party adds the
blocks), so F(s) ≤ Σ_j F(t_j). Hence each d_F is an AN price.

*(b) Every AN price bounds every protocol.* Let d be a price with Σ_T d > 0, and suppose T^{⊗m} ≤ S^{⊗n}. For a
spectral point φ, monotonicity, multiplicativity and A.2 give 2^{m Σ_T d_φ} = φ(T^{⊗m}) ≤ φ(S^{⊗n}) =
2^{n Σ_S d_φ}. This inequality is linear in the distances, so it survives positive multiples and pointwise limits:
m Σ_T d ≤ n Σ_S d. Hence f*(k) ≤ R(d). In the same way a_nΣ_vv d + b_n D ≤ nΣ_S d, so f*(K_{2,m}(w); k) ≤ R_w(d)
for every real w > 0.

*(c) Border protocols over infinite k.* Suppose (⊗_p A_p(ε)) S^{⊗n} = ε^e T^{⊗m} + O(ε^{e+1}), with the A_p
polynomial in ε of total degree D_n. Lagrange interpolation at D_n + 1 points of k writes T^{⊗m} as a combination of
D_n + 1 restrictions of S^{⊗n} (scalars absorbed into one party's map). This is a cover, so
2^{m Σ_T d_φ} ≤ (D_n + 1)·2^{n Σ_S d_φ}. If D_n = 2^{o(n)}, for example D_n = O(n) for powers of a fixed
single-shot border protocol, the rate bound is unchanged.

By (a) and (b), min over AN prices of R ≤ inf over 𝒳 = f* ≤ min over AN prices of R; the minimum is attained
(after normalising Σ_T d = 1 the prices are compact by Def. A.4 and Tychonoff, and the AN class is closed under
φ ↦ φ^a). So a lower bound may be proved for all AN prices, and an upper bound needs one. (b) and (c) are the
argument of review-hull §6.

*(d) Weighted demand [P-ref: review-k2m §0, item 1].* Let G(w) := min over AN prices d (with Σ_vv d + wD > 0) of
R_w(d); the minimum is attained as above. Then f*(K_{2,m}(w); k) = G(w) for every real w > 0.
- "≤" is (b).
- For rational w = p/q apply Strassen's theorem to a = ⊗_{i<j}⟨2^q⟩_{v_iv_j} ⊗ ⟨2^p⟩_{u₁u₂}, with
  log₂F(a) = qΣ_vv d_F + pD_F, and conclude with (a) as above.
- For irrational w use two facts. Monotonicity: ⟨2^b⟩ ≥ ⟨2^{b′}⟩ for b′ ≤ b, so f*(w) ≥ f*(w′) for w′ > w.
  Continuity: 1/G(w) is a maximum of affine functions of w over a compact set of normalised prices, hence convex
  and finite on (0,∞), so G is continuous. Hence f*(w) ≥ lim_{w′↓w, w′∈ℚ} G(w′) = G(w). The top of the range in
  Theorem K_m, m(m−1)/6, is rational, so such w′ exist inside the range.

### 1.3 The CAT(0) input [AN]

[AN] §C.4 (l. 1597–1602): "A metric space is CAT(0) if it is complete and if any two of its points have a
midpoint that satisfies the CN inequality. A price space is a CAT(0) space whose metric is a price in the sense of
Definition A.4." The CN inequality (C.1), for a midpoint m of x, v, is |zm|² ≤ ½|zx|² + ½|zv|² − ¼|xv|².

- **Prop. C.3** (`prop_space`; l. 1608–1609): "Every price on a set V is the pull-back of the metric of a price
  space." Its proof rests on Theorem C.1 (`thm_cn`, "prices have nonpositive curvature") and Prop. A.8. It has no
  restriction on |V|.
- **Lemma C.4(a)** (`lem_toolkit_a`; l. 1642–1644): "For x, v ∈ Y and t ∈ [0,1] exactly one point γ(t) has the
  distances t|xv| from x and (1−t)|xv| from v, and |zγ(t)|² ≤ (1−t)|zx|² + t|zv|² − t(1−t)|xv|² for every z ∈ Y."
- **Lemma C.4(f)** (`lem_toolkit`; l. 1658–1660): "Suppose that |xy| = |uv| = δ and |xu| = |yv| = h, that both
  diagonals of the quadrilateral x, y, v, u have the squared length δ² + h², and that a ∈ [x,u] and b ∈ [y,v] have
  |xa| = sh and |yb| = th. Then |ab|² = δ² + h²(s−t)²."

**An independent source for item 1.** OpenAI's [EG] Thm 4.3 ("Every complete geodesic spectral space X is CAT(0)"),
with [EG] Cor. 3.4 (geodesic extension), gives the CAT(0) embedding for points of Strassen's spectrum directly. On that
route item 1 uses nothing from [AN]: Strassen's theorem, [EG] 4.3 and the standard CAT(0) fact C.4(a). This is the
reading of the literature check; we have not rewritten §§3–4 along this route.

### 1.4 The contracting hypothesis [AN]

For a price on the additive group Mat_μ(F₂), D(r)² is the mean of |a, a+W|² over all a and all W of rank r.
Def. D.1 (`def_cases`; l. 1698–1702): "Contracting hypothesis: There are an integer μ ≥ 2 and a real number s with
1 ≤ s and s² < μ such that D(μ) ≤ s D(1) for all prices on Mat_μ(F₂)." Def. 2.1 states the same with spectral
points in place of prices. The two forms are equivalent, because the inequality is homogeneous and closed under
limits.

**`thm_alt_rank_price`** (`Paper/Alternative.lean`, l. 706–707 of that file; in the paper, Steps 1–7 of the proof
of Thm D.2 and Remark D.3):

    theorem thm_alt_rank_price (hK : ¬ Contracting K) (hμ : 3 ≤ μ) :
        ∃ w : Mt μ → Mt μ → ℝ, IsPrice K w ∧ ∀ a a', w a a' ^ 2 = (a - a').rank

Failure of the hypothesis is the universal statement "for all μ and s, some price violates the bound". So every
μ ≥ 3 is available (l. 1712: "Suppose that the contracting hypothesis fails, and fix μ ≥ 3"); the proof needs
μ ≥ 3 (l. 1760). Write ρ_μ(a,b) = √rk(a−b).

---

## 2. Upper bound: (m-pod) × segment is forced when contracting fails [P-ref]

### 2.1 Lemma P: the matrices

Let q = 2^r and P¹ = P¹(F_q) = {[1:a] : a ∈ F_q} ∪ {∞ = [0:1]} (q+1 points).

*Rank-one idempotents.* t ∈ Mat₂(F_q) has rk t = rk(I−t) = 1 iff t = uxᵀ with xᵀu = 1 (det(I − uxᵀ) = 1 − xᵀu;
then t² = t). Such t is determined by its image ⟨u⟩ and kernel x^⊥, two different points of P¹. For two of them,
t − t′ = [u u′]·diag(1,−1)·[x x′]ᵀ, so t − t′ is invertible iff im t ≠ im t′ and ker t ≠ ker t′.

*The family.* For the fixed-point-free permutation π(0) = ∞, π(∞) = 1, π(1) = 0, π(a) = a+1 (a ∈ F_q ∖ {0,1}), let
t_p be the idempotent with image p and kernel π(p). Explicitly (rows separated by ";"):

    t_0 = [1 0; 0 0],   t_∞ = [0 0; 1 1],   t_1 = [0 1; 0 1],   t_a = [a+1  1; a²+a  a]   (a ∈ F_q ∖ {0,1}).

> **Lemma P.** In Mat₂(F_q), q = 2^r: rk t_p = rk(I − t_p) = 1 for all p ∈ P¹, rk(t_p − t_{p′}) = 2 for p ≠ p′,
> and rk I = 2.

*Push-forward to F₂.* Let ι₂: Mat₂(F_q) → Mat_{2r}(F₂) apply the regular representation of F_q (for a fixed
F₂-basis) entrywise. Then ι₂(A) is the matrix of x ↦ Ax on F_q² ≅ F₂^{2r}, whose image is an F_q-subspace of
F_q-dimension rk A. So ranks over F₂ scale by r: rk_{F₂} ι₂(A) = r·rk_{F_q}(A), and, ι₂ being additive,
ρ_{2r}(ι₂A, ι₂B) = √r·√rk_{F_q}(A−B).

> **Corollary P.** For m ≤ 2^r + 1, the m+2 matrices 0, I, ι₂(t_p) (any m points p) carry under ρ_{2r} the metric
> √r·√(graph metric of K_{2,m}), with {0, I} the 2-side. The same holds in Mat_μ(F₂) for every μ ≥ 2r, since
> a ↦ diag(a,0) preserves ranks. We use μ = max(2r, 3).

For q = 2 the family is t₁ = e₁₁, t₂ = e₂₁ + e₂₂, t₃ = e₁₂ + e₂₂ of the first version, and the metric is **N5**,
the square root of the graph metric of K_{2,3}: its rank table is [L] (`Hull.lean`: `ranks_one`, `ranks_two`, over
`ZMod 2`); R(N5) = 6/(4√2) ≈ 1.06; N5 is ℓ₁-embeddable [N] and not Euclidean [P].

Checks: rank tables in Mat_{2r}(F₂) by exact integer arithmetic for r ≤ 6 (`k2m/fqpods.py`) and independently for
r ≤ 5 (review-k2m §1). The construction is optimal: Mat_μ(F₂) contains a scaled copy of √(graph metric of K_{2,m})
iff m ≤ 2^{⌊μ/2⌋} + 1 (review-k2m §2; not used).

### 2.2 Lemma H_m

Let 𝕋_m be the m-pod with hub o and legs of length a/√2. The diamond is
D_m = {(ξ,σ) ∈ 𝕋_m × ℝ : |ξo| + |σ| ≤ a/√2}, with the ℓ₂ product metric.

> **Lemma H_m.** Let Y be CAT(0) in the sense of §1.3, m ≥ 2, and let n, s, t₁, …, t_m ∈ Y satisfy
> |ns| = |t_it_j| = √2·a (i ≠ j) and |nt_i| = |st_i| = a. Then there is an isometric embedding Ψ: D_m → Y with
> Ψ(o, ∓a/√2) = n, s and Ψ(tip_i, 0) = t_i.

*Proof.*

*Step 1 (solid squares).* Let |xy| = |yv| = |vu| = |ux| = a and |xv| = |yu| = √2·a, and let α(s) ∈ [x,u],
β(s) ∈ [y,v] be the points at fraction s. C.4(f) with δ = h = a gives |α(s)β(t)|² = a²(1 + (s−t)²). For s ≠ s′,
the points α(s), α(s′), β(s′), β(s) again satisfy the hypotheses of C.4(f), with δ′ = a|s−s′|, h′ = a and diagonals
of squared length a²(1 + (s−s′)²) = δ′² + h′². So the point Φ(s,r) at fraction r on [α(s), β(s)] satisfies
|Φ(s,r)Φ(s′,r′)|² = a²((s−s′)² + (r−r′)²). Thus Φ is a times an isometry of [0,1]², with corners x, u, y, v. Geodesics are unique by C.4(a), so the image is
convex, and its diagonals meet at the common midpoint. Apply this to (n, t_i, s, t_j) for each of the C(m,2) pairs;
call the square Q_ij.

*Step 2 (one hub).* Every Q_ij contains [n,s]. So c := mid(n,s) = mid(t_i, t_j) for all pairs.

*Step 3 (triangles).* Δ_i := ∪_{p∈[n,s]} [t_i, p] is defined from geodesics alone. In Q_ij it is the t_i-half of
the square, and Q_ij = Δ_i ∪ Δ_j. Two isometric parametrisations of Δ_i, from Q_ij and from Q_ik, agree on the side
[n,s] (same endpoints, unique geodesic), hence on every segment from t_i to a point of that side, hence everywhere.

*Step 4 (gluing).* Put Ψ(ξ,σ) = ψ_i(|ξo|, σ) for ξ on leg i. Points on one leg lie in the flat triangle Δ_i.
Points on legs i ≠ j lie in the flat square Q_ij, at distance √((τ+τ′)² + (σ−σ′)²), the distance in 𝕋_m × ℝ. An
isometric embedding is a condition on pairs of points, so nothing about three legs is needed. ∎

Only C.4(a),(f) are used. Of [AN] D.2 Step 8 the one-square case is redone here, not cited. For m = 3 this is the
Lemma H of the first version (review-hull §§3–5: correct); the m-pod version is checked in review-k2m §3.

### 2.3 From Lemma H_m to the rate

W_{m+2}(ℓ,h) is the metric with v_j at distance ℓ from the hub on leg j at height 0, and u₁, u₂ at the hub at
heights ∓h:

    |u_k v_j| = √(ℓ² + h²),   |v_i v_j| = 2ℓ,   |u₁u₂| = 2h,   R_w = 2m√(ℓ²+h²)/(m(m−1)ℓ + 2wh).

By Cauchy–Schwarz, m(m−1)ℓ + 2wh ≤ √(m²(m−1)²+4w²)·√(ℓ²+h²), so

    min_{ℓ,h} R_w(W_{m+2}(ℓ,h)) = R_m(w),   attained exactly at h = 2wℓ/(m(m−1)).                    (2.1)

For m = 3, w = 1 (W5 := W_5) the minimum 3/√10 is attained only at h = ℓ/3, because
6√(ℓ²+h²)·√10 − 3(6ℓ+2h) ≥ 0 reduces to 4(ℓ−3h)² ≥ 0; this is [L] (`W5.lean`: `ratio_lower`, `ratio_at_third`,
`ratio_strict`, `w5_ratio`). W_{m+2}(ℓ,h) ⊂ D_m whenever max(ℓ,h) ≤ a/√2.

> **Corollary H_m.** If contracting fails over k, then for every m ≥ 3 and w > 0, W_{m+2}(ℓ, 2wℓ/(m(m−1))) is a price
> over k, and f*(K_{2,m}(w); k) ≤ R_m(w). In particular f*(k) ≤ 3/√10. The bound extends to border protocols as in
> §1.2(c).

*Proof.*
1. Choose r with 2^r + 1 ≥ m and put μ = max(2r, 3). `thm_alt_rank_price` gives the price ρ_μ. Pull back along
   the m+2 matrices of Corollary P and rescale by 1/√r: √(graph metric of K_{2,m}) is a price (N5 for m = 3).
2. By Prop. C.3 these m+2 points sit isometrically in a price space Y.
3. Lemma H_m (a = 1) embeds D_m, so a scaled copy of W_{m+2}(ℓ, 2wℓ/(m(m−1))) lies in Y.
4. The metric of Y is a price, so its pull-back to these points is a price. Rescale.
5. Apply §1.2(b) and (2.1). ∎

Prop. C.3 says the metric of the **whole** price space is a price, so no separate statement about convex hulls is
needed (review-hull §2). The m = 3 glue is [L] from explicit hypotheses (`Hull.lean`: `w5_price_of_rho_price`, with
Lemma H as the hypothesis `lemmaH`; Mathlib has no CAT(0) theory).

Equivalences: [P] N5 is a price over k ⇔ every finite subset of (tripod with infinite legs) × ℝ is (any finite
subset fits in a diamond after translation and scaling; likewise for m-pods). [P, not refereed] Also ⇔ W5(ℓ,ℓ/3)
is a price, by flat-quadrilateral rigidity [BH99, II.2.11], which is not in [AN]'s toolkit.

*Related geometry.* OpenAI's [MM] reduces its matrix-multiplication exponent to a tripod with unit arms in a spectral
space ("The critical ratio occurs at three tips of a tripod with unit arms", [MM] §1; also §8), a close relative of
W5 ⊂ tripod × segment; we use nothing from [MM].

---

## 3. Lower bound: the weighted five-point theorem

> **Theorem 5_w.** Let u₁, u₂, v₁, v₂, v₃ be points of a CAT(0) space (§1.3), and 0 < w ≤ 1. Then
> Σ_S ≥ κ(w)·(Σ_vv + w·D), κ(w) = 3/√(9+w²), with equality for W5(ℓ, wℓ/3). For w = 1 this is
> **Theorem 5**: Σ_S ≥ κ Σ_T.

By §1.2(a) and Prop. C.3, every d_F with F ∈ 𝒳, and every AN price on five parties over any field, is the
restriction of the metric of a CAT(0) space to five points. Theorem 5_w combines the reduction to books (§3.1,
[P-ref]), the calibration (§3.2, [P-ref], also numerical) and Theorem D (§3.3, [P-ref; L]). The referee's final
report on w = 1 (review-fivepoint.md) found no gap, fatal or repairable, in the chain C.3 → C.4(a) → (3.1) →
Prop. 3.2 → (CL*) → duality; the weighted chain is checked in review-k2m §4.

Write D = |u₁u₂|, A_i = |u₁v_i| and B_i = |u₂v_i|.

### 3.1 Reduction to books

*Passing to a price space.* Start from a price d on the five parties. By Prop. C.3, d is the pull-back of the
metric of a price space Y, which is CAT(0). The pull-back may identify points, which is harmless. From now on,
u₁, …, v₃ denote the image points in Y, so the segment [u₁,u₂] and its points c_t exist. For an abstract
five-point price they need not.

If D = 0, then u₁ = u₂ in Y, so B_i = A_i and Σ_vv ≤ Σ_{i<j}(A_i + A_j) = 2ΣA_i = Σ_S. Hence R_w ≥ 1 > κ(w). Let
D > 0, and let c_t ∈ Y be the point at fraction t of [u₁,u₂]. By C.4(a) with z = v_i, x = u₁ and v = u₂,

    |v_i c_t|² ≤ (1−t)A_i² + tB_i² − t(1−t)D² =: h_i(t)²,

where h_i(t) is the apex-to-base distance in the Euclidean triangle with sides D, A_i, B_i (Stewart's theorem).
The triangle inequality in Y through the same point c_t, used for both i and j, gives

    |v_iv_j| ≤ min_{t∈[0,1]} (h_i(t) + h_j(t)) =: d^Z_ij.                                              (3.1)

This inequality is the only thing used below. Put Σ_vv(Z) := Σ_{i<j} d^Z_ij. Since Σ_S and D are unchanged and
Σ_vv ≤ Σ_vv(Z), it suffices to prove Σ_S − κ(w)(Σ_vv(Z) + wD) ≥ 0. This quantity depends only on the six numbers
A_i, B_i and on D. Degenerate pages (ρ_i = 0, or v_i = u_k) need no special treatment.

*Language.* The **book** Z is three Euclidean comparison triangles (ū₁, ū₂, v̄_i) glued along the common side, the
spine; d^Z_ij is the distance of v̄_i and v̄_j in Z.

### 3.2 Calibration (complete computation)

*Coordinates.* In page i, (ρ,a) are the distance from the spine line (ρ ≥ 0) and the height along it: u₁ = (0,0),
u₂ = (0,D), v_i = (ρ_i, a_i) (a_i may lie outside [0,D]), c(y) = (0,y) for y ∈ [0,D]. Then A_i = |(ρ_i, a_i)|,
B_i = |(ρ_i, a_i − D)|, and f_i(y) := |v_i − c(y)| = h_i(y/D).

*Hubs and exit vectors.* For i ≠ j let y_ij = y_ji ∈ [0,D] minimise the convex function g_ij = f_i + f_j, so that
d^Z_ij = f_i(y_ij) + f_j(y_ij). Let e_ij = (cos ψ_ij, sin ψ_ij) =: (c_ij, σ_ij), with ψ_ij ∈ [−π/2, π/2], be the
unit vector of v_i − c(y_ij) in page i. Its first coordinate ρ_i/f_i is ≥ 0.
- Where f_i(y_ij) > 0, f_i′(y_ij) = −σ_ij.
- If v_i = c(y_ij), the subdifferential of f_i there is [−1,1]. Choose σ_ij ∈ [−1,1] so that (3.2) holds (σ_ij =
  −σ_ji, or 0 if both vanish), and put c_ij = √(1−σ_ij²). (The ρ_i c_ij term then vanishes.)

With ε_ij := σ_ij + σ_ji, so that −ε_ij is a (sub)gradient of g_ij, first-order optimality reads:

    y_ij ∈ (0,D):  ε_ij = 0;      y_ij = D:  ε_ij ≥ 0;      y_ij = 0:  ε_ij ≤ 0.                        (3.2)

In each case f_i(y_ij) = ⟨e_ij, v_i − c(y_ij)⟩ = ρ_i c_ij + (a_i − y_ij) σ_ij, and y_ij ε_ij = D ε_ij·[y_ij = D].
Put E₂ = Σ_{pairs with y_ij = D} ε_ij ≥ 0 and E₁ = Σ_{pairs with y_ij = 0} |ε_ij| ≥ 0. Then Σ_{i<j} ε_ij = E₂ − E₁
and Σ_{i<j} |ε_ij| = E₁ + E₂. Summing over the three pairs, with {j,k} the two indices other than i,

    Σ_{i<j} d^Z_ij = Σ_i (ρ_i P_i + a_i Q_i) − D E₂,     (P_i, Q_i) := e_ij + e_ik,     Σ_i Q_i = E₂ − E₁.     (3.3)

*Calibrating the supply.* By Cauchy–Schwarz, for any angles α_i and β_i,

    A_i ≥ ρ_i cos α_i + a_i sin α_i,        B_i ≥ ρ_i cos β_i + (D − a_i) sin β_i,                          (3.4)

where the second uses the unit vector (cos β_i, −sin β_i).

*Choice of angles.* Write λ = κ(w). Put μ_i = (ψ_ij + ψ_ik)/2 and δ_i = (ψ_ij − ψ_ik)/2, both in [−π/2, π/2].
Then (P_i, Q_i) = 2 cos δ_i (cos μ_i, sin μ_i), with cos δ_i ∈ [0,1]. Put ν_i = arccos(λ cos δ_i) ∈ (0, π/2]
(note λ < 1), α_i = ν_i + μ_i and β_i = ν_i − μ_i. The sum-to-product formulas give

    cos α_i + cos β_i = 2 cos ν_i cos μ_i = λ P_i,
    sin α_i − sin β_i = 2 cos ν_i sin μ_i = λ Q_i,
    sin β_i = sin ν_i cos μ_i − cos ν_i sin μ_i = M_i − λQ_i/2,     M_i := cos μ_i √(1 − λ² cos² δ_i) ≥ 0.

*Sum.* Add (3.4) over i and insert these identities and (3.3):

    Σ_S ≥ Σ_i [ρ_i(cos α_i + cos β_i) + a_i(sin α_i − sin β_i) + D sin β_i]
        = λ (Σ_vv(Z) + D E₂) + D Σ_i M_i − (λD/2)(E₂ − E₁),

    Σ_S − λ(Σ_vv(Z) + wD) ≥ D (Σ_i M_i − λw + (λ/2)(E₁ + E₂)).

All ρ_i and a_i have cancelled. Finally 1 − λ²cos²δ = (w² + 9 sin²δ)/(9+w²), so
M_i = (λw/3)·cos μ_i √(1 + (9/w²) sin²δ_i).

> **Proposition C₃ (weighted Prop. 3.2).** For every book and every w > 0,
> Σ_S − κ(w)(Σ_vv(Z) + wD) ≥ (κ(w)w/3)·D·Φ_w(ψ), where ψ = (ψ₁₂, ψ₁₃, ψ₂₁, ψ₂₃, ψ₃₁, ψ₃₂) and
>
>     Φ_w(ψ) = Σ_{i=1}^{3} cos μ_i √(1 + (9/w²) sin² δ_i) − 3 + (3/(2w)) Σ_{i<j} |sin ψ_ij + sin ψ_ji|.
>
> For w = 1 this is Proposition 3.2 of the first version: Σ_S − κΣ_T(Z) ≥ (D/√10)·Φ with Φ = Φ₁.

No relation between the six angles is used, except that each lies in [−π/2, π/2]. So Φ_w ≥ 0 on the whole cube
suffices for every hub pattern: interior hubs, and paths through u₁ or u₂.

*Algebraic form [P].* Substitute σ = sin ψ ∈ [−1,1] and c = cos ψ = √(1−σ²) ≥ 0. Since cos μ_i ≥ 0,
(c_ij + c_ik)² + K(σ_ij − σ_ik)² = 4 cos² μ_i (1 + (K−1) sin² δ_i), so with K = 1 + 9/w²

    Φ_w(σ) = ½ Σ_i √((c_ij + c_ik)² + K(σ_ij − σ_ik)²) − 3 + (3/(2w)) Σ_{i<j} |σ_ij + σ_ji|   on [−1,1]⁶.   (3.5)

For w = 1, K = 10, and **(CL*)** is the statement Φ₁ ≥ 0 on [−1,1]⁶.

Checks: review-fivepoint §2 recomputed every line at w = 1, review-k2m §4 the weighted version. [N]: at w = 1,
200 000 random books (referee; including ρ = 0, v_i = u_k, near-W5; minimum slack +1.5·10⁻⁵) and 2 × 20 000 by the
author; weighted, 40 000 books for each of five w ∈ (0,1] (review-k2m §4); no violation. A careless subgradient at a
hub on the spine (σ_ij = 0) produces apparent violations, so the choice in (3.2) is necessary.

### 3.3 Theorem D: an analytic proof of (CL*) [P-ref; L]

> **Theorem D.** For 0 < w ≤ 1, every K ≥ 9/w² and σ ∈ [−1,1]⁶, the right side of (3.5) with inner constant K is
> ≥ 0. In particular Φ_w ≥ 0 (K = 1 + 9/w²), and (CL*) holds.

*Proof.* Let m := max of the six |σ|, V := Σ_i |σ_ij − σ_ik| (three vertex differences) and
E := Σ_{i<j} |σ_ij + σ_ji| (three pair sums).

1. *Hexagon identity: V + E ≥ 2m.* Going once around the hexagon σ₁₂ — σ₁₃ — σ₃₁ — σ₃₂ — σ₂₃ — σ₂₁ — σ₁₂,
   whose edges are alternately a vertex difference and a pair sum,
   2σ₁₂ = (σ₁₂−σ₁₃) + (σ₁₃+σ₃₁) − (σ₃₁−σ₃₂) − (σ₃₂+σ₂₃) + (σ₂₃−σ₂₁) + (σ₂₁+σ₁₂).
   So 2|σ₁₂| ≤ V + E, and by symmetry the same holds for each of the six variables.
2. Every c_ij ≥ √(1−m²).
3. *Cauchy–Schwarz with one direction for all three vertices.* With the unit vector (√(1−m²), m):
   √(x² + Ky²) ≥ x√(1−m²) + √K·m|y| ≥ x√(1−m²) + (3m/w)|y|, since √K ≥ 3/w.
4. Hence, using 2 for the first term and E ≥ mE (as m ≤ 1) for the last,

       Φ_w + 3 ≥ ½√(1−m²) Σ_i (c_ij + c_ik) + (3m/(2w))·V + (3/(2w))·E
               ≥ 3(1−m²) + (3m/(2w))(V + E) ≥ 3(1−m²) + 3m²/w ≥ 3,

   by 1 and w ≤ 1. ∎

*Lean.* `PortsLean/CLStar.lean`: `clstar_gen` (Φ ≥ 0 for edge weight t ≥ 3 and K ≥ t², all |σ| ≤ 1);
`clstar_weighted` (exactly (3.5), 0 < w ≤ 1); `clstar` ((3.5) at w = 1, i.e. (CL*)); `clstar_weighted_sharp` (any
K ≥ 9/w²); `clstar_K9` (K = 9 at w = 1). The referee also compiled the file (review-k2m §4).

Remarks.
1. *Sharp constants.* At w = 1 the inner constant 10 can be lowered to 9 ("1 + 8 sin²δ" in trigonometric form), and
   9 is optimal: `clstar_K_lt9_fails` gives Φ = √K − 3 < 0 at σ = (1,−1,−1,−1,1,1) for K < 9.
2. *The three-angle inequality (I).* On the slice ψ_ji = −ψ_ij (all hubs interior), with θ₁ = ψ₁₂, θ₂ = −ψ₁₃,
   θ₃ = ψ₂₃, Φ₁ ≥ 0 becomes
   F_c(θ) = Σ_{i<j} cos((θ_i−θ_j)/2)·√(1 + c·sin²((θ_i+θ_j)/2)) ≥ 3 on [−π/2, π/2]³                    (I)
   with c = 9; equivalently z_i = (cos θ_i, √(1+c) sin θ_i) satisfy |z₁+z₂| + |z₁+z₃| + |z₂+z₃| ≥ 6. By Theorem D,
   (I) holds for every c ≥ 8, and **8 is sharp**: F_c(π/2, π/2, −π/2) = √(1+c). [L]: `three_angle_alg` (algebraic
   slice, K ≥ 9), `three_angle` (c ≥ 8), `three_angle_I` (c = 9), `three_angle_corner`. Near 0,
   F₉(θ) = 3 + θᵀQθ + O(|θ|⁴) with Q = (3/4)·Id + (5/4)·J, eigenvalues 3/4, 3/4, 9/2 [P].
3. *Weights above 1.* At the six corners of §3.4, Φ_w = 3/w − 3 < 0 for w > 1, so neither the statement nor the
   method extends beyond w = 1. The refined calibration of §4.4 repairs the corners and gives the cut regime; the
   arc 1 < w < 5/4 stays open.
4. *Another direction in step 3.* The source (k2m/notes.md §3.3) takes sin χ = 3m/√(9+w²); this is also correct
   and is used in §3.4. The direction (√(1−m²), m), as in Lean, needs only K ≥ 9/w². Earlier attempts (hull notes
   §3.5) bounded one pair term at a time; the proof uses one linearisation for all terms and the cyclic telescoping.

*Proof of Theorem 5_w.* If D = 0 see §3.1. If D > 0: by (3.1), Prop. C₃ and Theorem D,
Σ_S − κ(w)(Σ_vv + wD) ≥ (κ(w)w/3)·D·Φ_w ≥ 0. Equality at W5(ℓ, wℓ/3) is (2.1) with m = 3. ∎

### 3.4 Equality cases and uniqueness

- At W5(ℓ,ℓ/3) (D = 2ℓ/3, ρ_i = 3D/2, a_i = D/2) all hubs are at D/2, all ψ = 0, the calibrating vectors
  (3,±1)/√10 are the true directions u_k→v_i, and every inequality in §§3.1–3.2 is an equality.
- *Zeros of Φ₁ [P].* With sin χ = 3m/√10 in step 3 of Theorem D, the chain ends with
  3√(1 − 9m²/10)·√(1−m²) + 3m² ≥ 3, which is strict for 0 < m < 1. At m = 1 the first term forces all c_ij = 0, so
  σ ∈ {±1}⁶, and the 64 sign vectors contain exactly six zeros: for one vertex i and one sign s, ψ_ij = ψ_ik = −sπ/2
  and the other four angles equal +sπ/2. So the zeros of Φ₁ are 0 and these six corners; this replaces the
  numerical statement of the first version. For w < 1 the last step is strict for every m > 0, and 0 is the only
  zero of Φ_w.
- *Uniqueness [P; new in this version, not refereed].* Let five points of a CAT(0) space satisfy
  Σ_S = κ(w)(Σ_vv + wD) with Σ_vv + wD > 0 and 0 < w ≤ 1. Then D > 0 (§3.1), equality holds in (3.1) and in every
  (3.4), and Φ_w(σ) = 0.
  - At a corner all c_ij = 0, so all ρ_i = 0 and the book metric is a tree metric, hence ℓ₁; so
    Σ_S ≥ Σ_vv(Z) + D (§6(c)) and Σ_S − κ(w)(Σ_vv(Z) + wD) ≥ (1 − κ(w))D > 0. Corners give no equality.
  - Hence σ = 0: every exit vector is horizontal, so all y_ij = a_i and all a_i are equal. Equality in (3.4) with
    α_i = β_i = arccos κ(w) gives (ρ_i, a_i) ∥ (3, w) and (ρ_i, D − a_i) ∥ (3, w), so a_i = D/2 and
    ρ_i = 3D/(2w). Equality in (3.1) gives |v_iv_j| = 2ρ_i.

  So the configuration is W5(ℓ, wℓ/3) with ℓ = 3D/(2w): **W5(ℓ,ℓ/3) is, up to scale, the only five-point CAT(0)
  configuration with R = 3/√10.** (The analogue for W_{m+2} via §4.1 is not written out.)

### 3.5 Independent confirmation by interval arithmetic [IV]

Before Theorem D, (CL*) and (I) were proved by interval arithmetic (`tools/ivcert/`: certificates `clstar`, eight
`clnear` orthants at 0, a hand lemma for six corner regions, and `hull3`), verified by `ivcheck` (same Rust code
base) and by `ivcheck2` (Python with Arb; not refereed); covering and region tests were refereed (review-fivepoint
§6). With the hand proof and Lean they are now a redundant confirmation. Details: `ivcert-notes.md` §§0–4.

### 3.6 Remarks and numerical cross-checks

- **What kind of inequality this is.** The quadrilateral (Reshetnyak) inequalities of C.4(b), together with the
  triangle inequalities, give only min R = 0.944606… [N], a root of 58x³ − 14x² − 29x − 9 (PSLQ at 60 digits). So
  Theorem 5 genuinely uses C.4(a) at t ≠ ½, in the book reduction.
- **Toyoda's criterion [N].** By [Toy, Thm 1.3], at most five points embed in a CAT(0) space iff they satisfy the
  Gromov–Sturm box inequalities; minimising R under these gave 0.948683298050505 at W5 in 1000 of 1000 multistarts
  (e3 notebook). Lebedeva's six-point spaces satisfy all box inequalities without embedding in any CAT(0) space
  ([AKP, §7.2]; [Toy24, Thm 3.1]; [Toy24b, Thm 2.4]; see also [LP22]). Theorem K_m uses only five-point subsets.
- **Model spaces [N].** Products of two or three trees and the Euclidean cone over the Heawood graph give 3/√10 at
  W5; trees and Euclidean spaces give 1. Over m-page books min R_w = R_m(w) to ≈ 10⁻¹⁶ (m ≤ 6; review-k2m §5).

---

## 4. K_{2,m}, the proofs of Theorems K and K_m, and the cut regime

### 4.1 Averaging over triples [P-ref; arithmetic L]

> **Theorem B.** Let m ≥ 3, 0 < w ≤ m(m−1)/6, and let u₁, u₂, v₁, …, v_m be points of a CAT(0) space. Then
> Σ_S ≥ R_m(w)·(Σ_vv + w·D), with equality for W_{m+2}(ℓ, 2wℓ/(m(m−1))).

*Proof.* Put w′ = 6w/(m(m−1)) ∈ (0,1]. For each of the C(m,3) triples {i,j,k} apply Theorem 5_{w′} to the five
points u₁, u₂, v_i, v_j, v_k of the same space:

    Σ_{l∈{i,j,k}} (A_l + B_l) ≥ κ(w′)·( |v_iv_j| + |v_iv_k| + |v_jv_k| + w′D ).

Sum over all triples. Each v_l lies in C(m−1,2) triples and each pair in m−2 triples:

    C(m−1,2)·Σ_S ≥ κ(w′)·( (m−2)·Σ_vv + C(m,3)·w′·D ).

Divide by C(m−1,2) = (m−1)(m−2)/2 and use C(m,3)/(m−2) = m(m−1)/6:

    Σ_S ≥ (2κ(w′)/(m−1))·( Σ_vv + wD ),     2κ(w′)/(m−1) = 6/((m−1)√(9 + 36w²/(m²(m−1)²))) = R_m(w).

Equality: every triple of W_{m+2}(ℓ, 2wℓ/(m(m−1))) is W5(ℓ, w′ℓ/3), and (2.1). ∎

No m-page book is needed: Theorem 5_{w′} is applied directly to each five-point subset (review-k2m §5). So K_{2,m} at
weight w is as hard as K_{2,3} at weight 6w/(m(m−1)).

*Lean.* `PortsLean/CLStar.lean`: `k2m_average` (if κ(T_ij + T_jk + T_ik + w′D) ≤ S_i + S_j + S_k for all distinct
i, j, k, with T symmetric, then (2κ/(m−1))(Σ_{i<j}T_ij + w′·m(m−1)/6·D) ≤ Σ_iS_i), `R_eq` (the identity for
2κ(w′)/(m−1)) and `k2m_rate` (the combination). The five-point inequality enters as a hypothesis; Lean does not
connect it to CAT(0) spaces or to Theorem D.

### 4.2 Proofs

**Theorem K.1 and K_m.1.** Let d be an AN price on the m+2 parties with Σ_vv d + wD > 0. By Prop. C.3 it is the
restriction of the metric of a CAT(0) space to m+2 points. By Theorem B (Theorem 5 for m = 3, w = 1),
R_w(d) ≥ R_m(w). By §1.2(d), f*(K_{2,m}(w); k) ≥ R_m(w). This holds over every field: [AN] l. 564–567 says that "the
field only supplies the scalars", and Strassen's theorem holds over every field.

**Theorem K.2 and K_m.2.** Corollary H_m, with border protocols as in §1.2(c); item 1 gives equality in its range.

**Theorem K_m.3 [P-ref: review-k2m §7].**
- *Routing.* Send each v_iv_j half through u₁ and half through u₂, and u₁u₂ equally through the v_j: each edge
  carries f((m−1)/2 + w/m). The path metric of K_{2,m} has the same R_w, so no routing does better. For m = 3, w = 1
  the dual inequality 3Σ_T d ≤ 4Σ_S d is [L] (`W5.lean`: `flow_bound`).
- *Cuts.* For X with a = |X ∩ {u₁,u₂}| and b = |X ∩ {v_i}|, the cut separates a(m−b) + (2−a)b supply pairs and
  b(m−b) + w·[a = 1] demand weight. The least ratio is 2/(m−1) (a ∈ {0,2}, b = 1) or m/(⌊m²/4⌋+w) (a = 1,
  b = ⌊m/2⌋). Brute force over all subsets agrees for m ≤ 6.
- *Strictness.* R_m(w) < 2/(m−1) for w > 0, and R_m(w) > routing since (m(m−1)+2w)² > m²(m−1)² + 4w². With
  β = ⌊m²/4⌋, R_m(w) < m/(β+w) iff w < w_c(m) := (m²(m−1)² − 4β²)/(8β), and m(m−1)/6 < w_c(m): w_c(3) = 5/4; for
  m ≥ 4, w_c(m) ≥ (3m−2)(m−2)/8 > m(m−1)/6, since 5m² − 20m + 12 > 0.

**Theorem K_m.4.** Item 2 and §5. **K_m.5:** Corollary E (§4.4). ∎

Numbers for w = 1:

| m | routing 2m/(m(m−1)+2) | R_m(1) | cut 2/(m−1) | R_m(1)/routing |
|---|---|---|---|---|
| 3 | 0.7500 | 0.948683 = 3/√10 | 1 | 1.2649 |
| 4 | 0.5714 | 0.657596 = 8/√148 | 0.6667 | 1.1508 |
| 5 | 0.4545 | 0.497519 = 10/√404 | 0.5 | 1.0945 |
| 6 | 0.3750 | 0.399114 = 12/√904 | 0.4 | 1.0643 |

The gain over routing, (m(m−1)+2w)/√(m²(m−1)²+4w²), increases in w on the proved range and equals 4/√10 at its top
w = m(m−1)/6, for every m. At w = 1 it is ≈ 1 + 2/(m(m−1)), and cut bound/R_m(1) = √(1 + 4/(m²(m−1)²)). So among
the K_{2,m}(1), K_{2,3} has the largest proved gain over routing and, if contracting fails, the largest gap to the
cut bound.

### 4.3 Remark: the direct m-page calibration fails [P-ref]

The calibration of §3.2 works for m pages with any constant λ < 2/(m−1): with V_i = Σ_{j≠i} e_ij = |V_i|(cos μ_i,
sin μ_i) and M_i = cos μ_i √(1 − λ²|V_i|²/4), Σ_S − λ(Σ_vv(Z) + wD) ≥ D·Br with Br = Σ_iM_i − λw +
(λ/2)Σ_{i<j}|ε_ij|, and all lengths cancel. At λ = R_m(w) this is tight at W_{m+2}. But Br ≥ 0 is **false** for
every even m ≥ 4 and every w > 0, and for odd m ≥ 5 when w > m(m−1)/(2√(m²−1)) (m = 5: w > 2.04, inside the range).
Take the collinear book with all ρ_i = 0 and v₁, …, v_m different interior points of the spine, numbered upwards.
The hubs can be taken interior and the exit vectors can be taken vertical, so V_i = (0, 2i − m − 1): for even m,
Br = −λw < 0; for odd m, Br = 1 − λw. Nearby books with small ρ_i > 0 have unique hubs and still Br < 0 (m = 4,
w = 1: Br = −0.650, true left side +2.03; review-k2m §7). The cause is parity: m−1 exit vectors at a vertex cannot
cancel when m−1 is odd. Theorem B avoids the issue.

### 4.4 The cut regime: Theorem E [(a) P-ref; (b), (c) P-ref + IV]

Let λ₁ = 0.7665884… be the real root of 4λ³ − 8λ² + 9λ − 4 and w₁ := (3 − 2λ₁)/λ₁ = 1.9134429…. The three levels
are (a) w₀ = w₁, (b) w₀ = 4/3, (c) w₀ = 5/4; put λ₀ := 3/(2+w₀) = λ₁, 9/10, 12/13.

> **Theorem E.** For five points of a CAT(0) space (§1.3) and 0 < λ ≤ λ₀: Σ_S ≥ λΣ_vv + (3 − 2λ)D. Equivalently,
> Σ_S ≥ (3/(2+w))(Σ_vv + wD) for every w ≥ w₀. At level (c) this is (★) 13Σ_S ≥ 12Σ_vv + 15D. Equality holds on
> the whole family of line metrics (v_i = u₁, v_j = u₂, v_k anywhere on [u₁,u₂]), for every λ; the cut metric of
> {u₁, v₁} is the case v_k = u₂.

(3 − 2λ = λw at λ = 3/(2+w); smaller λ follow by convexity from λ₀ and (λ, η) = (0, 3), valid as A_i + B_i ≥ D.)

> **Corollary E (unconditional exact rates).** For every field k and each level: f*(K_{2,3}(w); k) = 3/(2+w) for
> w ≥ w₀, and f*(K_{2,4}(w); k) = 4/(4+w) for w ≥ 2w₀ (3.8268858, 8/3, 5/2). Routing gives 3/(3+w) and 4/(6+w).

Level (a): hand proof below, refereed (review-thmE.md). Levels (b), (c): two certificates [IV] plus Lemma R and
convexity; the referee checked the implications (item 6), not the certificates.

*Upper bound.* The cut {u₁, v₁} is crossed by three supply wires (u₁v₂, u₁v₃, u₂v₁) and by the demand v₁v₂, v₁v₃
(rate f) and u₁u₂ (rate wf). Its flattening rank is a spectral point over every field (§6(c)), so (2 + w)f ≤ 3.
Over all 15 bipartitions the least ratio is min(1, 3/(2+w), 3/w), i.e. 3/(2+w) for w ≥ 1 (review-thmE item 1). For
K_{2,4}: the cut {u₁, v₁, v₂}, four supply wires against 4 + w (least cut for w ≥ 2). The cut value equals
κ(w) = 3/√(9+w²) at w = 5/4 and is smaller above (for K_{2,4}: at w = 5/2).

*Proof of Corollary E.* Lower bound: §1.2(d), C.3 and Theorem E (irrational w via rational w′ ↓ w). For K_{2,4}
apply Theorem E at w′ = w/2 ≥ w₀ to the four triples of v's (each v in three, each pair in two):
3Σ_S ≥ (3/(2+w′))(2Σ_vv + 4w′D), i.e. Σ_S ≥ (4/(4+w))(Σ_vv + wD). Upper bounds: the cuts. (For m ≥ 5 triples give
only m/(m(m−1)/3 + w), below the cut bound.) ∎

*Example, w = 2.* f* = 3/4 over every field, against routing 3/5: from n copies of the six binary wires one obtains
asymptotically 0.75n binary wires on each v_iv_j and 1.5n on u₁u₂, and no more; routing obtains 0.6n and 1.2n.

**Refined calibration.** In §3.2 the angles satisfy cos α_i + cos β_i = λP_i. Since ρ_i ≥ 0, ≥ suffices: any
p_i, q_i ∈ ℝ² with |p_i|, |q_i| ≤ 1 and

    p_{i,x} + q_{i,x} ≥ λP_i,        p_{i,y} − q_{i,y} = λQ_i                                            (4.1)

may replace (cos α_i, sin α_i), (cos β_i, sin β_i) in (3.4), and the summation of §3.2 gives
Σ_S − λΣ_vv(Z) − ηD ≥ D·(Σ_i (p_{i,y} + q_{i,y})/2 + (λ/2)(E₁ + E₂) − η). Let sin γ_i = λ cos δ_i, γ_i ∈ [0, π/2)
(so γ_i = π/2 − ν_i), and N_i := cos((γ_i − |μ_i|)₊); v_i is *linear* if |μ_i| ≥ γ_i (N_i = 1), *curved* otherwise.

> **Proposition C′ [P-ref].** For every book, λ ∈ (0,1) and η: Σ_S − λΣ_vv(Z) − ηD ≥ D·Br′, where
> Br′ := Σ_i N_i − (λ/2)X − η, X := Σ_i |Q_i| − Σ_{i<j} |ε_ij|.

*Proof.* Meet (4.1) with (p_{i,y} + q_{i,y})/2 = N_i − (λ/2)|Q_i|, where (λ/2)|Q_i| = sin γ_i sin|μ_i|. Curved: the
angles of §3.2, with (p_y + q_y)/2 = cos γ_i cos μ_i = N_i − sin γ_i sin|μ_i|. If μ_i ≥ γ_i:
p_i = (0,1), q_i = (√(1 − (1 − λQ_i)²), 1 − λQ_i), giving 1 − λQ_i/2; here 0 ≤ λQ_i < 2, and p_x + q_x ≥ λP_i ⇔
2Q_i ≥ λ(P_i² + Q_i²) ⇔ sin μ_i ≥ sin γ_i. If μ_i ≤ −γ_i: mirror image. ∎

The bracket of §3.2 is Σ_i cos(γ_i − |μ_i|) − (λ/2)X − η ≤ Br′; the gain is where α_i or β_i would exceed π/2. At the
six corners of §3.3 remark 3, Br′ = 3 − 2λ − η.

*Sign cases* (σ_ij = sin ψ_ij). (X1) If Q₁, Q₂, Q₃ have one sign (*unfrustrated*), X ≤ 0, as Σ|ε_ij| ≥ |ΣQ_i|.
(X2) Otherwise, after renumbering and possibly σ ↦ −σ (which preserves N_i, |Q_i|, |ε_ij|), Q₁ ≤ 0 ≤ Q₂, Q₃
(*frustrated at v₁*). Always, by a + b − |a − b| = 2 min(a,b),

    X = 2 min(−σ₁₂, σ₂₁) + 2 min(−σ₁₃, σ₃₁) − 2(−σ₂₃ − σ₃₂)₊.                                            (4.2)

*One-vertex lemmas.* For exit angles ψ, ψ′ put μ = (ψ+ψ′)/2, d = |ψ−ψ′|/2, sin γ = λ cos d, N = cos((γ−|μ|)₊),
Q = 2 cos d sin μ, τ = √(1−λ²); so cos γ ≥ τ.
- (V1) 1 − N ≤ (1−τ)(1 − |Q|/2). For 0 ≤ μ ≤ γ (μ ≥ γ is trivial, μ < 0 symmetric), with t = (1−τ)/λ ∈ (0,1),
  right minus left is g(μ) = cos γ cos μ + (1−t) sin γ sin μ − τ: concave on [0, γ], g(0) = cos γ − τ ≥ 0,
  g(γ) = 1 − t sin²γ − τ ≥ (1−τ)(1−λ) ≥ 0.
- (V2) If μ ≥ 0, then 1 − N ≤ λ²(1 − s), s = sin(μ + d) the larger exit sine (mirror for μ ≤ 0). For 0 ≤ μ ≤ γ
  let φ = π/2 − d: sin γ = λ sin φ, γ ≤ φ, 1 − s = 2 sin²((φ−μ)/2), 1 − N = 2 sin²((γ−μ)/2), and
  h(μ) = λ sin((φ−μ)/2) − sin((γ−μ)/2) has h′ ≥ 0 (as 0 ≤ γ−μ ≤ φ−μ) and h(0) ≥ 0, since
  sin(γ/2) = λ sin(φ/2) cos(φ/2)/cos(γ/2) ≤ λ sin(φ/2).

*Proof of Theorem E, level (a).* D = 0: Σ_vv ≤ Σ_S. Let D > 0, η = 3 − 2λ, 0 < λ ≤ λ₁. By (3.1) and Prop. C′ it
suffices that Σ_i(1 − N_i) ≤ (λ/2)(4 − X).
- *Unfrustrated:* X ≤ 0, 1 − N_i ≤ 1 − τ, and 3(1−τ) ≤ 2λ ⇔ λ ≤ 12/13.
- *Frustrated at v₁:* with ϑ := (1−τ)/(2λ) ∈ (0,1), (4.2) and max(x,y) ≥ ϑx + (1−ϑ)y give
  (λ/2)(4 − X) ≥ λϑ(2 − |Q₁|) + λ(1−ϑ)[(1−σ₂₁) + (1−σ₃₁)]. By (V1), 1 − N₁ ≤ λϑ(2 − |Q₁|); by (V2) (μ₂, μ₃ ≥ 0),
  1 − N₂ ≤ λ²(1−σ₂₁) and 1 − N₃ ≤ λ²(1−σ₃₁). The difference is ≥ (λ(1−ϑ) − λ²)[(1−σ₂₁) + (1−σ₃₁)] ≥ 0 iff
  G(λ) := 2λ(1−λ) − (1−τ) ≥ 0.
- *The cubic:* G(0) = 0, G′(0) = 2; G(λ) = 0 with λ > 0 forces τ = 1 − 2λ + 2λ² and, squaring,
  4λ³ − 8λ² + 9λ − 4 = 0, whose derivative has no real root. So G ≥ 0 on (0, λ₁]. ∎

λ₁ is where this argument stops: numerically Br′(·; λ, 3 − 2λ) ≥ 0 on the cube up to λ = 12/13 [N: review-thmE item 3].

**Levels (b) and (c).**

> **Lemma R [P-ref].** Let 0 < λ ≤ 12/13 and η ≤ min(3τ, 3 − 2λ). Then Br′ ≥ 0 on [−1,1]⁶ outside
> 𝓕′ := {frustrated at some v_i, v_i curved, and another vertex curved}.

*Proof.* Write Br′ = (3 − 2λ − η) + (λ/2)(4 − X) − Σ_i(1 − N_i). Unfrustrated: Br′ ≥ 3τ − η. Frustrated at v₁, v₁
linear: (V2) at v₂, v₃ and (4.2) give Br′ ≥ 3 − 2λ − η. v₂, v₃ linear: (V1) gives 1 − N₁ ≤
((1−τ)/2)[(1+σ₁₂) + (1+σ₁₃)] ≤ λ[…], and (λ/2)(4−X) ≥ λ[(1+σ₁₂) + (1+σ₁₃)]. ∎

By the symmetries it remains to prove Br′ ≥ 0 on 𝓕′₁ = {Q₁ ≤ 0, Q₂ ≥ 0, Q₃ ≥ 0, 2|Q₁| ≤ λW₁, 2Q₂ ≤ λW₂},
W_i = (c_ij + c_ik)² + Q_i², c = √(1−σ²); on curved vertices N_i = ½√(τ²(c_ij + c_ik)² + (σ_ij − σ_ik)²) + (λ/2)|Q_i|.
Certified [IV] (`ivcert-notes.md` §5):
- **S(9/10):** Br′(σ; 9/10, 6/5) ≥ 0 on 𝓕′₁ (numerical minimum +0.0627; certified only ≥ 0);
- **(CL\*\*₀):** Br′(σ; 12/13, 15/13) ≥ 0 on 𝓕′₁, equality at σ = 0.

As 6/5 ≤ 3τ(9/10) and 15/13 = 3τ(12/13), Lemma R, Prop. C′ and (3.1) give Σ_S ≥ (9/10)Σ_vv + (6/5)D and (★); one
λ₂ covers all smaller λ. Near λ = 12/13 the minimum over 𝓕′ is 3τ − η, at σ = 0 [N] (+0.0158 at λ = 0.92).

*Certificates.* 16 closed pieces (signs of ε_ij; v₃ curved or linear) on which the bracket is smooth where all c > 0.
The Rust prover `ivcert` closed all of them: 23.3M leaf boxes for S(9/10), 62.1M for (CL\*\*₀), with eight orthant
certificates at σ = 0. Every certificate was verified by `ivcheck` (same code base) and by `ivcheck2` (Python with
Arb: own piece test, gradient and origin lemma; reads only the box lists). Both encodings for these two problems
were written by the same author, in one session, with shared piece and coordinate conventions. A bug in the new code
of `ivcheck2` (gradient not scaled) was found by a mutation test and fixed before the reported runs. Not refereed.

**Below 5/4.** W5(ℓ, wℓ/3) ⊂ tripod × ℝ has R_w = κ(w) < 3/(2+w) for w < 5/4 (2.1), so CAT(0) geometry cannot give
the cut value there; numerically the CAT(0) minimum is min(κ(w), 3/(2+w)) at every tested w (two codes: `k2m/wscan.py`,
review-thmE item 4). For w < 5/4, f* ≤ κ(w) holds only when contracting fails (Corollary H_m),
and the matching lower bound κ(w) is proved only for w ≤ 1 (Theorem 5_w). For 1 < w < 5/4 the unconditional bound is the chord: valid (λ, η) form a
convex set containing (κ(1), κ(1)) and (λ₀, 3 − 2λ₀), and f* is at least the λ where the segment meets η = wλ.

| w | proved, level (a) | proved, level (c) | κ(w) | cut 3/(2+w) | routing |
|---|---|---|---|---|---|
| 1.1 | 0.9246 | 0.9383 | 0.9389 | 0.9677 | 0.7317 |
| 1.2 | 0.9018 | 0.9281 | 0.9285 | 0.9375 | 0.7143 |
| 1.5 | 0.8395 | 0.8571 = cut | 0.8944 | 0.8571 | 0.6667 |

### 4.5 Other pinned networks

For supply G and demand H, f_flow ≤ f_CAT(0) ≤ f*(k) ≤ f_cut, f_CAT(0) the infimum of the ratio over CAT(0)
configurations (§1.2, C.3). The network is *pinned* if f_CAT(0) is already the infimum over finite subsets of
(m-pod) × ℝ, which are prices when contracting fails (proof of Corollary H_m); *cut-pinned* if f_CAT(0) = f_cut, so
that f* = f_cut unconditionally (Corollary E); *two-apex* if every supply wire has an end in {u₁, u₂}.

> **Proposition B (book principle) [P-ref: review-thmE item 7].** For a two-apex network f_CAT(0) is the infimum
> over m-page books (D = 0 included); it is attained on the closed parameter set, which contains degenerate books
> (ρ_i = 0, points on the spine), and minimisers are often of this kind.

*Proof.* (3.1) leaves supply terms and D unchanged and only enlarges v_iv_j distances; books are CAT(0)
(Reshetnyak gluing [BH99, II.11.1]). ∎

> **Proposition T [P-ref: review-thmE item 7].** Let H be r-regular on v₁, …, v_m with a fractional triangle
> decomposition (x_t ≥ 0, Σ_{t∋e} x_t = 1 for every edge e). For supply K_{2,m}, demand H at rate f and u₁u₂ at wf,
> 0 < w ≤ mr/6: f_CAT(0) = 2m/√(m²r² + 4w²), attained at W_{m+2}(ℓ, 2wℓ/(mr)); the network is pinned.

*Proof.* Σ_{t∋i} x_t = r/2, Σ_t x_t = mr/6. Summing Theorem 5_{w′}, w′ = 6w/(mr) ≤ 1, with weights x_t:
(r/2)Σ_S ≥ κ(w′)(Σ_H + (mr/6)w′D), and 2κ(w′)/r = 2m/√(m²r²+4w²). Equality by Cauchy–Schwarz as in (2.1). ∎
(H = K_m is Theorem B. No non-regular version is stated.) Example: K_{2,6} with octahedron demand (r = 4, x_t = ½),
w = 1: f_CAT(0) = 12/√580 = 0.498273, routing 6/13, cut 1/2.

*Three distinct values* [N: books; the last two also Toyoda's criterion]: K_{2,5} with pentagon demand, w = 1 (no
triangles): 5/6, 5/√26 = 0.980581 (at W₇), 1. The five-point instance with supply u₁v₁, u₁v₂ and demand v₁v₂ doubled:
0.8, 0.965136 (asymmetric book), 1. K_{2,3}(1) plus a supply wire u₁u₂ of capacity ½: 7/8, 0.98675, 1. The optima
found lie in (pod) × ℝ, so these are pinned [N].

*K_{3,3}* (demand: the six pairs inside the sides; not two-apex): routing 3/4, cut 1. A valid inequality
Σ_S ≥ λΣ_vv + ηD on five points, applied to the six sub-instances, gives f_CAT(0) ≥ (3λ + η)/4 [P-ref]: 3/√10 by
Theorem 5, 0.975 at level (b), 51/52 = 0.9808 at level (c); these are unconditional lower bounds on f*.

*Conjectures* (open problem 7). **W** [C; N for m = 3, 4, 5]: on K_{2,m}(w) the CAT(0) minimum of R_w is
min(R_m(w), m/(⌊m²/4⌋ + w)) for all w; for m = 3 the arc 1 < w < 5/4 is missing. **P** [C; N]: every two-apex network
has an optimal book with all hubs on the spine, hence is pinned. **K_{3,3}** [C; N]: f_CAT(0) = 1, which would give
f* = 1 over every field, unconditionally.

---

## 5. Consequences and the falsifiable prediction

**(i)** By Corollary H_m, a protocol over k of rate > 3/√10 shows that W5, and hence N5, ρ₂ and ρ₃, are not prices
over k. So Contracting(k) holds [P-ref]. A protocol over ℚ also counts over ℝ, ℂ and ℚ̄. The same holds for a
protocol on K_{2,m}(w) of rate > R_m(w), for any w > 0.

**(ii)** If char k = 0, Contracting(k) implies 3-SAT in 2^{O(n^{1−δ})}·poly, by [CE]. Two routes:
- **Theorem R** uses [AN] only. Its non-uniform form (advice of size poly(n)) is refereed (review-theoremR.md); the
  uniform form rests on a one-reader audit of [AN]'s Lean proof terms (review-uniformity.md), not a Lean theorem.
- **Theorem A** (contracting ⇒ ports; refereed, review-theoremAB.md) uses [AN] F.6 and OpenAI's HC Thm 4.2; the
  step from ports to 3-SAT uses OpenAI's IM Thm 7.1, which we have not reviewed.

**(iii) Prediction.** Under the non-uniform weak exponential-time hypothesis, the following holds via Theorem R in
its refereed form. Under the uniform Weak ETH it holds via the audit or via Theorem A + IM 7.1.

> For every field k of characteristic 0, no asymptotic restriction protocol from the six binary wires of K_{2,3}
> to the four demand wires has rate above 3/√10 = 0.948683…. The same holds for border protocols of
> approximation degree 2^{o(n)}. Rates arbitrarily close to 3/√10 are attained (unconditionally, by item 1).
> More generally, no protocol on K_{2,m}(w) has rate above R_m(w).

The prediction can be refuted by an explicit object, for example a single restriction over ℚ from wires of
dimension 10 on the six edges to wires of dimension 9 on the four demand pairs (rate ≈ 0.954). It would imply
Contracting(ℚ), and with [CE] a 2^{O(n^{1−δ})} algorithm for 3-SAT.

**(iv) Product closure.** If f*(k) > 3/√10, then tripod × segment is not a price space over k, although tripod and
segment are. So ℓ₂ products of spectral spaces are then not always spectral [P].

---

## 6. Small exact facts (Theorem K.4)

**(a) Rate 1 single-shot is impossible [P] (from the e3 notebook, re-derived here).** Suppose
(⊗_p A_p) S_D = T_D, where every supply and demand wire has dimension D ≥ 2, over any field.
Each cut {v_i} has flattening rank D² on both sides, so each A_{v_i} is invertible, and
(A_{u₁} ⊗ A_{u₂}) S_D = (⊗_i A_{v_i}⁻¹) T_D. The left side is M₁ ⊗ M₂ (M_k = A_{u_k} applied to the wires at u_k),
whose rank across {u₁,u₂} is rk_{u₁}(M₁)·rk_{u₂}(M₂) ≥ rk_{u₁}(M₁) = its rank across {u₁}. Invertible maps at the
v's preserve both ranks; for T_D the rank across {u₁,u₂} is 1 and across {u₁} it is D. So D ≤ 1, a contradiction. The same argument excludes every
instance in which the v-cuts are tight and the u₁u₂ wire has dimension ≥ 2.

**(b) Bond dimension 2, border, over ℂ [P].** Suppose S₂ degenerates to a tensor with v₁v₂ = v₂v₃ = v₁v₃ = 2 (any
dimension on u₁u₂).
Compose with e₁* at u₁ and at u₂. The target becomes ⟨2,2,2⟩ on v₁, v₂, v₃; the source becomes
(⊗A_v(ε))(X(ε) ⊗ Y(ε)) with X, Y ∈ (ℂ²)^{⊗3}, of border rank ≤ 4. Border rank ≤ 4 is a closed condition, but the
border rank of ⟨2,2,2⟩ is 7 [Lan06].

**(c) ℓ₁ metrics [P; L].** For a cut metric δ_X, let a = |X ∩ {u₁,u₂}| and b = |X ∩ {v₁,v₂,v₃}|. The cut crosses
a(3−b) + (2−a)b supply pairs and [a = 1] + b(3−b) demand pairs: for a = 0, 2b against b(3−b); for a = 1, 3 against
1 + b(3−b) ≤ 3; a = 2 by complementation. So each cut has Σ_S ≥ Σ_T, and so does every nonnegative combination:
R ≥ 1 on the cut cone. This is [L] (`W5.lean`: `cut_ineq`, all 32 cuts; `w5_not_cut_combination`). The cut {v₁}
attains 1 (`cut_v1`), and so f* ≤ 1, since a flattening rank is a spectral point.

Explicit spectral points with ℓ₁ wire metrics (`ideas-ports.md` §4.1): flattening ranks (cut pseudometrics);
Strassen's support functionals (every field) and the quantum functionals of Christandl–Vrana–Zuiddam (over ℂ), which
give star metrics d(x,y) = θ_x + θ_y; the laminar upper quantum functionals [BCFLN26; VZ26, Thm 1.9] and the upper
support functionals [SDW26; ALP26; both known to us only from search-engine excerpts], whose wire metrics on graph
tensors are nonnegative combinations of cut metrics (the literature check's own computation, not refereed, not
stated in those papers). The spectrum on graph tensors is log-star-convex [WZ26, Thm 12.23; over every field VZ26,
Thm 4.12]. ℓ₁-embeddability survives pull-backs, nonnegative multiples and pointwise limits, so none of these points,
nor any price obtained from one of them by those operations, certifies an upper bound below 1. (A sum of cut metrics
need not be a price: the path metric of the 4-cycle is a sum of two cuts and violates the CN inequality.)

**(d) Routing [P; L].** Routing achieves exactly 3/4 (§4.2; `flow_bound`); the path metric of K_{2,3} has R = 6/8.

---

## 7. An explicit family above routing

Theorem K.1 is non-constructive. An explicit asymptotic family above 3/4 comes from the crossing identity of [AN]
(`protocol/notes.md`; refereed once, `review-protocol.md`: no fatal gap). It is not part of Theorem K.

*Construction.* Split the u₁u₂ demand into three factors and pair each with one wire v_iv_j (log-dimensions 1 : 3).
The crossing identity [AN, Prop. B.2] writes each pair as a sum of polynomially many integer tensors whose log-ranks
across the two crossing cuts satisfy r² + r′² ≤ 2(p²+q²). By [AN, Lemma A.3] each term is a restriction of a
three-wire network through u₁ or through u₂, chosen per term over many blocks; the parties share the term index as a
GHZ index, at O(1) supply copies per block. The supply needed is the value n*(B) of a finite zero-sum game with B
rank buckets per pair. The tensors are integer, so this works over every field.

> **Proposition P1 [P-ref].** For every B there are explicit restrictions T^{⊗m} ≤ S^{⊗n}, over every field, with
> m/n → 1/n*(B). Exact certificates give n*(B) ≤ c_B for B = 2, 4, 8, 16, 32, so the rate is ≥ 0.83132 (B = 2) and
> ≥ 0.83671 (B = 32).

The written proof is the sketch of `protocol/notes.md` §2.3; the referee checked each step (shared index, rank
accounting, adaptive rounding, all o(n) terms).
- *Certificates* (`protocol/certificates/`). A verifier using only exact fractions checks, for every term type, an
  explicit mixture with all six edge loads ≤ c_B; square roots are rounded up, which only raises loads. B = 2 is
  also in Lean with the looser constant 1.20292 (`ProtocolCert.lean`: `n_star_two_le`, game arithmetic only).
- *Closed form at B = 2.* n*(2) = 29/27 + 11√10/270 = 1.2029076084 (root of 270x² − 580x + 307). The upper bound is
  exact: an explicit mixture (α = 7/18 − √10/90, γ = 5/9 − 13√10/90) makes the three distinct loads equal to this
  number (symbolic check by the executor). An exact rational dual price gives n*(2) ≥ 1.2029076080, so the upper and
  lower rational bounds agree to nine decimals.
- *The limit [N].* In floating point n*(B) → (4+√10)/6 for B = 8, …, 128, with gap ≈ 0.048/B. The all-middle term
  type has value exactly (4+√10)/6 [P-ref]; that it is the worst type is only numerical. So **the limit rate
  6/(4+√10) ≈ 0.83772 rests on a numerical claim.** It is also the ceiling without nesting: the minimum of R over
  five-point metrics satisfying the triangle inequalities and all instances of [AN, Prop. B.3] is 0.83772 [N].
- *Size.* With the proved rank bounds, the first instance above 3/4 in a one-parameter scan has demand wires of
  dimension ≈ 2¹²⁸ per block (rate 0.7529 on float LPs; not a minimality statement). Up to class dimensions 5 × 5 the
  middle terms have full rank (exact, mod p), so there is no gain at sizes reachable by dense computation.
- *Searches [N].* Least-squares searches, single-shot at uniform supply dimension 2 to 5 and on non-uniform demands
  at dimension ≤ 4, found no protocol above 3/4 (best relative residual 0.64 at 4 → 3).

---

## 8. Status table

| Step | By hand | Referee | Lean | Interval / exact | Numerical |
|---|---|---|---|---|---|
| (1.1) rate formula, Strassen 1988 | [cl] | — | — | — | — |
| §1.2(a)–(c) | [P] | review-hull §6 | — | — | — |
| §1.2(d) weighted duality | [P] | review-k2m §0 (fix applied) | — | — | — |
| C.3, C.4(a),(f), thm_cn, thm_alt_rank_price | [AN] | not refereed by people; Lean by [AN], not built by us | [AN] | — | — |
| Lemma P, Corollary P | [P] | review-k2m §1 | q = 2: `ranks_one`, `ranks_two` | rank tables r ≤ 6 | — |
| Lemma H_m | [P] | review-hull §§3–5 (m = 3); review-k2m §3 | **no** (hypothesis `lemmaH`) | — | model check (m = 3) |
| (2.1); W5 ⊂ diamond; Corollary H_m | [P] | review-hull; review-k2m §3 | m = 3: `w5_ratio`, `ratio_strict`, `model_n5`, `w5_in_diamond`, glue `w5_price_of_rho_price` | — | yes |
| §3.1 books; §3.2 Prop. C₃ | [P] | review-fivepoint §§1–2 (w = 1); review-k2m §4 | no | — | ≈ 2.4·10⁵ books (w = 1), 2·10⁵ (weighted) |
| Theorem D, (CL*), sharp inner constant 9 | [P] | review-k2m §4 | `clstar_gen`, `clstar_weighted`, `clstar`, `clstar_weighted_sharp`, `clstar_K9`, `clstar_K_lt9_fails` | w = 1: `clstar` + 8 × `clnear`, two checkers | chain steps on 4·10⁵ points |
| (I) with constant 8, sharp | [P] | via Theorem D | `three_angle_alg`, `three_angle`, `three_angle_I`, `three_angle_corner` | c = 9: `hull3` | — |
| Zeros of Φ₁; uniqueness of W5 | [P] (uniqueness new) | **not refereed** | — | 64 sign vectors | agrees with searches |
| Theorem 5_w; Theorem B | [P] | review-fivepoint; review-k2m §§4–5 | Theorem B arithmetic: `k2m_average`, `R_eq`, `k2m_rate` | — | Toyoda SIP; m-page books |
| K_m.3 routing, cuts, strictness; §4.3 | [P] | review-k2m §7 | m = 3: `flow_bound`, `cut_ineq`, `cut_v1` | — | LPs, brute-force cuts |
| K.3 | [CE] | Theorem R non-uniform: refereed; uniform: audit; Theorem A: refereed; IM 7.1: not reviewed | arithmetic only (`ThmR.lean`, `ThmA.lean`) | — | — |
| K.4(a), (b), (c) | [P] ((b) uses [Lan06]) | — | (c): `cut_ineq`, `w5_not_cut_combination`, `cut_v1` | — | ALS floors √(5/8), 0.6695 |
| §7 family, rate ≥ 0.83671 | [P] (sketch-level write-up) | review-protocol | B = 2 game: `n_star_two_le` | rational certificates B ≤ 32 | limit 0.83772 only [N] |
| Theorem E (a), w ≥ w₁: Prop. C′, (X1), (X2), (V1), (V2), cubic; Corollary E | [P] | review-thmE (passed) | no | — | books, [−1,1]⁶, five-point searches (referee) |
| Theorem E (b), w ≥ 4/3 | (a) + Lemma R + convexity [P] | review-thmE item 6 (implications only) | no | S(9/10): ivcert, ivcheck, ivcheck2; 23.3M boxes; both encodings by one author; not refereed | min +0.0627 |
| Theorem E (c), w ≥ 5/4, (★) | as (b) | as (b) | no | (CL\*\*₀): same tools and caveat; 62.1M boxes | min 0, at σ = 0 |
| §4.5 Prop. B, Prop. T; K_{3,3} bound (3λ+η)/4 | [P] | review-thmE item 7 | — | — | three-value instances [N] |
| Conjectures W, P; f_CAT(0)(K_{3,3}) = 1 | [C] | — | — | — | [N] |

**Trust base of item 1.**
1. [AN] Theorem C.1 (`thm_cn`) and Prop. C.3, with Lemma C.4(a), in the direction price ⇒ CAT(0) embedding. C.4(a)
   is a standard CAT(0) fact. Alternatively [EG] Thm 4.3 with Cor. 3.4 (§1.3); item 1 then uses nothing from [AN].
2. Strassen's spectral theorem [Str88], or [AN] Theorem A.6 with the cover-to-restriction step of §1.1.
3. §3.1 and Prop. C₃: elementary, checked by hand by referees and numerically.
4. Theorem D: six lines by hand, and in Lean (`clstar_weighted`, `clstar`).
5. For m ≥ 4: Theorem B, whose arithmetic is in Lean (`k2m_rate`).
6. Not needed: interval arithmetic, Reshetnyak gluing, Toyoda's theorem, m-page books, uniqueness, anything from
   OpenAI.

**Weakest points.** The computer is no longer part of item 1. What remains:
- the **book reduction and the calibration** (§§3.1–3.2): proved by hand and checked by one referee each
  (review-fivepoint at w = 1; review-k2m for the weighted form), with numerical tests, but not in Lean;
- the **imported statements from [AN]** (C.1/C.3, C.4(a); for item 2 also C.4(f) and `thm_alt_rank_price`): the
  paper is machine-generated and not refereed by people, and we have not built its Lean.

For item 2 there is in addition Lemma H_m, refereed twice but not in Lean (Mathlib has no CAT(0) theory).

**Trust base of item K_m.5 (Theorem E).** (a): points 1, 2 above, §3.1, Prop. C′, (X1), (X2), (V1), (V2) and the
cubic (by hand, one referee, not in Lean), and one flattening rank. (b), (c) add Lemma R (refereed) and the
certificates: the two encodings of Br′ and 𝓕′₁ (`ivcert` `k2m.rs`, `ivcheck2`) were written by the same author, so the
checkers are independent in arithmetic and code but not in the reading of the specification; binary64 with
correctly rounded fma and Rust, or python-flint/Arb. Certificates and code are not refereed.

---

## 9. Open problems

1. **Explicit protocols between 0.8377 and 3/√10** (§7). They need the crossing construction nested, with a
   finite-depth form of [AN, Lemma C.2] and explicit constants. Also open: a proof that the all-middle type is the
   worst, which would make the limit 6/(4+√10) exact; smaller instances; any explicit protocol on K_{2,m}, m ≥ 4,
   above routing. Above 3/√10, a protocol over a field of characteristic 0 would imply Contracting there (§5).
2. **Solved: an analytic proof of (I) and of (CL*).** Theorem D (§3.3), by hand and in Lean, with the sharp
   constants: 8 in place of 9 in (I), attained at (π/2, π/2, −π/2); inner constant 9 in place of 10 in (3.5).
3. **Attainment in 𝒳.** W5(ℓ,ℓ/3) is the unique five-point CAT(0) minimiser (§3.4; not refereed), and the minimum
   over AN prices is attained (§1.2), so f*(k) = 3/√10 ⇔ W5 is an AN price over k (⇔ tripod × ℝ is a price space,
   by the unrefereed direction of §2.3). Whether some point of 𝒳 has R = 3/√10 is not known.
4. **K_{2,m} beyond the proved range.** For m = 3 the arc 1 < w < 5/4: the lower bound κ(w) is not proved (Theorem D
   fails there, §3.3 remark 3); only the chord bounds of §4.4 hold. The statement (CL\*\*) of `k2m/notes.md` §5.4
   (Br′ ≥ 0 on 𝓕′ for 12/13 ≤ λ ≤ 3/√10, η = 3τ; seven variables) would settle it (review-thmE item 6). For m = 4 the gap is 2 < w < 5/2; for m ≥ 5
   the cut regime needs an m-page version of Theorem E. Which other networks and demands are pinned by five-point CAT(0)
   inequalities is open (§4.5); where six or more points interact, box inequalities do not suffice (§3.6), and one needs
   the full cone of quadratic CAT(0) inequalities (Andoni–Naor–Neiman 2018, Thm 1.1, as quoted in [Toy24]; [Toy24b]).
5. **Lean formalisation.** The book reduction and the calibration (elementary real analysis) would complete item 1
   in Lean from C.3, C.4(a) and Strassen's theorem. The same holds for Prop. C′, the one-vertex lemmas (V1), (V2),
   (X1), (X2) and the cubic of Theorem E. Lemma H_m needs a CAT(0) library (or C.4 as axioms).
   Connecting to [AN]'s `prop_space` and `thm_alt_rank_price` requires building their development.
6. **Whether contracting decides the rate.** If contracting holds over k, is f*(k) > 3/√10? By uniqueness this
   means that W5 is not an AN price over k (by §2.3, unrefereed: that N5 is not one). Contracting alone does not
   obviously decide it.
7. **Conjectures W, P and f_CAT(0)(K_{3,3}) = 1** (§4.5); for K_{3,3}, f* ≥ 51/52 is proved at level (c).

---

## References

- [AN] Anthropic, "VP ≠ VNP over every field", November 2026, with Lean development (`vp-vnp`). Machine-generated;
  not refereed by people.
- [CE] "The contracting case of the tensor-price dichotomy contradicts the weak exponential-time hypothesis",
  companion note, `research/ports/note-contracting-eth.md`, draft of 26 November 2026. Contains Theorems A, B, R
  and their status table (§7 there).
- [EG] OpenAI, "Euclidean geometry in the asymptotic spectrum of tensors", 24 November 2026 (Thm 4.3, Cor. 3.4).
  Machine-generated; not refereed by people.
- [MM] OpenAI, "The matrix multiplication exponent is nine fourths", 24 November 2026 (§§1, 8). Machine-generated;
  not refereed by people.
- [AHJKL06] Adler, Harvey, Jain, Kleinberg, Lehman, SODA 2006 (cited alongside [HKL06] for the same result).
- [AKP] Alexander, Kapovitch, Petrunin, "Alexandrov meets Kirszbraun", Gökova 2010; updated version
  arXiv:1012.5636v2 (2017), §7.2.
- [ALP26] Alman, Li, Pratt, "The edge of the asymptotic spectrum of tensors", arXiv:2604.01386 (seen in a search
  excerpt only).
- [BCFLN26] Botero, Christandl, Fraser, Leigh, Nieuwboer, "On quantum functionals for higher-order tensors",
  arXiv:2604.18283 (April 2026).
- [BH99] M. Bridson, A. Haefliger, *Metric spaces of non-positive curvature*, Springer 1999.
- [CLSWW24] Christandl, Lysikov, Steffan, Werner, Witteveen, "The resource theory of tensor
  networks", Quantum 8, 1560 (2024), doi:10.22331/q-2024-12-11-1560. The restriction framework of f*; no K_{2,3}
  instance.
- [HKL06] N. J. A. Harvey, R. Kleinberg, A. R. Lehman, "On the capacity of information networks", IEEE Trans. Inf.
  Theory 52(6) (2006), §X.B, Thm 27 ("The network coding rate of the Okamura–Seymour example is 3/4"); Thm 28 extends
  it to "special bipartite" instances.
- [JV20] Jensen, Vrana, "The asymptotic spectrum of LOCC transformations", IEEE Trans. Inf. Theory (2020),
  arXiv:1807.05130.
- [Lan06] J. M. Landsberg, "The border rank of the multiplication of 2×2 matrices is seven", J. Amer. Math. Soc. 19
  (2006).
- [LOW10] Leung, Oppenheim, Winter, "Quantum network communication — the butterfly and beyond", IEEE Trans.
  Inf. Theory 56 (2010) 3478, arXiv:quant-ph/0608223.
- [LP22] Lebedeva, Petrunin, "Trees meet octahedron comparison", arXiv:2212.06445.
- [OS81] Okamura, Seymour, J. Combin. Theory Ser. B 31 (1981) 75–81.
- [SDW26] Sakabe, Doğan, Walter, arXiv:2601.21553 (support functionals equal quantum functionals; seen in a search
  excerpt only).
- [Str88] V. Strassen, "The asymptotic spectrum of tensors", J. reine angew. Math. 384 (1988).
- [Toy] T. Toyoda, "An intrinsic characterization of five points in a CAT(0) space", Anal. Geom. Metr. Spaces 8
  (2020) 114–165; arXiv:1907.09074, Thm 1.3.
- [Toy24] T. Toyoda, arXiv:2404.13871 (J. Topol. Anal., 2026), Thm 3.1 (Lebedeva's six-point space).
- [Toy24b] T. Toyoda, "Inequalities on six points in a CAT(0) space", arXiv:2411.13877, Thm 2.4.
- [VC17] Vrana, Christandl, "Entanglement distillation from GHZ shares", Comm. Math. Phys. (2017),
  arXiv:1603.03964. Tensors reach the cut bound for GHZ/broadcast-type demands; not multiple-unicast.
- [VZ26] Vrana, Zuiddam, "The asymptotic spectrum of tensors is connected", arXiv:2611.34664 (dated 2 November
  2026, listed 25 November 2026), Thms 1.9, 4.12.
- [WZ26] Wigderson, Zuiddam, "Asymptotic spectra: theory, applications and extensions", Bull. Amer. Math. Soc.
  (2026), doi:10.1090/bull/1880, Thm 12.23.
- Network coding preprints cited as context in §0.1: Z. Li, B. Li, "Network coding can beat routing in undirected
  multiple-unicast networks", arXiv:2610.09367; Zhongtian He, "The multiple unicast conjecture is false",
  arXiv:2610.10108; Liu, Que, Li, Li, "On the multiple-unicast conjecture: beyond cut metrics", arXiv:2608.06070.
- Working files (under `research/ports/`): `hull/notes.md`; `k2m/notes.md` (§§0–6); `protocol/notes.md`,
  `protocol/certificates/README.md`; `e3/notebook.md`; `ivcert-notes.md` (§5: certificates of §4.4); reviews
  `review-hull.md`, `review-fivepoint.md`, `review-k2m.md`, `review-protocol.md`, `review-thmE.md`; `lean/` (`W5.lean`, `Hull.lean`, `CLStar.lean`, `ProtocolCert.lean`,
  `NOTES.md`). Interval tools: `tools/ivcert/` (`certs/`, `run_k2.sh`), `tools/ivcheck2/` (`run_k2.sh`).

---

## Changes in this version

**This revision.** (1) Theorem E and Corollary E (§4.4; item K_m.5): unconditional exact rates 3/(2+w) on K_{2,3}(w)
and 4/(4+w) on K_{2,4}(w) in the cut regime, at three levels of support (hand proof, refereed, w ≥ 1.9134; with the
certificate S(9/10), w ≥ 4/3; with (CL\*\*₀), w ≥ 5/4), with the refined calibration, the sign cases, the one-vertex
lemmas, Lemma R, the certificates and the chord bounds for 1 < w < 5/4. The remarks of review-thmE.md are applied:
equality on the whole family of line metrics; "infimum" in Prop. B; no non-regular version of Prop. T; margin
+0.0158 at λ = 0.92. (2) §4.5: Props. B and T, three-value instances, the K_{3,3} lower bounds 0.975 and 51/52, and
Conjectures W, P and f_CAT(0)(K_{3,3}) = 1. (3) §3.5 compressed (now a third confirmation of (CL\*)). §§0.1–0.3, the
status table, trust base and open problems are updated; the title is extended.

**Previous revision.** (CL*) proved analytically (Theorem D, Lean), so item 1 stopped being computer-assisted;
Theorem K_m for K_{2,m}(w) (weighted calibration, averaging, Lemmas P and H_m, weighted duality); the explicit
protocols in §7 with exact certificates to B = 32; zeros of Φ₁ and uniqueness of W5 (§3.4, not refereed).
