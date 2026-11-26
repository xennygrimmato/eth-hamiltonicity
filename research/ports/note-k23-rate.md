# Tensor rates of the networks K_{2,m}: 3/√10 ≤ f* for the Okamura–Seymour network K_{2,3}, and 2m/√(m²(m−1)²+4w²) ≤ f* in general, with equality unless the contracting hypothesis holds

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
>    - Every ℓ₁-embeddable pseudometric d has R(d) ≥ 1 (R as in §1.2). So none of the spectral points whose wire
>      metrics are explicitly known certifies any upper bound below 1.

Item 1 is no longer computer-assisted: its last step, the six-variable inequality (CL*), now has a six-line
analytic proof (Theorem D, §3.3), which is checked in Lean. The interval certificates of the first version remain as
an independent confirmation (§3.5).

**The general statement.** For m ≥ 3 and w > 0 let K_{2,m}(w) be the network with parties u₁, u₂, v₁, …, v_m,
supply the 2m binary wires u_kv_i, and demand all C(m,2) wires v_iv_j at rate f together with the wire u₁u₂ at rate
w·f (precise definition in §1.1). Theorem K is the case m = 3, w = 1. Put

    R_m(w) = 2m/√(m²(m−1)² + 4w²),       κ(w) := R_3(w) = 3/√(9+w²),       R_3(1) = κ.

> **Theorem K_m.** Let m ≥ 3 and let k be any field.
> 1. *(Unconditional.)* f*(K_{2,m}(w); k) ≥ R_m(w) for 0 < w ≤ m(m−1)/6. The range contains w = 1 for every m.
> 2. *(Conditional upper bound.)* If contracting fails over k, then f*(K_{2,m}(w); k) ≤ R_m(w) for every w > 0
>    (also for border protocols as in item K.2). So f* = R_m(w) in the range of item 1.
> 3. *(Comparison.)* Routing achieves exactly 2m/(m(m−1)+2w). The cut bound is min(2/(m−1), m/(⌊m²/4⌋+w)). In
>    the range of item 1, routing < R_m(w) < cut bound.
> 4. *(Consequence.)* A protocol over k of rate above R_m(w) implies that contracting holds over k, with the
>    consequences of §5.

The ingredients are: a weighted five-point theorem (§3, Theorem 5_w); an averaging over triples of pages (§4.1);
explicit rank-one idempotents in Mat₂(F_q) (Lemma P, §2.1); and the m-pod version of the hull lemma (Lemma H_m,
§2.2).

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

- **Scope of the theorems.** f* is the rate of exact asymptotic restriction. Items K.1 and K_m.1 are
  non-constructive.
- **Not LOCC, not a coding improvement.** f* is exact asymptotic restriction (SLOCC-type), a different resource
  model from classical network coding [HKL06] and from LOCC or fidelity-based quantum network models (Jensen–Vrana
  [JV20]: LOCC with success probability 2^{−rn}; that the restriction rate is the r → ∞ end is the literature check's
  inference, not checked against the paper; Leung–Oppenheim–Winter
  [LOW10]: k-pair quantum communication with or without free classical communication). Theorem K says nothing about
  LOCC rates on K_{2,3}; we found no LOCC result for this instance, and for LOCC we know no upper bound better than the
  cut bound 1. The comparison with network coding in §0.1 is between rates in different models on the same graph.
- **No explicit protocol near 3/√10.** Item 1 comes from Strassen's duality theorem, which proves that protocols
  exist and does not construct them. An explicit asymptotic family above routing is described in §7: rate ≥ 0.83671
  with exact certificates, and 6/(4+√10) ≈ 0.83772 in the limit under one numerical claim. It is not part of the
  theorems, and its smallest instances are far beyond direct computation. Nothing explicit is known for K_{2,m},
  m ≥ 4.
- **No unconditional value.** If contracting holds over k, we know only f*(k) ∈ [3/√10, 1], and for K_{2,m}(w)
  only f* ∈ [R_m(w), cut bound].
- **No claim that contracting holds or fails** over any field.
- **Border protocols.** Nothing is claimed for border protocols over finite fields, or over infinite fields
  when the approximation degree grows exponentially in n.
- **Non-uniform demands.** Only the demand vectors of K_{2,m}(w) are treated: one weight on u₁u₂, the same rate on
  all v_iv_j. For m = 3 the lower bound covers w ≤ 1 only; for w > 1 the method fails (§3.3, remark 3). Other demand
  vectors are different linear tests (§1.2) and are not treated.
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
- **Items K.1, K_m.1** use only Strassen 1988 [Str88] and the CAT(0) property of prices. In [AN] that property is
  Theorem C.1 (`thm_cn`), packaged as Prop. C.3 (`prop_space`). We use it through Lemma C.4(a).
- **Items K.2, K_m.2** additionally use `thm_alt_rank_price` (from the proof of Theorem D.2), Prop. C.3 and Lemma
  C.4(f).
- **Items 1–2 use nothing from OpenAI's November 2026 papers.** OpenAI's [EG] Thm 4.3 is an alternative,
  independent source for the CAT(0) input of item 1 (§1.3).
- **Item 3** uses the companion note [CE] (`note-contracting-eth.md`). One of its two routes uses OpenAI results;
  see §5.

Tags:
- **[P]**: proved here by hand, completely.
- **[P-ref]**: [P], and also checked by an internal referee (a named report).
- **[L]**: machine-checked in Lean in `research/ports/lean/` (Lean v4.36.0 with Mathlib). The project was rebuilt
  for this version: it compiles with no `sorry`, and `#print axioms` shows only `propext`, `Classical.choice` and
  `Quot.sound`. The Lean statement is named each time.
- **[IV]**: verified by the interval certifiers of §3.5.
- **[N]**: numerical evidence only.
- **[AN]**: quoted from [AN].
- **[cl]**: classical.
- **[C]**: conjecture.

---

## 1. Setup

### 1.1 Strassen duality for this instance [cl]

The tensors on the m+2 parties over k, with direct sum, tensor product and restriction, form a preordered
semiring that satisfies Strassen's conditions. Let 𝒳 be its asymptotic spectrum: the functions F ≥ 0 on tensors
that are
- monotone under restriction,
- multiplicative under ⊗,
- additive under ⊕,
- normalised by F(⟨r⟩) = r on unit tensors.

Strassen [Str88] proved that a^{⊗n} ≤ b^{⊗(n+o(n))} iff F(a) ≤ F(b) for all F ∈ 𝒳.

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

To get from rational rates to the sup in the definition of f*:
- take rationals p/q ↑ the infimum;
- S^{⊗n} ≥ S^{⊗n′} for n ≥ n′, because S ≠ 0 has the unit tensor 1 as a restriction;
- S ≥ ⟨2⟩ on all parties (via a spanning tree of K_{2,m}), so ≤ S^{⊗(n+o(n))} and ≤ S^{⊗n} ⊗ ⟨2^{o(n)}⟩
  mean the same thing;
- a diagonal choice of sequences then finishes.

Strassen's theorem can be replaced by [AN] Theorem A.6 (`thm_duality`, l. 1164–1167). Under its hypothesis,
C^N is covered by 2^{εN} products of N factors from the A_β. A cover is a restriction of a direct sum, and
⟨2^{εN}⟩ ≤ S^{⊗εN}, so the same lower bound follows.

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

*(a) Every F ∈ 𝒳 is an AN spectral point.* If s = Σ_j s_j with s_j ≤ t_j, then s ≤ ⊕_j s_j. Each party maps its
direct-sum index space onto its original one by adding the blocks. So F(s) ≤ Σ_j F(s_j) ≤ Σ_j F(t_j). Hence each
d_F is an AN price.

*(b) Every AN price bounds every protocol.* Let d be a price with Σ_T d > 0, and suppose T^{⊗m} ≤ S^{⊗n}. For a
spectral point φ, monotonicity, multiplicativity and A.2 give 2^{m Σ_T d_φ} = φ(T^{⊗m}) ≤ φ(S^{⊗n}) =
2^{n Σ_S d_φ}. This inequality is linear in the distances, so it survives positive multiples and pointwise limits:
m Σ_T d ≤ n Σ_S d. Hence f*(k) ≤ R(d). The same argument gives a_nΣ_vv d + b_n D ≤ nΣ_S d for the weighted
demand, so f*(K_{2,m}(w); k) ≤ R_w(d) for every real w > 0.

*(c) Border protocols over infinite k.* Suppose (⊗_p A_p(ε)) S^{⊗n} = ε^e T^{⊗m} + O(ε^{e+1}), with the A_p
polynomial in ε of total degree D_n.
- Lagrange interpolation at D_n + 1 points of k writes T^{⊗m} as a combination of D_n + 1 restrictions of
  S^{⊗n}. The scalars are absorbed into one party's map.
- This is a cover, so 2^{m Σ_T d_φ} ≤ (D_n + 1)·2^{n Σ_S d_φ}.
- If D_n = 2^{o(n)}, the rate bound is unchanged. This holds for powers of a fixed single-shot border protocol,
  where D_n = O(n).

Together, (a) and (b) say: min over AN prices of R ≤ inf over 𝒳 = f* ≤ min over AN prices of R. The minimum over
AN prices is attained, because after normalising Σ_T d = 1 the prices form a compact set (Def. A.4, Tychonoff),
and the AN class is closed under φ ↦ φ^a. So f* = min over AN prices on the parties. Consequently:
- a lower bound f* ≥ r may be proved for all AN prices on the parties;
- an upper bound needs a single AN price.

Item (b) and the border clause are the argument of review-hull §6.

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

Mat_μ(F₂) is the additive group of μ×μ matrices over F₂. For a price on it, D(r)² is the mean of |a, a+W|² over
all a and all W of rank r.

Def. D.1 (`def_cases`; l. 1698–1702): "Contracting hypothesis: There are an integer μ ≥ 2 and a real number s with
1 ≤ s and s² < μ such that D(μ) ≤ s D(1) for all prices on Mat_μ(F₂)." Def. 2.1 states the same with spectral
points in place of prices. The two forms are equivalent, because the inequality is homogeneous and closed under
limits.

**`thm_alt_rank_price`** (`Paper/Alternative.lean`, l. 706–707 of that file; in the paper, Steps 1–7 of the proof
of Thm D.2 and Remark D.3):

    theorem thm_alt_rank_price (hK : ¬ Contracting K) (hμ : 3 ≤ μ) :
        ∃ w : Mt μ → Mt μ → ℝ, IsPrice K w ∧ ∀ a a', w a a' ^ 2 = (a - a').rank

Failure of the hypothesis is the universal statement "for all μ and s, some price violates the bound". So every
μ ≥ 3 is available (l. 1712: "Suppose that the contracting hypothesis fails, and fix μ ≥ 3"). The proof needs
μ ≥ 3 (l. 1760). Write ρ_μ(a,b) = √rk(a−b).

---

## 2. Upper bound: (m-pod) × segment is forced when contracting fails [P-ref]

### 2.1 Lemma P: the matrices

Let q = 2^r and P¹ = P¹(F_q) = {[1:a] : a ∈ F_q} ∪ {∞ = [0:1]} (q+1 points).

*Rank-one idempotents.* t ∈ Mat₂(F_q) has rk t = rk(I−t) = 1 iff t = uxᵀ with xᵀu = 1: if t = uxᵀ then
det(I − t) = 1 − xᵀu, and then t² = t. Such t is determined by its image ⟨u⟩ and kernel x^⊥, two different points of
P¹, and every ordered pair of different points arises exactly once. For two of them,
t − t′ = [u u′]·diag(1,−1)·[x x′]ᵀ, so t − t′ is invertible iff im t ≠ im t′ and ker t ≠ ker t′.

*The family.* Take the fixed-point-free permutation π(0) = ∞, π(∞) = 1, π(1) = 0, π(a) = a+1 for
a ∈ F_q ∖ {0,1}, and let t_p be the idempotent with image p and kernel π(p). Explicitly (rows separated by ";"):

    t_0 = [1 0; 0 0],   t_∞ = [0 0; 1 1],   t_1 = [0 1; 0 1],   t_a = [a+1  1; a²+a  a]   (a ∈ F_q ∖ {0,1}).

> **Lemma P.** In Mat₂(F_q), q = 2^r: rk t_p = rk(I − t_p) = 1 for all p ∈ P¹, rk(t_p − t_{p′}) = 2 for p ≠ p′,
> and rk I = 2.

*Push-forward to F₂.* Let ι: F_q → Mat_r(F₂) be the regular representation for a fixed F₂-basis, applied entrywise:
ι₂: Mat₂(F_q) → Mat_{2r}(F₂). Then ι₂(A) is the matrix of x ↦ Ax on F_q² ≅ F₂^{2r}; its image is an F_q-subspace of
F_q-dimension rk A, so rk_{F₂} ι₂(A) = r·rk_{F_q}(A). Since ι₂ is additive, ρ_{2r}(ι₂A, ι₂B) = √r·√rk_{F_q}(A−B).

> **Corollary P.** For m ≤ 2^r + 1, the m+2 matrices 0, I, ι₂(t_p) (any m points p) carry under ρ_{2r} the metric
> √r·√(graph metric of K_{2,m}), with {0, I} the 2-side: |0 I| = |t_p t_{p′}| = √(2r), |0 t_p| = |I t_p| = √r.
> The same holds in Mat_μ(F₂) for every μ ≥ 2r, since a ↦ diag(a,0) preserves ranks. We use μ = max(2r, 3).

For q = 2 the family is t₁ = e₁₁, t₂ = e₂₁ + e₂₂, t₃ = e₁₂ + e₂₂ of the first version, and the metric is
**N5**, the square root of the graph metric of K_{2,3}. For N5: the rank table is [L] (`Hull.lean`: `ranks_one`,
`ranks_two`, over `ZMod 2`); R(N5) = 6/(4√2) ≈ 1.06; N5 is ℓ₁-embeddable [N] and not Euclidean [P].

Checks: rank tables over F₂ in Mat_{2r}(F₂) by exact integer arithmetic for r ≤ 6 (`k2m/fqpods.py`, m up to 65) and
independently by the referee for r ≤ 5 (review-k2m §1, own field arithmetic). The construction is optimal: in
Mat_μ(F₂) a scaled copy of √(graph metric of K_{2,m}) exists iff m ≤ 2^{⌊μ/2⌋} + 1 (the images of the t_i form a
partial spread; review-k2m §2: correct). This maximality is not used.

### 2.2 Lemma H_m

Let 𝕋_m be the m-pod with hub o and legs of length a/√2. The diamond is
D_m = {(ξ,σ) ∈ 𝕋_m × ℝ : |ξo| + |σ| ≤ a/√2}, with the ℓ₂ product metric.

> **Lemma H_m.** Let Y be CAT(0) in the sense of §1.3, m ≥ 2, and let n, s, t₁, …, t_m ∈ Y satisfy
> |ns| = |t_it_j| = √2·a (i ≠ j) and |nt_i| = |st_i| = a. Then there is an isometric embedding Ψ: D_m → Y with
> Ψ(o, ∓a/√2) = n, s and Ψ(tip_i, 0) = t_i.

*Proof.*

*Step 1 (solid squares).* Let |xy| = |yv| = |vu| = |ux| = a and |xv| = |yu| = √2·a. Let α(s) ∈ [x,u] and
β(s) ∈ [y,v] be the points at fraction s.
- C.4(f) with δ = h = a gives |α(s)β(t)|² = a²(1 + (s−t)²).
- For s ≠ s′, the four points α(s), α(s′), β(s′), β(s) again satisfy the hypotheses of C.4(f), with
  δ′ = a|s−s′| and h′ = a. Their diagonals have squared length a²(1 + (s−s′)²) = δ′² + h′².
- So the point Φ(s,r) at fraction r on [α(s), β(s)] satisfies |Φ(s,r)Φ(s′,r′)|² = a²((s−s′)² + (r−r′)²).

Thus Φ is a times an isometry of [0,1]², with corners x, u, y, v. Geodesics are unique by C.4(a), so the image is
convex, and its diagonals [x,v] and [y,u] meet at the common midpoint. Apply this to (n, t_i, s, t_j) for each of
the C(m,2) pairs; call the square Q_ij.

*Step 2 (one hub).* Every Q_ij contains [n,s]. So c := mid(n,s) = mid(t_i, t_j) for all pairs.

*Step 3 (triangles).* Δ_i := ∪_{p∈[n,s]} [t_i, p] is defined from geodesics alone. In Q_ij it is the t_i-half of
the square, and Q_ij = Δ_i ∪ Δ_j. Two isometric parametrisations of Δ_i, from Q_ij and from Q_ik, agree on the side
[n,s] (same endpoints, unique geodesic), hence on every segment from t_i to a point of that side, hence everywhere.

*Step 4 (gluing).* Put Ψ(ξ,σ) = ψ_i(|ξo|, σ) for ξ on leg i.
- Points on one leg lie in the flat triangle Δ_i.
- Points on legs i ≠ j lie in the flat square Q_ij, at distance √((τ+τ′)² + (σ−σ′)²). This is the
  distance in 𝕋_m × ℝ.

An isometric embedding is a condition on pairs of points, so no statement about three legs is needed. ∎

Only C.4(a),(f) are used. Of [AN] D.2 Step 8 the one-square case is redone here, not cited. For m = 3 this is the
Lemma H of the first version (review-hull §§3–5: correct); the m-pod version is checked in review-k2m §3.

### 2.3 From Lemma H_m to the rate

W_{m+2}(ℓ,h) is the metric with v_j at distance ℓ from the hub on leg j at height 0, and u₁, u₂ at the hub at
heights ∓h:

    |u_k v_j| = √(ℓ² + h²),   |v_i v_j| = 2ℓ,   |u₁u₂| = 2h,   R_w = 2m√(ℓ²+h²)/(m(m−1)ℓ + 2wh).

By Cauchy–Schwarz, m(m−1)ℓ + 2wh ≤ √(m²(m−1)²+4w²)·√(ℓ²+h²), so

    min_{ℓ,h} R_w(W_{m+2}(ℓ,h)) = R_m(w),   attained exactly at h = 2wℓ/(m(m−1)).                    (2.1)

- For m = 3, w = 1 (W5 := W_5): the minimum 3/√10 is attained only at h = ℓ/3, because
  6√(ℓ²+h²)·√10 − 3(6ℓ+2h) ≥ 0 reduces to 4(ℓ−3h)² ≥ 0. This is [L] (`W5.lean`: `ratio_lower`,
  `ratio_at_third`, `ratio_strict`, `w5_ratio`).
- W_{m+2}(ℓ,h) ⊂ D_m whenever max(ℓ,h) ≤ a/√2 (the referee's relaxation of ℓ + h ≤ a/√2 in our first draft).

> **Corollary H_m.** If contracting fails over k, then for every m ≥ 3 and w > 0, W_{m+2}(ℓ, 2wℓ/(m(m−1))) is a price
> over k, and f*(K_{2,m}(w); k) ≤ R_m(w). In particular f*(k) ≤ 3/√10. The bound extends to border protocols as in
> §1.2(c).

*Proof.*
1. Choose r with 2^r + 1 ≥ m and put μ = max(2r, 3). `thm_alt_rank_price` gives the price ρ_μ. Pull back along
   the m+2 matrices of Corollary P and rescale by 1/√r: √(graph metric of K_{2,m}) is a price (N5 for m = 3).
2. By Prop. C.3 these m+2 points sit isometrically in a price space Y.
3. Lemma H_m (a = 1) embeds D_m, so the points of W_{m+2}(ℓ, 2wℓ/(m(m−1))) lie in Y after scaling.
4. The metric of Y is a price, so its pull-back to these points is a price. Rescale.
5. Apply §1.2(b) and (2.1). ∎

A point about Step 4: Prop. C.3 says the metric of the **whole** price space is a price. So points of Y outside
the image of the m+2 points also carry prices, and no separate statement about convex hulls is needed
(review-hull §2). The m = 3 glue is [L] from explicit hypotheses (`Hull.lean`: `w5_price_of_rho_price`, with Lemma
H as the hypothesis `lemmaH`; Mathlib has no CAT(0) theory).

Equivalences:
- [P] N5 is a price over k ⇔ every finite subset of (tripod with infinite legs) × ℝ is a price over k. For ⇒,
  any finite subset fits in a diamond after translation and scaling. The same holds for m-pods; under
  ¬Contracting every finite subset of (finite pod) × ℝ is a price.
- [P, not refereed] Also ⇔ W5(ℓ,ℓ/3) is a price. This direction uses flat-quadrilateral rigidity [BH99, II.2.11],
  which is not in [AN]'s toolkit.

*Related geometry.* OpenAI's [MM] reduces its matrix-multiplication exponent to a tripod with unit arms in a spectral
space ("The critical ratio occurs at three tips of a tripod with unit arms", [MM] §1; see also [MM] §8 and its
"Propagation of equality on a tripod"). This is a close relative of the extremal configuration W5 ⊂ tripod × segment used here; we use
nothing from [MM].

---

## 3. Lower bound: the weighted five-point theorem

> **Theorem 5_w.** Let u₁, u₂, v₁, v₂, v₃ be points of a CAT(0) space (§1.3), and 0 < w ≤ 1. Then
> Σ_S ≥ κ(w)·(Σ_vv + w·D), κ(w) = 3/√(9+w²), with equality for W5(ℓ, wℓ/3). For w = 1 this is
> **Theorem 5**: Σ_S ≥ κ Σ_T.

By §1.2(a) and Prop. C.3, every d_F with F ∈ 𝒳, and every AN price on five parties over any field, is the
restriction of the metric of a CAT(0) space to five points. Theorem 5_w is the combination of three steps:
- §3.1: reduction to books [P-ref];
- §3.2: calibration [P-ref; also checked numerically];
- §3.3: the inequality Φ_w ≥ 0 (Theorem D) [P-ref; L].

The referee's final report on the case w = 1 (review-fivepoint.md) found no gap, fatal or repairable, in the chain
C.3 → C.4(a) → (3.1) → Prop. 3.2 → (CL*) → duality. The weighted chain (3.1) → Prop. C₃ → Theorem D is checked
in review-k2m §4.

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

*Remark (not used).* Let Z, the **book**, be three Euclidean comparison triangles (ū₁, ū₂, v̄_i) glued along the
common side, the spine. Then d^Z_ij is the distance of v̄_i and v̄_j in Z. We use this only as language.

### 3.2 Calibration (complete computation)

*Coordinates.* In page i use (ρ,a): ρ ≥ 0 is the distance from the line of the spine and a is the height along it.
- u₁ = (0,0), u₂ = (0,D), v_i = (ρ_i, a_i).
- The foot a_i may lie outside [0,D].
- Spine points are c(y) = (0,y), y ∈ [0,D].
- Then A_i = |(ρ_i, a_i)|, B_i = |(ρ_i, a_i − D)|, and f_i(y) := |v_i − c(y)| = h_i(y/D).

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

Checks:
- **Referees [P-ref].** review-fivepoint §2 recomputed every line at w = 1; review-k2m §4 recomputed the weighted
  version and the general-m version (Prop. C there) by hand.
- **Numerics [N].** At w = 1: 200 000 random books (referee), including ρ = 0, v_i = u_k and near-W5 books, minimum
  slack +1.5·10⁻⁵, and 2 × 20 000 books by the author. Weighted: 40 000 books for each w ∈ {0.05, 0.2, 0.5, 0.8, 1}
  (review-k2m §4, own hub formula), no violation, and the bracket identity holds to 3·10⁻¹⁴.
- A careless subgradient at a hub on the spine (σ_ij = 0 instead of the choice above) produces apparent
  violations. So the choice in (3.2) is necessary, not cosmetic.

### 3.3 Theorem D: an analytic proof of (CL*) [P-ref; L]

> **Theorem D.** For 0 < w ≤ 1, every K ≥ 9/w² and σ ∈ [−1,1]⁶, the function (3.5) with inner constant K is ≥ 0.
> In particular Φ_w ≥ 0 (K = 1 + 9/w²), and (CL*) holds.

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
`clstar_weighted` (exactly (3.5) with K = 1 + 9/w², 0 < w ≤ 1); `clstar` ((3.5) at w = 1, K = 10, i.e. (CL*));
`clstar_weighted_sharp` (any K ≥ 9/w²); `clstar_K9` (K = 9 at w = 1); `clstar_K_lt9_fails` (at
σ = (1,−1,−1,−1,1,1), Φ = √K − 3 < 0 for K < 9). The referee also compiled the file (review-k2m §4).

Remarks.
1. *Sharp constants.* At w = 1 the inner constant 10 can be lowered to 9, and 9 is optimal
   (`clstar_K_lt9_fails`). In trigonometric form: "1 + 8 sin²δ" instead of "1 + 9 sin²δ".
2. *The three-angle inequality (I).* On the slice ψ_ji = −ψ_ij (all hubs interior), with θ₁ = ψ₁₂, θ₂ = −ψ₁₃,
   θ₃ = ψ₂₃, Φ₁ ≥ 0 becomes
   F_c(θ) = Σ_{i<j} cos((θ_i−θ_j)/2)·√(1 + c·sin²((θ_i+θ_j)/2)) ≥ 3 on [−π/2, π/2]³                    (I)
   with c = 9. Equivalently, three points z_i = (cos θ_i, √(1+c) sin θ_i) satisfy
   |z₁+z₂| + |z₁+z₃| + |z₂+z₃| ≥ 6. By Theorem D, (I) holds for every c ≥ 8, and **8 is sharp**: F_c(π/2, π/2,
   −π/2) = √(1+c). [L]: `three_angle_alg` (algebraic slice, K ≥ 9), `three_angle` (c ≥ 8), `three_angle_I`
   (c = 9), `three_angle_corner`. Near 0, F₉(θ) = 3 + θᵀQθ + O(|θ|⁴) with Q = (3/4)·Id + (5/4)·J, eigenvalues
   3/4, 3/4, 9/2 [P].
3. *Weights above 1.* At the six corners of §3.4, Φ_w = 3/w − 3 < 0 for w > 1, so neither the statement nor the
   method extends beyond w = 1.
4. *Another direction in step 3.* The source notes (k2m/notes.md §3.3) take sin χ = 3m/√(9+w²) instead; this
   is also correct and is used for the equality analysis in §3.4. The Lean proof uses (√(1−m²), m), which needs only
   K ≥ 9/w².
5. *Why it was missed.* The earlier attempts (hull notes §3.5) bounded one pair term at a time or decoupled the
   angles. The proof uses one linearisation for all terms, tuned to the largest |σ|, and the cyclic telescoping.

*Proof of Theorem 5_w.* If D = 0 see §3.1. If D > 0: by (3.1), Prop. C₃ and Theorem D,
Σ_S − κ(w)(Σ_vv + wD) ≥ (κ(w)w/3)·D·Φ_w ≥ 0. Equality at W5(ℓ, wℓ/3) is (2.1) with m = 3. ∎

### 3.4 Equality cases and uniqueness

- At W5(ℓ,ℓ/3), in book coordinates D = 2ℓ/3, ρ_i = 3D/2 and a_i = D/2:
  - all hubs are at D/2 and all ψ = 0;
  - the calibrating vectors (cos α_i, sin α_i) = (3,1)/√10 and (cos β_i, −sin β_i) = (3,−1)/√10 are the true
    directions u₁→v_i and u₂→v_i;
  - every inequality in §3.1–3.2 is an equality;
  - Σ_S = 3√10·D and Σ_T = 10·D.
- *Zeros of Φ₁ [P].* With sin χ = 3m/√10 in step 3 of Theorem D, the chain ends with
  3√(1 − 9m²/10)·√(1−m²) + 3m² ≥ 3, which is strict for 0 < m < 1. At m = 1 the first term forces all c_ij = 0, so
  σ ∈ {±1}⁶, and the 64 sign vectors contain exactly six zeros: for one vertex i and one sign s, ψ_ij = ψ_ik = −sπ/2
  and the other four angles equal +sπ/2. So the zeros of Φ₁ are 0 and these six corners. This replaces the numerical
  statement of the first version (2·10⁷ random points, about 10⁴ local searches, no other zeros). For w < 1 the last
  step is strict for every m > 0, and 0 is the only zero of Φ_w.
- *Uniqueness [P; new in this version, not refereed].* Let five points of a CAT(0) space satisfy
  Σ_S = κ(w)(Σ_vv + wD) with Σ_vv + wD > 0 and 0 < w ≤ 1. Then D > 0 (§3.1), and equality holds in (3.1), in every
  (3.4), and Φ_w(σ) = 0.
  - At a corner all c_ij = 0, so all ρ_i = 0 and the book is a metric tree; tree metrics are ℓ₁, so
    Σ_S ≥ Σ_vv(Z) + D (§6(c)) and Σ_S − κ(w)(Σ_vv(Z) + wD) ≥ (1 − κ(w))D > 0. So corners give no equality.
  - Hence σ = 0: every exit vector is horizontal, μ_i = δ_i = 0, and all y_ij = a_i, so all a_i are equal. Equality
    in (3.4) with α_i = β_i = arccos κ(w) gives (ρ_i, a_i) ∥ (3, w) and (ρ_i, D − a_i) ∥ (3, w), so a_i = D/2 and
    ρ_i = 3D/(2w). Equality in (3.1) gives |v_iv_j| = 2ρ_i.

  So the configuration is W5(ℓ, wℓ/3) with ℓ = 3D/(2w): **W5(ℓ,ℓ/3) is, up to scale, the only five-point CAT(0)
  configuration with R = 3/√10.** By the averaging of §4.1, the same follows for W_{m+2} in the range of
  Theorem K_m (each five-point subset is then extremal); we have not written this out.
- Searches over books found the minimum only at W5 [N].

### 3.5 Independent confirmation by interval arithmetic [IV]

Before Theorem D, (CL*) and (I) were proved by interval arithmetic (`tools/ivcert/`). These certificates are now an
independent confirmation of the case w = 1.

- *Certificates.* The main certificate `clstar:rho=0.5` is a bisection tree on [−1,1]⁶ in the coordinates (3.5).
  Its leaves are closed by natural interval extension, a mean-value form, a second-order Taylor form or certified
  convexity, or are **excluded**. It exists with symmetry pruning (S₃ × {±1}; 92 195 leaves) and without (528 970
  leaves); the version without pruning suffices. Excluded leaves lie in the central cube [−½, ½]⁶, covered by eight
  orthant certificates `clnear:rho=0.5:s=±±±` (8 608 to 11 685 leaves each), which close the equality point 0 by a
  gain test, or in one of six corner regions {sσ_jk ≥ 15/16, sσ_kj ≥ 15/16}. (I) has its own certificate `hull3`
  (401 leaves; 1 014 without symmetry).
- *Corner lemma [P].* On a corner region put d₁ = 1 − sσ_jk, d₂ = 1 − sσ_kj ∈ [0, 1/16]. The vertex terms at j and k
  are ≥ √d₁/2 and ≥ √d₂/2, and |σ_jk + σ_kj| = 2 − d₁ − d₂, so Φ ≥ (√d₁ + √d₂)/2 − (3/2)(d₁ + d₂) ≥ 0, because
  3d ≤ √d for d ≤ 1/9.
- *Covering [P-ref].* The checker rebuilds every leaf from the tree, so the leaves cover the domain structurally;
  the region tests are exact in binary64, since ½ and 15/16 are dyadic (review-fivepoint §6).
- *Two checkers.* `ivcheck` performs no search but shares the Rust implementation (interval arithmetic, forward
  automatic differentiation, positive-definiteness certification, leaf and gain tests, certificate parsing) with the
  prover; the referee checked the encoding of Φ by hand and spot-checked rounding and the gain test. `ivcheck2`
  (`tools/ivcheck2`) is a separate implementation in Python with Arb ball arithmetic (python-flint 0.9.0, FLINT
  3.6.0): it takes only the box lists, checks that they partition the domain and that the 94 excluded boxes lie in
  the central cube (64) or a corner region (30), re-proves Φ ≥ 0 on every other box, and uses its own argument at
  the origin. It verifies the no-symmetry `clstar` certificate, all eight `clnear` certificates and `hull3`, and
  rejects a mutation (Φ − 0.001). It has not been refereed. All twelve certificate files in `tools/ivcert/certs/`
  report VERIFIED under `ivcheck`.
- *Trust base of this route.* IEEE-754 binary64 round-to-nearest with a correctly rounded fma on the machine used;
  the Rust source of `ivcert` and its compiler, or alternatively the `ivcheck2` stack; and the hand steps (sine
  substitution, orthant cover, corner lemma, gain-test bound in the header of `lb_gain_h`, `src/bnb.rs`).
- *Consistency with Theorem D.* With constant 8 in (I) the interval certificate does not close at (π/2, π/2,
  −π/2); by §3.3, remark 2, F₈ = 3 exactly there, so this is an equality point and not a counterexample.

### 3.6 Remarks and numerical cross-checks

- **What kind of inequality this is.** The quadrilateral (Reshetnyak) inequalities of C.4(b), together with the
  triangle inequalities, give only min R = 0.944606… [N], a root of 58x³ − 14x² − 29x − 9 (PSLQ at 60 digits). So
  Theorem 5 genuinely uses C.4(a) at t ≠ ½, in the book reduction.
- **Toyoda's five-point criterion [N].** Toyoda [Toy, Thm 1.3]: a metric space with at most five points embeds
  isometrically in a CAT(0) space iff it satisfies the Gromov–Sturm box inequalities. Minimising R under these as a
  semi-infinite program gave 0.948683298050505 at W5 in 1000 of 1000 multistarts (e3 notebook). The criterion is
  special to at most five points: Lebedeva's six-point spaces satisfy all box inequalities without embedding in any
  CAT(0) space ([AKP, arXiv:1012.5636v2, §7.2]; Thm 3.1 in [Toy24], Thm 2.4 in [Toy24b]; see also [LP22]). Theorem
  K_m avoids this, because it uses only five-point subsets.
- **Model spaces [N].** Minimising R over products of two or three trees, and over the Euclidean cone over the
  Heawood graph, gave 3/√10 at W5. Single trees and Euclidean spaces give 1.
- **m-page books [N].** The minimum of R_w over m-page books equals R_m(w) to about 10⁻¹⁶ for m = 3, …, 6 and several
  w in the range (review-k2m §5).

---

## 4. K_{2,m}, and the proofs of Theorems K and K_m

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
weight w is exactly as hard as K_{2,3} at weight 6w/(m(m−1)). The uniform instance w = 1 is covered for all m ≥ 3
(for m ≥ 4 with w′ ≤ ½).

*Lean.* `PortsLean/CLStar.lean`: `k2m_average` (if κ(T_ij + T_jk + T_ik + w′D) ≤ S_i + S_j + S_k for all distinct
i, j, k, with T symmetric, then (2κ/(m−1))(Σ_{i<j}T_ij + w′·m(m−1)/6·D) ≤ Σ_iS_i; no sign hypotheses), `R_eq`
(2m/√(m²(m−1)²+4w²) = (2/(m−1))·3/√(9+w′²) for w = w′m(m−1)/6) and `k2m_rate` (the combination, with
κ = 3/√(9+w′²)). These formalise the counting and the constant. The five-point inequality enters as a hypothesis;
Lean does not connect it to CAT(0) spaces or to Theorem D.

### 4.2 Proofs

**Theorem K.1 and K_m.1.** Let d be an AN price on the m+2 parties with Σ_vv d + wD > 0. By Prop. C.3 it is the
restriction of the metric of a CAT(0) space to m+2 points. By Theorem B (Theorem 5 for m = 3, w = 1),
R_w(d) ≥ R_m(w). By §1.2(d), f*(K_{2,m}(w); k) ≥ R_m(w). This holds over every field: [AN] l. 564–567 says that "the
field only supplies the scalars", and Strassen's theorem holds over every field.

**Theorem K.2 and K_m.2.** Corollary H_m, with border protocols as in §1.2(c); item 1 gives equality in its range.

**Theorem K_m.3 [P-ref: review-k2m §7].**
- *Routing.* Send each v_iv_j half through u₁ and half through u₂, and u₁u₂ in equal parts through the m vertices
  v_j. Each edge carries f((m−1)/2 + w/m), so f = 2m/(m(m−1)+2w). The path metric of K_{2,m} has R_w equal to the
  same number, so no routing does better. For m = 3, w = 1: 3/4, and the dual inequality 3Σ_T d ≤ 4Σ_S d for every
  pseudometric is [L] (`W5.lean`: `flow_bound`).
- *Cuts.* For X with a = |X ∩ {u₁,u₂}| and b = |X ∩ {v_i}|, the cut separates a(m−b) + (2−a)b supply pairs and
  b(m−b) + w·[a = 1] demand weight. For a ∈ {0, 2} the least ratio is 2/(m−1), at b = 1; for a = 1 it is
  m/(⌊m²/4⌋+w), at b = ⌊m/2⌋. (Brute force over all subsets agrees for m ≤ 6.)
- *Strictness.* R_m(w) < 2/(m−1) for w > 0, and R_m(w) > routing because (m(m−1)+2w)² > m²(m−1)² + 4w². With
  β = ⌊m²/4⌋, R_m(w) < m/(β+w) iff w < w_c(m) := (m²(m−1)² − 4β²)/(8β), and m(m−1)/6 < w_c(m): w_c(3) = 5/4; for
  m ≥ 4, w_c(m) ≥ (3m−2)(m−2)/8 > m(m−1)/6, since 5m² − 20m + 12 > 0.

**Theorem K_m.4.** Item 2 and §5. ∎

Numbers for w = 1:

| m | routing 2m/(m(m−1)+2) | R_m(1) | cut 2/(m−1) | R_m(1)/routing |
|---|---|---|---|---|
| 3 | 0.7500 | 0.948683 = 3/√10 | 1 | 1.2649 |
| 4 | 0.5714 | 0.657596 = 8/√148 | 0.6667 | 1.1508 |
| 5 | 0.4545 | 0.497519 = 10/√404 | 0.5 | 1.0945 |
| 6 | 0.3750 | 0.399114 = 12/√904 | 0.4 | 1.0643 |

The gain over routing is (m(m−1)+2w)/√(m²(m−1)²+4w²). It increases in w on the proved range and is largest at the top,
w = m(m−1)/6, where it equals 4/√10 for every m. At w = 1 it tends to 1 like 1 + 2/(m(m−1)), and the ratio of the cut
bound to R_m(1) is √(1 + 4/(m²(m−1)²)). So among the uniform instances K_{2,m}(1), K_{2,3} has the largest proved
gain over routing and, if contracting fails, the largest gap to the cut bound.

### 4.3 Remark: the direct m-page calibration fails

The calibration of §3.2 works for m pages with any constant λ < 2/(m−1): with V_i = Σ_{j≠i} e_ij = |V_i|(cos μ_i,
sin μ_i) and M_i = cos μ_i √(1 − λ²|V_i|²/4), one gets Σ_S − λ(Σ_vv(Z) + wD) ≥ D·Br with
Br = Σ_iM_i − λw + (λ/2)Σ_{i<j}|ε_ij|, and all lengths cancel (review-k2m §4). At λ = R_m(w) this is tight at
W_{m+2}. But the scalar inequality Br ≥ 0 is **false** [P-ref], for every even m ≥ 4 and every w > 0, and for odd
m ≥ 5 when w > m(m−1)/(2√(m²−1)) (for m = 5: w > 2.04, inside the range w ≤ 10/3).
- Take the collinear book with all ρ_i = 0 and v₁, …, v_m pairwise different interior points of the spine, numbered
  upwards. The hubs can be taken interior (ε_ij = 0), and the exit vectors can be taken vertical: v_i exits upwards
  towards the i−1 points below it and downwards towards the m−i points above it. So V_i = (0, 2i − m − 1).
- m even: no V_i vanishes, all cos μ_i = 0, and Br = −λw < 0. m odd: only the middle point has V_i = 0, and
  Br = 1 − λw.
- For nearby books with small ρ_i > 0 the hubs are unique and Br stays negative (m = 4, w = 1: Br = −0.650 while the
  true left side is +2.03; review-k2m §7).

The reason is parity: an odd number m−1 of exit vectors at a vertex cannot cancel. For m = 3 two opposite exits
cancel, and Theorem D shows that this suffices. Theorem B avoids the issue.

---

## 5. Consequences and the falsifiable prediction

**(i)** By Corollary H_m, a protocol over k of rate > 3/√10 shows that W5, and hence N5, ρ₂ and ρ₃, are not prices
over k. So Contracting(k) holds [P-ref]. A protocol over ℚ also counts over ℝ, ℂ and ℚ̄. The same holds for a
protocol on K_{2,m}(w) of rate > R_m(w), for any w > 0.

**(ii)** If char k = 0, Contracting(k) implies 3-SAT in 2^{O(n^{1−δ})}·poly, by [CE]. Two routes:
- **Theorem R** uses [AN] only. In the non-uniform form (advice of size poly(n)) it is refereed
  (review-theoremR.md). The uniform form rests on a one-reader audit of [AN]'s Lean proof terms
  (review-uniformity.md), not on a Lean theorem.
- **Theorem A** (contracting ⇒ ports; refereed, review-theoremAB.md) uses [AN] F.6 and OpenAI's HC Thm 4.2. The
  step from ports to 3-SAT then uses OpenAI's IM Thm 7.1, which we have not reviewed.

**(iii) Prediction.** Under the non-uniform weak exponential-time hypothesis, the following holds via Theorem R in
its refereed form. Under the uniform Weak ETH it holds via the audit or via Theorem A + IM 7.1.

> For every field k of characteristic 0, no asymptotic restriction protocol from the six binary wires of K_{2,3}
> to the four demand wires has rate above 3/√10 = 0.948683…. The same holds for border protocols of
> approximation degree 2^{o(n)}. Rates arbitrarily close to 3/√10 are attained (unconditionally, by item 1).
> More generally, no protocol on K_{2,m}(w) has rate above R_m(w).

The prediction can be refuted by an explicit object. For example, a single restriction over ℚ from wires of
dimension 10 on the six edges to wires of dimension 9 on the four demand pairs (rate ≈ 0.954) would refute it. So
would any power or tensor combination with rate > 3/√10. Such a restriction would imply Contracting(ℚ), and with
[CE] a 2^{O(n^{1−δ})} algorithm for 3-SAT.

**(iv) Product closure.** If f*(k) > 3/√10, then tripod × segment is not a price space over k, although tripod and
segment are. So ℓ₂ products of spectral spaces are then not always spectral [P].

---

## 6. Small exact facts (Theorem K.4)

**(a) Rate 1 single-shot is impossible [P] (from the e3 notebook, re-derived here).** Suppose
(⊗_p A_p) S_D = T_D, where every supply and demand wire has dimension D ≥ 2, over any field.
1. Each cut {v_i} has flattening rank D² on both sides, so each A_{v_i} is invertible.
2. Then (A_{u₁} ⊗ A_{u₂}) S_D = (⊗_i A_{v_i}⁻¹) T_D. The left side is M₁ ⊗ M₂, where M_k is A_{u_k} applied to the
   three wires at u_k.
3. For M₁ ⊗ M₂ (with M₂ ≠ 0), the flattening rank across {u₁} equals rk_{u₁}(M₁). The rank across {u₁,u₂} equals
   rk_{u₁}(M₁)·rk_{u₂}(M₂) ≥ rk_{u₁}(M₁).
4. Invertible maps at the v's preserve both ranks. For T_D they are D and 1.

So D ≤ 1, a contradiction. The same argument excludes every instance in which the v-cuts are tight and the
u₁u₂ wire has dimension ≥ 2.

**(b) Bond dimension 2, border, over ℂ [P].** Suppose S₂ degenerates to a tensor with v₁v₂ = v₂v₃ = v₁v₃ = 2 (any
dimension on u₁u₂).
1. Compose with the functional e₁* at u₁ and at u₂. The target becomes the 2×2 matrix multiplication tensor
   ⟨2,2,2⟩ on v₁, v₂, v₃.
2. The source becomes (⊗A_v(ε))(X(ε) ⊗ Y(ε)), with X, Y ∈ (ℂ²)^{⊗3}. Its border rank is ≤ 2·2 = 4.
3. The set of tensors of border rank ≤ 4 is closed, but the border rank of ⟨2,2,2⟩ is 7 [Lan06].

**(c) ℓ₁ metrics [P; L].** For a cut metric δ_X, let a = |X ∩ {u₁,u₂}| and b = |X ∩ {v₁,v₂,v₃}|. The cut crosses
a(3−b) + (2−a)b supply pairs and [a = 1] + b(3−b) demand pairs.
- a = 0: 2b supply against b(3−b) demand.
- a = 1: 3 supply against 1 + b(3−b) ≤ 3 demand.
- a = 2: by complementation, as for a = 0.

So each cut has Σ_S ≥ Σ_T, and so does every nonnegative combination. Hence R ≥ 1 on the cut cone. This is [L]
(`W5.lean`: `cut_ineq`, all 32 cuts; `w5_not_cut_combination`). The cut {v₁} attains 1 (`cut_v1`), and so
f* ≤ 1, since a flattening rank is a spectral point.

Which explicit spectral points have ℓ₁ wire metrics [K] (`ideas-ports.md` §4.1):
- flattening ranks give cut pseudometrics;
- Strassen's support functionals (every field) give star metrics d(x,y) = θ_x + θ_y = Σ_z θ_z δ_{{z}}(x,y);
- the quantum functionals of Christandl–Vrana–Zuiddam (over ℂ) give star metrics;
- the laminar (non-crossing) upper quantum functionals, which are spectral points on complex tensors [BCFLN26,
  arXiv:2604.18283; VZ26, arXiv:2611.34664, Thm 1.9], and the upper support functionals [SDW26, arXiv:2601.21553;
  ALP26, arXiv:2604.01386; both known to us only from search-engine excerpts]. On graph tensors each of these gives a
  wire metric Σ_b θ_b·δ_b, a nonnegative combination of cut metrics. This is by the literature check's own
  computation, not refereed, and is not stated in those papers.

For context on the structure of the spectrum on graph tensors: the asymptotic spectrum of graph tensors is
log-star-convex [WZ26, Thm 12.23], and Vrana–Zuiddam reprove this over every field: log Δ is star-convex about every
point of the convex hull of the singleton flattening-rank vectors [VZ26, Thm 4.12].

Each of these wire metrics is ℓ₁-embeddable, and ℓ₁-embeddability survives the operations that preserve prices
(pull-backs, non-negative multiples, pointwise limits). So neither these points nor any price obtained from one of
them by those operations certifies an upper bound below 1. (Products of spectral points are in general not spectral
points, and a sum of cut metrics need not be a price: the path metric of the 4-cycle is a sum of two cuts and violates
the CN inequality.)

**(d) Routing [P; L].** See §4.2: routing achieves exactly 3/4 (`flow_bound`); the path metric of K_{2,3} has
R = 6/8.

---

## 7. An explicit family above routing

Theorem K.1 is non-constructive. An explicit asymptotic family with rate above 3/4 comes from the crossing identity
of [AN] (`protocol/notes.md`; refereed once, `review-protocol.md`: no fatal gap). It is not part of Theorem K.

*Construction.* Split the u₁u₂ demand into three factors, one for each pair {i,j}, and pair it with the wire v_iv_j,
with log-dimensions in the ratio 1 : 3. The crossing identity [AN, Prop. B.2] writes the product of the two crossing
wires as a sum of polynomially many integer tensors Ψ_N whose log-ranks across the two crossing cuts satisfy
r² + r′² ≤ 2(p²+q²) (versus the trivial r, r′ ≤ p+q). By [AN, Lemma A.3] each term is a restriction of a three-wire
network with hubs at real parties, through u₁ or through u₂. Over many blocks the realisation is chosen per term;
the five parties share the whole term index as a GHZ index, which costs O(1) supply copies per block. The required
supply per block is the value n*(B) of a finite zero-sum game, with B rank buckets per pair. Because the tensors are
integer, the construction works over every field.

> **Proposition P1 [P-ref].** For every B there are explicit restrictions T^{⊗m} ≤ S^{⊗n}, over every field, with
> m/n → 1/n*(B). Exact certificates give n*(B) ≤ c_B for B = 2, 4, 8, 16, 32, so the rate is ≥ 0.83132 (B = 2) and
> ≥ 0.83671 (B = 32).

The written proof is the sketch of `protocol/notes.md` §2.3; the referee checked each step in detail (cover to
restriction via the shared index, rank accounting per bucket, adaptive rounding, all o(n) terms).
- *Certificates* (`protocol/certificates/`). A standalone verifier using only exact fractions checks, for every term
  type, an explicit mixture with all six edge loads ≤ c_B. Square roots are rounded up, which only raises the loads.
  B = 2 is also checked in Lean with the looser constant 30073/25000 = 1.20292 (`PortsLean/ProtocolCert.lean`:
  `n_star_two_le`, game arithmetic only; `decide +kernel`, not `native_decide`).
- *Closed form at B = 2.* n*(2) = 29/27 + 11√10/270 = 1.2029076084 (root of 270x² − 580x + 307). The upper bound is
  exact: an explicit mixture (α = 7/18 − √10/90, γ = 5/9 − 13√10/90) makes the three distinct loads equal to this
  number (symbolic check by the executor). An exact rational dual price gives n*(2) ≥ 1.2029076080, so the upper and
  lower rational bounds agree to nine decimals.
- *The limit [N].* In floating point n*(B) decreases for B = 8, …, 128 towards (4+√10)/6 = 1.1937129, with gap
  ≈ 0.048/B. The all-middle term type has value exactly (4+√10)/6 [P-ref: an explicit mixture and the uniform edge
  price]. That the maximum over term types is at the all-middle type is supported only numerically. So **the limit
  rate 6/(4+√10) ≈ 0.83772 rests on a numerical claim.**
- *Ceiling without nesting [N].* The minimum of R over five-point metrics satisfying the triangle inequalities and
  all instances of [AN, Prop. B.3] on the five parties is the same 0.83772. Higher rates need the construction
  nested (a finite-depth form of [AN, Lemma C.2] with explicit constants).
- *Size.* With the proved rank bounds, the first instance above 3/4 in a one-parameter scan has demand wires of
  dimension ≈ 2¹²⁸ per block (rate 0.7529 on float LPs; not a minimality statement). At class dimensions up to 5 × 5
  the middle terms have full rank (exact computation mod p), so the construction gives no gain at sizes reachable
  by dense computation.
- *Searches [N].* Alternating least squares and Levenberg–Marquardt searches, single-shot at uniform supply wire
  dimension 2 to 5 and on non-uniform demands at dimension ≤ 4, found no protocol of rate above 3/4 (best relative
  residual 0.64 at 4 → 3). Proved small-size facts for arbitrary protocols (single-shot uniform needs supply
  dimension ≥ 4; in the form T^{⊗m} ≤ S^{⊗n} the first open case is (m,n) = (4,5)) are in `protocol/notes.md` §3.3,
  not refereed.

---

## 8. Status table

| Step | By hand | Referee | Lean | Interval | Numerical |
|---|---|---|---|---|---|
| (1.1) rate formula from Strassen 1988 | [cl] | — | — | — | — |
| §1.2(a)–(c): 𝒳 ⊂ AN spectral points; prices bound protocols; border over infinite k | [P] | review-hull §6 (b, c) | — | — | — |
| §1.2(d) weighted duality (rational w, monotonicity, continuity) | [P] | review-k2m §0 (fix applied) | — | — | — |
| Prop. C.3, C.4(a),(f), thm_cn, thm_alt_rank_price | [AN] | not refereed by people; Lean by [AN], not built by us | [AN] | — | — |
| Lemma P, Corollary P (μ = max(2r,3)) | [P] | review-k2m §1 | q = 2 only: `ranks_one`, `ranks_two` | — | exact rank tables r ≤ 6 (author), r ≤ 5 (referee) |
| Lemma H_m | [P] | review-hull §§3–5 (m = 3); review-k2m §3 | **no** (hypothesis `lemmaH` in `Hull.lean`) | — | model check (m = 3) |
| W5 ⊂ diamond; model of N5 in tripod × ℝ | [P] | review-hull §5 | `model_n5`, `w5_in_diamond` | — | yes |
| (2.1) optimum of W_{m+2}; m = 3 minimum only at h = ℓ/3 | [P] | review-hull §5; review-k2m §3 | m = 3: `ratio_lower`, `ratio_at_third`, `ratio_strict`, `w5_ratio` | — | yes |
| Corollary H_m (¬Contracting ⇒ f* ≤ R_m(w)) | [P] | review-hull; review-k2m §3 | m = 3 glue: `w5_price_of_rho_price` | — | — |
| §3.1 book reduction | [P] | review-fivepoint §1 | no | — | yes |
| §3.2 calibration, Prop. C₃ (Prop. 3.2 at w = 1) | [P] | review-fivepoint §2 (w = 1); review-k2m §4 (weighted) | no | — | 200 000 + 40 000 books (referee, w = 1); 5 × 40 000 (referee, weighted) |
| Theorem D, (CL*), sharp constant 9 (inner K) | [P] | review-k2m §4 | `clstar_gen`, `clstar_weighted`, `clstar`, `clstar_weighted_sharp`, `clstar_K9`, `clstar_K_lt9_fails` | (CL*) at w = 1: `clstar` + 8 × `clnear`, two checkers (§3.5) | 4·10⁵ points per step of the chain |
| (I), with constant 8, sharp | [P] | via Theorem D | `three_angle_alg`, `three_angle`, `three_angle_I`, `three_angle_corner` | constant 9: `hull3` | 121³ grid |
| Zeros of Φ₁: 0 and six corners | [P] | — | — | — | earlier [N] searches agree |
| Theorem 5_w, Theorem 5 | = §§3.1–3.3 + C.3 | review-fivepoint; review-k2m | no (only the final inequality) | via (CL*) at w = 1 | Toyoda SIP: 1000/1000 at W5 |
| Uniqueness of the minimiser W5 | [P], new | **not refereed** | — | — | consistent with searches |
| Theorem B (averaging) | [P] | review-k2m §5 | `k2m_average`, `R_eq`, `k2m_rate` (arithmetic only) | — | m-page books, m ≤ 6 |
| Theorem K.1, K_m.1 | = C.3 + Theorem B + §1.2(d) | review-fivepoint; review-k2m | no | — | — |
| K_m.3 routing, cuts, strictness | [P] | review-k2m §7 (LPs, brute-force cuts) | m = 3: `flow_bound`, `cut_ineq`, `cut_v1` | — | yes |
| §4.3 failure of direct m-page calibration | [P] | review-k2m §7 | — | — | yes |
| K.3: Contracting ⇒ 3-SAT in 2^{O(n^{1−δ})} | [CE] | Theorem R non-uniform: refereed; uniform: audit; Theorem A: refereed; IM 7.1: not reviewed | arithmetic only (`ThmR.lean`, `ThmA.lean`) | — | — |
| K.4(a) rate 1 single-shot impossible | [P] | — | no | — | ALS floor √(5/8) at D = 2 |
| K.4(b) bond 2 border over ℂ | [P], uses [Lan06] | — | no | — | ALS floor 0.6695 |
| K.4(c) ℓ₁ ⇒ R ≥ 1; cut {v₁} gives 1 | [P] | — | `cut_ineq`, `w5_not_cut_combination`, `cut_v1` | — | — |
| §7 explicit family, rate ≥ 0.83671 | [P] (sketch-level write-up) | review-protocol: no fatal gap | B = 2 game: `n_star_two_le` | exact rational certificates B = 2…32 | limit 0.83772 only numerical |

**Trust base of item 1.**
1. [AN] Theorem C.1 (`thm_cn`) and Prop. C.3, with Lemma C.4(a). The direction used is price ⇒ CAT(0) embedding.
   C.4(a) is a standard CAT(0) fact. Alternatively, [EG] Thm 4.3 with Cor. 3.4 gives the CAT(0) embedding for points
   of Strassen's spectrum directly (§1.3); item 1 then uses nothing from [AN].
2. Strassen's spectral theorem for the semiring of tensors on the m+2 parties over k [Str88]. Alternatively, [AN]
   Theorem A.6 with the cover-to-restriction step of §1.1.
3. §3.1 and Prop. C₃: elementary, checked by hand by referees and numerically.
4. Theorem D: six lines by hand, and in Lean (`clstar_weighted`, `clstar`).
5. For m ≥ 4: Theorem B, whose arithmetic is in Lean (`k2m_rate`).
6. Not needed: interval arithmetic, Reshetnyak gluing, Toyoda's theorem, m-page books, uniqueness of the minimiser,
   anything from OpenAI.

**Weakest points.** The computer is no longer part of item 1. What remains:
- the **book reduction and the calibration** (§§3.1–3.2): proved by hand and checked by one referee each
  (review-fivepoint at w = 1; review-k2m for the weighted form), with numerical tests, but not in Lean;
- the **imported statements from [AN]** (C.1/C.3, C.4(a), and for item 2 also C.4(f) and `thm_alt_rank_price`): the
  paper is machine-generated and not refereed by people, and we have not built its Lean.

For item 2 there is in addition Lemma H_m, refereed twice but not in Lean (Mathlib has no CAT(0) theory).

---

## 9. Open problems

1. **Explicit protocols between 0.8377 and 3/√10** (§7). They need the crossing construction nested, with a
   finite-depth form of [AN, Lemma C.2] and explicit constants. Also open: a proof that the bucket game is maximal
   at the all-middle type, which would make the limit 6/(4+√10) exact; smaller instances; and any explicit protocol
   on K_{2,m}, m ≥ 4, above routing. Above 3/√10, a protocol over a field of characteristic 0 would imply
   Contracting there (§5).
2. **Solved: an analytic proof of (I) and of (CL*).** Theorem D (§3.3) proves (CL*) and (I) by hand and in Lean,
   with the sharp constants: in (I), 8 in place of 9, attained at (π/2, π/2, −π/2); in (3.5), inner constant 9 in
   place of 10.
3. **Attainment in 𝒳.** W5(ℓ,ℓ/3) is the unique minimiser among five-point CAT(0) configurations (§3.4; not
   refereed). Since the minimum over AN prices is attained (§1.2), f*(k) = 3/√10 ⇔ W5 is an AN price over k
   (⇔ tripod × ℝ is a price space over k, by the unrefereed direction of §2.3). It is not known whether some point
   of Strassen's spectrum 𝒳 has R = 3/√10; for 𝒳 only the infimum is known to equal f*.
4. **K_{2,m} beyond the proved range.** For w > m(m−1)/6 (for m = 3: w > 1) the lower bound R_m(w) is not proved,
   and Theorem D fails there (§3.3, remark 3). Which other two-apex networks, and which other demand vectors, are
   pinned by five-point (or (m+2)-point) CAT(0) inequalities is open. For instances where six or more points interact
   essentially, box inequalities do not suffice (§3.6); one needs the full cone of quadratic inequalities valid in
   CAT(0) spaces (Andoni–Naor–Neiman 2018, Thm 1.1, as quoted in [Toy24]; [Toy24b] gives the first explicit
   six-point inequalities not implied by the box inequalities).
5. **Lean formalisation.**
   - The book reduction and the calibration are elementary real analysis and look within reach; with Theorem D
     and `k2m_rate` already in Lean, they would complete item 1 in Lean from C.3, C.4(a) and Strassen's theorem.
   - Lemma H_m needs a CAT(0) library, or at least C.4(a),(f) as axioms in the style of `HullHyps`.
   - Connecting to [AN]'s own `prop_space` and `thm_alt_rank_price` requires building their development.
6. **Whether contracting decides the rate.** If contracting holds over k, is f*(k) > 3/√10? By uniqueness this is
   equivalent to W5 not being an AN price over k, and (with the unrefereed direction of §2.3) to N5 not being one.
   Contracting alone does not obviously decide it.

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
- Working files:
  - `research/ports/hull/notes.md` (§§1–3); `research/ports/review-hull.md`; `research/ports/review-fivepoint.md`;
  - `research/ports/k2m/notes.md` (§§0–4) and `research/ports/review-k2m.md`;
  - `research/ports/protocol/notes.md`, `protocol/certificates/README.md`, `research/ports/review-protocol.md`;
  - `research/ports/e3/notebook.md`;
  - `research/ports/lean/` (`W5.lean`, `Hull.lean`, `CLStar.lean`, `ProtocolCert.lean`, `NOTES.md`);
  - `tools/ivcert/` (`run_proofs.sh`, `src/problems/clstar.rs`, `certs/`), `tools/ivcheck2/`.

---

## Earlier changes (literature check)

After `literature-check.md` (26 November 2026), with no mathematical claim changed: §0.1 identifies the instance as
the Okamura–Seymour example and cites its classical network-coding rate, the novelty sentence and the October 2026
multiple-unicast preprints; §0.2 gained "Not LOCC, not a coding improvement"; [EG] Thm 4.3 was added as an
independent CAT(0) source, [MM] as related geometry, Toyoda's five-point limitation, the laminar and upper support
functionals in §6(c), and the corresponding references.

## Changes in this version

*Substance.* (1) Item 1 is no longer computer-assisted: (CL*) is proved analytically (Theorem D, §3.3; Lean
`clstar_weighted`, `clstar`), with the sharp constants 9 in (3.5) and 8 in (I); the interval material is compressed
into §3.5 as an independent confirmation. (2) New general statement Theorem K_m for K_{2,m} with weight w on u₁u₂
(§0.1, §4), from the weighted calibration (Prop. C₃), Theorem D, averaging over five-point subsets (Theorem B; Lean
`k2m_rate`), Lemma P and Lemma H_m (§2); weighted duality §1.2(d) with the referee's rational-w/continuity argument;
corrected table row m = 6 (0.399114, 1.0643); the failure of the direct m-page calibration as a remark (§4.3). (3)
The explicit protocols have their own section (§7), with exact certificates to B = 32, the closed form of n*(2), and
the limit marked as numerical. (4) The zeros of Φ₁ are determined by proof, and from this uniqueness of the
minimiser W5 is derived (§3.4; new and not refereed). *Status changes.* Trust base, status table and weakest points
(§8) are rewritten: the weakest points are now the book reduction and calibration (refereed, not in Lean) and the
imported [AN] statements. Open problem "analytic proof of (I)" is recorded as solved; the open problem on K_{2,m}
is replaced by the range beyond m(m−1)/6; uniqueness is replaced by attainment in 𝒳. The [D] tag, used but not
defined in the first version, no longer appears. *Title* changed to cover K_{2,m}; the Okamura–Seymour case stays
Theorem K.
