# The clause-width dependence of Anthropic's #k-SAT bound: where k² comes from, and which factor can go

Plan: `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/plans/sat-width-plan.md`.
Sources: Anthropic's paper text `/tmp/claude-0/-home-user-lean-code/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/anth/fm/paper.txt`
(App. D l.2060–2452), Lean under `/home/user/anth-build/proof/`, OpenAI's preprint (read-only .tex)
`.../scratchpad/oai-math-latest/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/{main_full_version,quantitative-reduction}.tex`.
Scripts: `/home/user/eth-hamiltonicity/research/scripts/satw_*.py` (each prints PASS/FAIL, output in `.out` beside it).

## 0. Verdict

Anthropic's Theorem D: #k-SAT in 2^{C k² n log log n/√log n}, for k ≤ (log n)^{1/4}.

* **The two factors k.** One is the **arity of a mark**: a violated-clause mark has to reach the ≤ k nodes that hold
  the clause's variables. The other is **log of the clause density of a sparsification output**:
  log(m_G/n) ≤ log Δ = Θ(k log(k/ε)). Δ itself enters U only through m ≤ Δn (Prop. 1.1).
  The arity factor is k·M·log(I/M), with M = Θ(n) marks among I incidences.
* **Can one factor of k be removed? No, not by this mechanism, in the range of k where it matters.** It is open
  outside the mechanism.
  * The density route (A1) is impossible for k ≥ C log log n. **Theorem S (§3.3, new; proved, numerically checked)**:
    some k-CNF φ (density ≈ 0.69·2^k/k) has the following property. Every expression sol φ = ⋃_{i ≤ 2^{εn}} sol G_i,
    with each G_i a CNF of width ≤ k' on the same n variables, contains a G_i with
    log₂(m_{G_i}/n) ≥ k(1−ε) − log₂(k(k' log₂ 2n + 2)) − 3.
    So no sparsification has density poly(k/ε) once k ≳ 4c·log log n (c the degree of the polynomial).
    For k ≤ C log log n the two bounds differ only by a log log n factor, and both are subexponential there anyway.
  * Within the clause-mark design of Steps 1–3, the remaining factors are tight up to constants (§2):
    * the rank lemma: c_{ab} ≥ log C(t_{ab}, μ_{ab});
    * connectivity: t_o − 1 tests per mark;
    * the 2-adic cut-off: M ≥ ν − 1 + r with ν ≥ n+1; p = 2 is optimal, and parity is the unique fastest check function;
    * averaging: every catch family has mean check size ≥ m/(4(n̄+1)).
  * OpenAI's route (A3) is **not** variable-parity. Their tests are clause-violation parities, i.e. F₂-polynomials of
    degree ≤ k. Their engine-II network is bipartite (test groups × variable groups), so an incidence touches 2
    nodes. But a monomial of a violated clause has degree k, and the wire budget is
    K log(e(N+K)/K) with **K = k(a + 2(ℓ−1)) = Θ(kn)**. That is the same k × log(sparsity), with sparsity
    (log n)^{Θ(k)}. Their k-dependence is hidden in O_k; their sparsifier has log B ≈ k² log 3 (§4).
* **What *is* removable, proved by inspection (not Lean-checked).**
  * For formulas of density d = m/n, branching on the ≤ n/√log n heaviest variables (OpenAI's trick) and then
    Steps 1–4 with the density form of (68) gives **#k-SAT in 2^{O(k n log(2d)/√log n + n/√log n)}**, which has one
    factor of k (§5.2). With only the Lean-proved (68) and Δ ≤ k d √log n after branching, the exponent is
    O(k n (log(2kd) + log log n)/√log n).
  * So the k² is exactly the price of the input density after sparsification. By Theorem S that price is Θ(k) in
    the worst case.
  * The best general bound left inside the mechanism needs a disjoint sparsifier with density 2^{O(k)}·poly(1/ε).
    Its existence is open; Calabro suspects density Θ(2^k) (thesis §5.1). It would give exponent
    O(k² n/√log n + k n log log n/√log n): the log log n leaves the k² term, and the subexponential range grows
    from k = o((log n)^{1/4}/√log log n) to k = o((log n)^{1/4}).

## 1. Anatomy of the exponent (verified against the Lean and the paper)

All paths below are under `/home/user/anth-build/proof/`; every line number was checked.

| piece | where | bound | k-dependence |
|---|---|---|---|
| tests per object | `variables/VariableBound/Net/SizeU.lean` `tests_le` l.104 | T₀ ≤ (k−1)m, T₁ ≤ k·I, n̄·I ≤ r·16m | arity: k−1 tests for a clause, ≤ k for an incidence (E,j) |
| kind 0 (cut-off Π₀, \|Π₀\| ≤ n̄+1) | `kind_zero_le` l.123 | log C(T₀,μ₀) ≤ (k−1)(n̄+1)·3 log(2Δ) ≤ 3(k−1)(n + log 2Δ) | **O(kn)**: log Δ cancels against n̄ ≈ n/log 2Δ |
| kind 1 (check incidences, ≤ M marks) | `kind_one_le` l.164 | log C(T₁,μ₁) ≤ kM·log(3·16m/n̄) ≤ kM·log(96Δ log 2Δ) | **k·M·log(m/n̄)**, the only k·log Δ |
| total | `stU` l.231, `stUPrinted` l.262 | U ≤ 6(k−1)(n + log 2Δ) + 2kM log(96Δ log 2Δ) + 2g² ≤ 6k(n+log 2Δ) + 28kn log(96Δ log 2Δ) + 2g² | (68) |
| M | `statements/AppVariablesStatement.lean` l.148–163 (`IsNb`, `beta`, `IsRb`, `Mb`, `IsTb`) | M = r̄ + β − 1 ≤ 14n (61) | — |
| log Δ | `variables/RecursionToBound/Defs.lean` l.115 `occBound`; l.249 `OutputsAreWithinTheSetting`; l.263 `OccBoundIsThePrinted` | Δ ≤ 2(θ₀+…+θ_{k−1})+2 ≤ 2(8k/ε)^{3k}+2; log Δ ≤ 3k log(8k/e) + 2 | **the second k** |
| thresholds | `sparsification/SparsificationLemma/Cal/Defs.lean` l.37–53 (`xC, logC, alphaC, betaC, thetaC`) | α = ⌈2(k−1)²ε⁻¹⌈log 32(k−1)²/ε⌉⌉, β₁ = 2, β_c = Σ 4αβ_{c−h}β_h, θ₀ = 2, θ_c = αβ_c | log₂ occBound / ((k−1)log₂(k/ε)) ∈ [1.5, 3.8] for k ≤ 12 (`satw_exponent.py` X1) |
| exponent | `variables/VariableBound/Printed/ThmVariablesADefs.lean` l.72 | `expVariablesA k n e = k²·e·n·lg(k/e)` | k² |

The paper's own remark (l.2425–2430) says the same thing: "Of the two factors k, one comes from the up to k tests of a
mark and the other from log Δ = O(k log(k/e))". `satw_exponent.py` X3 reproduces the remark that ends App. D: for
k = 3 the bound beats 2^n only if e < 2.09·10⁻⁴, i.e. ℓ ≥ 23 and log₂ n > 8.56·10⁹.

**Proposition 1.1 (density form of (68); by inspection of the paper, with the Lean lemmas as the template).**
In Steps 1–3, Δ is used in two ways:
* through m ≤ Δn. This happens in n̄ (`IsNb`), in s̄ < 32Δ log 2Δ, in β ≤ 4n + 3 log 2Δ + 2, in p·r̄ < 22 log 2Δ,
  and in t̄. In Lean these are `kind_zero_le` / `kind_one_le`, which take `hm : m ≤ Δ * n` and nothing else about Δ.
* as a maximum occurrence. This happens only in the parameter bound (69), gP ≤ 2(n+g)(1 + Δ(t̄+3)) + …. Step 4 then
  needs gP/K = o(en), i.e. Δ ≤ n^{1/(40C₀)}.

Put d̂ = max(2, ⌈m/n⌉) in place of Δ wherever Δ is used through m ≤ Δn, and keep the true maximum occurrence
Δ_occ ≤ n^{1/(40C₀)} for (69). Then

  U ≤ 6k(n + log 2d̂) + 28 k n log(96 d̂ log 2d̂) + 2g².

In Lean this needs a `Setting` (`variables/VariableBound/Net/Defs.lean` l.298) with two parameters, `occ_le` with
Δ_occ and `m_le`/`isNb` with d̂. The current structure uses one Δ for both. `stU` itself would be unchanged.

So **U = O(k n log(m/n))**. What multiplies the arity k is the log of the clause density, not of the maximum
occurrence.

## 2. Inside the clause-mark design: each remaining factor is forced

### 2.1 The model (Steps 1–3 of App. D, abstracted)

A **clause-mark network** for a CNF G (width ≤ k, m clauses, n variables, g nodes) consists of the following data:

1. A placement of the variables on g nodes. For a clause E, N(E) is the set of nodes holding its variables, t_E = |N(E)|.
2. A cut-off n̄ and a list Λ = (Λ₁,…,Λ_r) of checks Λ_j ⊆ G with X(Λ) = 0 (62). Equivalently: every ξ with
   |V(ξ)| > n̄ has some j with |Λ_j ∩ V(ξ)| odd.
3. A 2-adic truncation of the form of Lemma 12: [q even] = Σ_i σ_i C(q,i), keeping the tuples (Π₀; Π₁,…,Π_r) with
   Σ_j |Π_j| ≤ M′, valid modulo 2^ν.
4. Objects: the clauses (kind 0) and the incidences (E,j), E ∈ Λ_j (kind 1). An object o touches N(o) (for (E,j):
   N(E) ∪ {h(j)}). Its mark bit is replicated at every node it touches. A node verifies that a marked object has all
   its literals false at that node.
5. For each pair {a,b}, Ψ_{ab} is the **equality** of the mark strings of the objects whose test graph contains
   {a,b}. Each object's test graph is a graph on N(o).
6. Profiles fix μ_{ab} = the number of marked objects with test {a,b}. The cost of a profile is
   U = 2Σ_{a<b} c_{ab}, with c_{ab} the number of bits Ψ_{ab} factors through.

Anthropic's Step 3 is this model with path test graphs, rank encoding, M′ = M and the checks of Lemma 13.

### 2.2 The lemmas (each one a real statement inside the model)

**Lemma A (rank).** Let Ψ(z,z′) = [s(z) = s(z′)], where s takes each of N strings on both sides. If Ψ factors
through c bits, Ψ(z,z′) = Σ_{θ∈{0,1}^c} f(z,θ) f′(z′,θ), then 2^c ≥ N.

*Proof.* The N×N identity is a submatrix of Ψ and has rank N, while a factorization through c bits has rank ≤ 2^c. ∎

So c_{ab} ≥ log₂ C(t_{ab}, μ_{ab}). Every string with μ_{ab} ones occurs: a node can make the literals of any μ_{ab}
objects false. The rank code `cw t μ = ⌈log C(t,μ)⌉` of `Net/Rank.lean` is therefore optimal for each pair.
(`satw_cover.py` C3.)

**Lemma B (connectivity).** Suppose the test graph of some object o does not connect N(o). Then the network has
terms in which o is marked on one component and unmarked on another. Such terms are not tuples of (65), so the value
is no longer the right side of (65). Hence each marked object costs at least t_o − 1 tests.

When the clauses' variables lie on distinct nodes (the typical case when g ≫ k², and the worst case over placements
for expanding formulas), this is k−1 tests per clause and k per incidence.

**Lemma D (2-adic cut-off).**
(i) Recovering F ∈ [0, 2^n] needs ν ≥ n+1.
(ii) A tuple with all |Π_j| ≤ 1 has 2-adic weight 0, so Lemma 12's truncation must keep every tuple with up to
r + ν − 1 marks: M′ ≥ ν − 1 + r ≥ n.
(iii) For a prime p, the Newton coefficients of [q ≡ 0 mod p] satisfy v_p(c_i) ≥ ⌈i/(p−1)⌉ − 1, with equality
infinitely often. That is log₂p/(p−1) bits per mark: 1 for p = 2, 0.79 for p = 3, 0.58 for p = 5. The moduli 4 and 8
are worse still.
(iv) Over **all** check functions f: {0..14} → {0,1} with f(0) = 1 and f(1) = 0, min_i (v₂(c_i) − (i−1)) ≤ 0, and only
f = [q even] attains 0.

So parity with p = 2 needs the fewest marks per bit of precision. (`satw_newton.py` N1–N4; (ii) is checked by the
truncation at M′−1 failing in 61 of 300 random cases.)

**Lemma C (n̄-implication).** Let Λ* = ⋃_j Λ_j and G′ = G ∖ Λ*. Then |V_{G′}(ξ)| ≤ n̄ for every ξ ∈ sol(Λ*).

*Proof.* Such a ξ violates no clause of any check, so every check is even, so |V(ξ)| ≤ n̄. ∎

The naive corollary Σ_{E∈G′} 2^{−|E|} ≤ n̄ ("the checks must cover all but 2^k n̄ clauses") is **false**. Counterexample:
G = (x₀), (x₀∨x_i) for i ≤ 7, with Λ = ({(x₀)}). This gives X = 0 but a sum of 1.75 > n̄ = 1 (`satw_cover.py` C2,
witness). Clauses that Λ* implies, or nearly implies, need no check. So I is lower-bounded only through the family
design (Lemma E), not unconditionally.

**Lemma E (averaging).** Let Γ_u (u ∈ Ω) be a family in which every set V of v+1 clauses has odd intersection with at
least |Ω|/4 members (Lemma 13(c)). Then the mean of |Γ_u| is ≥ m/(4(v+1)).

*Proof.* For a uniform (v+1)-set V, Pr[|Γ∩V| odd] ≤ E|Γ∩V| = |Γ|(v+1)/m. Average over u. ∎

The Monte Carlo of Lemma 13's GF(2^s) family (m up to 256) gives a mean |Γ_u| within a factor 4.2–5.0 of this bound,
and min_V Pr[odd] ≈ 0.41–0.45 ≥ 1/4 (`satw_cover.py` C1). So Lemma 13 is optimal up to a constant, and
log(I/M) = log(m/n̄) − O(1) for any family-based kill.

### 2.3 Theorem K (the kill costs Θ(k·n·log(m/n̄)) in the design)

In the model of §2.1, assume (H): I = Σ_j|Λ_j| ≥ c·r·m/(n̄+1). By Lemma E this holds in expectation for checks drawn
uniformly from any family with property (c) of Lemma 13 at v = n̄ (c = 1/4). Also place the variables so that a
constant fraction of the clauses span ≥ k/2 nodes. Then the worst admissible profile has

  U_kind1 ≥ (k/2 − 1)·(r + n)·(log₂(m/(4(n̄+1))) − O(1)),  U_kind0 ≥ (k/2 − 1)(n̄+1)(log₂(m/(n̄+1)) − O(1)).

The paper's (68) has the matching upper bound, O(k n log(m/n̄)).

*Proof.* Take μ_{ab} ∝ t_{ab}. By Lemmas A and B, U ≥ Σ log C(t_{ab}, μ_{ab}) ≥ μ log(T/μ) − O(μ). Then:
* μ ≥ (k/2 − 1)·#marks;
* #marks ≥ r + ν − 1 by Lemma D;
* T/μ ≥ I/#marks;
* I ≥ c·r·m/(n̄+1) by (H). The greedy's chosen list need not satisfy (H): Lemma E bounds family means, not the
  minimiser of Υ. This is part of the caveat below.

The kind-0 bound comes the same way, with T₀/μ₀ = m/(n̄+1). ∎

Balancing n̄: kind 0 wants n̄ ≲ n/log(m/n), and kind 1 then pays log(m/n̄) ≥ log(m/n). Neither choice of n̄ escapes
k·n·log(m/n).

*Caveat (open, not covered by the theorem).* A structure-aware kill could use small checks adapted to the sets V(ξ)
(they are 2^n special sets, not arbitrary (n̄+1)-sets). By Lemma C such a kill cannot be ruled out in general. Every
construction we know (Lemma 13; OpenAI's Tanner code plus greedy, §4) has checks of size ≳ m/n̄.

### 2.4 Failed shortcut: incidence marks inside clause marks

The idea is to make the kind-1 marks a sub-selection Π_j ⊆ Π₀ ∩ Λ_j, so that a marked incidence only travels from E's
owner to h(j) (arity 2). For one ξ it replaces [V = ∅] by

  S(V) = Σ_{Π⊆V} (−1)^{|Π|} Π_j [|Π ∩ Λ_j| even] = 2^{|V| − rank(Λ|_V)}·[1_V ∈ span_{F₂}(Λ_j|_V)].

This is nonzero for many nonempty V, e.g. V = {E} with Λ₁ = {E}, where S = 1. So the shortcut is not inclusion–exclusion.
`satw_pi0_fail.py` checks the identity on 400 random instances (128 of them have nonempty V with S ≠ 0) and confirms
that the correct expansion (65) gives [V = ∅]·Π[|V_j| even].

## 3. Sparsification: known bounds, lower-bound status, and what would plug in

### 3.1 Known upper bounds (exact statements)

* **IPZ 2001** (Impagliazzo–Paturi–Zane, *Which problems have strongly exponential complexity?*, JCSS 63(4) 2001).
  Every k-CNF is an OR of ≤ 2^{εn} k-CNFs, each with ≤ c(k,ε)·n clauses. Their c is **doubly exponential in k**
  (Calabro thesis, Ch. 5 intro; Santhanam–Srinivasan §1).
* **Calabro–Impagliazzo–Paturi, CCC 2006** (*A duality between clause width and clause density for SAT*, pp. 252–260):
  a sketch of the singly exponential bound.
* **Calabro, PhD thesis (UCSD 2009), Theorem 5.15** (read from the PDF). There is an algorithm A such that for all
  k ≥ 2, ε ∈ (0,1] and φ ∈ k-CNF with n variables, A outputs φ₁,…,φ_s ∈ k-CNF with n^{O(k)} delay and:
  * s ≤ 2^{εn} and sol(φ) = ⋃ sol(φ_i);
  * each disjunction of h literals occurs ≤ O(k/ε)^{3(k−h)} times in φ_i;
  * (a) each literal occurs ≤ O(k/ε)^{3k} times;
  * (b) |φ_i| ≤ O(k/ε)^{3k} n.

  Lemma 5.14 / (5.4): the count is ≤ 2 + 4α(32α)^{k−h−1}. This is what Anthropic uses (paper l.2397–2403; Lean
  `occBound`, `OccBoundIsThePrinted`).
* **Counting (disjoint) version:** Dell–Husfeldt–Marx–Taslaman–Wahlén, App. A (cited by OpenAI). Anthropic's version
  adds the side list {¬ω : ω ∈ H} to the heavy child (App. C; Lean `SparsifyWidthK`, `StepSparsify.exactly_one`).
* **OpenAI App. A** (main_full_version.tex l.3636–3884). θ_j = M^j, B = 2Σ_{j<k} M^j ≤ 4M^{k−1}, where M is the least
  power of two ≥ Γ = 2(3^{k−1}−1) with Γ⌈log₂ 4CM⌉ ≤ σM. Hence log₂ B ≈ (k−1)·((k−1)log₂3 + log₂(k/σ)), i.e.
  **Θ(k²) for fixed σ**: worse in k than Calabro's (`satw_exponent.py` X2: log₂ B/k² ≥ 2.6 for k ≤ 12, and it tends
  to log₂3). Their Lemma `lem:sparsify` hides this in B = O_k((σ⁻¹ log(2/σ))^{k−1}).

### 3.2 Lower-bound status in the literature

* **Santhanam–Srinivasan, "On the limits of sparsification"** (ECCC TR11-131; ICALP 2012). Their lower bounds are
  for **unbounded-width** CNFs:
  * Thm 1: for every f(n) = ω(n) there are CNFs of size f(n) that are not an OR of 2^{n−εn} linear-size CNFs.
  * Thm 2: a hierarchy n^{k′} vs n^k.

  They say nothing about how c(k,ε) depends on k. Their method is a union bound over n^{O(n)} linear-size CNFs and
  needs superlinear size.
* **Calabro thesis §5.1** states the k-dependence as open: "we suspect that the problems can be reduced to each other
  in subexponential time when Δ = Θ(2^k) … it would suffice to bound the sparsification constant by O(2^k). We do not
  accomplish this."
* Web searches (Oct 2026) found no lower bound on the k-dependence of c(k,ε) for k-CNFs.

### 3.3 Theorem S (new): sparsification needs log-density ≈ (1−ε)k

**Theorem S.** Let k ≥ 3, k′ ≥ 1, n ≥ 2, 0 < ε < 1, α = (1−2^{−k})/(k log₂e), m = ⌈α2^k n⌉ and
σ = 1 − ε − 1/k − 3/n. Suppose D > 0 satisfies

  (*) 2^{Dn(k′ log₂(2n)+2)}·exp(−m·2^{−k(1−σ)}) < (1−2^{−k})^m / 2.

Then there is a k-CNF φ with m clauses on n variables such that no N ≤ 2^{εn} CNFs G_1,…,G_N of width ≤ k′ on the
same variables, each with ≤ Dn clauses, satisfy sol φ = ⋃ sol G_i. Disjointness is not needed.
(*) holds for all D < (2^{k(1−ε)−3})/(k(k′ log₂(2n)+2)) whenever k(1−ε) ≥ 3. So every such cover contains a G_i with

  **log₂(m_{G_i}/n) ≥ k(1−ε) − log₂ k − log₂(k′ log₂(2n) + 2) − 3.**

*Proof.* Let φ have m independent uniform clauses (uniform k-set of variables, uniform signs).

1. (Shearer.) For a fixed S ⊆ {0,1}^n with |S| = 2^{σn} and a uniform clause C with falsifying pattern b on V:
   * S ⊆ sol C iff b ∉ S_V (the projection), so Pr[S ⊆ sol C] = 1 − E_V|S_V|/2^k.
   * For X uniform on S, Han/Shearer gives E_V H(X_V) ≥ (k/n)H(X) = kσ.
   * Then E_V|S_V| ≥ E_V 2^{H(X_V)} ≥ 2^{kσ} by Jensen.

   Hence Pr_φ[S ⊆ sol φ] ≤ (1 − 2^{−k(1−σ)})^m ≤ exp(−m 2^{−k(1−σ)}).
2. (Union bound.) There are ≤ 2(2n)^{k′} clauses of width ≤ k′, so ≤ 2^{Dn(k′ log₂ 2n + 2)} formulas with ≤ Dn clauses.
   So Pr[∃ G: |sol G| ≥ 2^{σn}, sol G ⊆ sol φ] is below the left side of (*).
3. (Many solutions.) Let Z = |sol φ|. Then E Z = 2^n(1−2^{−k})^m and Z ≤ 2^n. So
   Pr[Z ≥ EZ/2] ≥ EZ/2^{n+1} = (1−2^{−k})^m/2, which is the right side of (*).

   So some φ has Z ≥ EZ/2 and no sparse G with ≥ 2^{σn} solutions inside sol φ. In a cover by such G_i every G_i has
   fewer than 2^{σn} solutions. Using −m log₂(1−2^{−k}) ≤ m2^{−k}log₂e/(1−2^{−k}) ≤ n/k + 1 (with m ≤ α2^k n + 1),
   N ≥ (EZ/2)/2^{σn} ≥ 2^{n(1−σ) − n/k − 1 − 1} = 2^{εn + 1} > 2^{εn}.

For the bound on D, note that log₂e·m·2^{−k(1−σ)} ≥ n(1−2^{−k})2^{kσ}/k and that the right side of (*) is
≥ 2^{−n/k − 2}. With 2^{kσ} ≥ 2^{k(1−ε)−1−3k/n}, (*) holds when D(k′log₂ 2n + 2) < (1−2^{−k})2^{k(1−ε)−1−3k/n}/k − 1/k − 2/n,
which holds for D < 2^{k(1−ε)−3}/(k(k′log₂(2n)+2)) once k(1−ε) ≥ 3 (checked numerically in S3). ∎

Checks (`satw_sparsity_lb.py`):
* S1: the hit probability against 2^{−k(1−σ)} is exact over all k-sets, for random sets, subcubes, affine subspaces
  and Hamming balls (minimum ratio 1.107).
* S2: Monte Carlo of Pr[S ⊆ sol φ].
* S3: the closed-form D* for k ≤ 200 and log₂ n ≤ 4096.
* S4: the crossover with poly(k/ε) densities.

**Consequences.**
1. *A1 (the density route) is closed where it matters.* Theorem D runs with ε ∈ [e, 2e] and e ≈ 1/√log n.
   * A density bound (k/ε)^c means log₂ D ≤ c(log₂ k + ½ log₂ log n).
   * Theorem S forces log₂ D ≥ k − log₂(k² log n) − O(1).
   * So such a sparsifier cannot exist for k ≥ (c/2 + 3) log₂ log n + O(log k). The crossover is k = 57 / 83 / 137 / 241
     for log₂ n = 2^{10} / 2^{20} / 2^{40} / 2^{80} at c = 3 (S4).
   * The paper's Remark (l.2431–2434: "occurrences polynomial in 1/ε … for fixed k") is consistent with this: for
     fixed k, density 2^{O(k)}·poly(1/ε) is not excluded.
2. *Theorem S is tight in k up to constants*, against Calabro's O(k/ε)^{3k}: log D = Θ(k) for constant ε. Whether
   log D = O(k + log(1/ε)) is achievable (Calabro's suspicion, sharpened) is **open**.
3. *Limits of the lower bound.* It loses log n, as in Santhanam–Srinivasan, so for fixed k it says nothing. It
   concerns outputs on the same n variables. Outputs with extension variables (Tovey copies, gate variables) are not
   covered, but they enlarge n and hence U ∝ n.

### 3.4 What would plug in (exact replacement for `OccBoundIsThePrinted`)

Keep `OutputsAreFew` (≤ 2^{εn} outputs, ε ∈ [e,2e]) and `exactly_one` / `count_eq_sum` (disjointness). Replace the
occurrence statement by two:

* `OccBoundSmall`: every output has maximum occurrence ≤ n^{1/(40C₀)}. Calabro's (8k/ε)^{3k} already gives this for
  k ≤ (log n)^{1/4}.
* `DensityBound(f)`: every output has m_G ≤ f(k,ε)·n.

Then by Prop. 1.1 the exponent is O(e k n log f(k, e)) + 2en. The possibilities:
* f = poly(k/ε): exponent O(k n log log n/√log n). Excluded for k ≥ C log log n by Theorem S.
* f = 2^{O(k)} poly(1/ε): exponent O(k² n/√log n + k n log log n/√log n). Open.

## 4. OpenAI's route (A3), from the primary .tex

* **Theorem (main_full_version.tex l.69–81).** For each fixed k ≥ 2, #F in (n+m)^{O_k(1)} 2^{O_k(n log log n/√log n)}
  bit operations and poly space. For m ≤ Dn the time is 2^{O_{k,D}(n/√log n)}. The interpolation version has
  O_k(ρ(n)) with ρ = n(log log n)²/√log n (Prop. `prop:interpolation-bound`). **k is fixed and no k-dependence is
  stated.**
* **Their "weaker" route (l.1429–1504).** Sparsification, then Tovey copying to a 3-CNF with ≤ 3 occurrences on
  N = O_k(Bn) variables, gives 2^{O_k(σn + Bρ(n))}. With σ ≈ (log n)^{−1/(2k)} this is
  2^{n(log log n)^{k+1}/(log n)^{1/(2k)}}, i.e. only 2^{o(n)}.
* **"Polylog sparsity" means (log n)^{Θ_k(1)}** (l.3240–3500, `lem:sparse-checks`, `lem:greedy-hashes`):
  * initial Tanner-code rows have support ≤ D₀ = 320000 B² μ³;
  * the greedy rows have list length P = 20000 B² μ², with μ = ⌊log₂ m⌋ + 1 and B = O_k((σ⁻¹ log)^{k−1}) = λ^{O_k(1)}.
* **The tests are clause parities, not variable parities.** P_i(x) = Σ_{e: A_{ie}=1} v_e(x) over F₂, with v_e a product
  of ≤ k factors x_v or 1+x_v. So a test is a degree-≤ k polynomial with ≤ 2^k·max(D₀,P) monomials.

  A variable-parity test cannot work in general: a check must accept every satisfying assignment, so a check
  ⟨a,x⟩ = b requires sol(Φ) to lie in a hyperplane.

  The degree of a clause parity is exactly k unless supports cancel. The top homogeneous part of Σ_{e∈S} v_e is
  Σ_{e∈S, |e|=k} x_{supp(e)}, whatever the signs. So deg < k iff every k-support occurs an even number of times in S.
* **Where the k sits in their engine** (quantitative-reduction.tex l.100–300, `lem:tensor-sparse-query`).
  * The network is bipartite: J = ⌈n^{1/4}⌉ test groups × J variable groups. Each incidence indeterminate z_{iv} joins
    one test group to one variable group, so **an incidence touches 2 nodes**. This is the "arity-2 mark" the plan
    hoped for.
  * But the factor B_i has incidence degree ≤ k(1+2j) in V^j, and the global truncation (`lem:total-order`,
    main_full_version.tex l.2958) bounds the monomial degree by **K = k(a + 2(ℓ−1))** (eq. `sharp-incidence-degree`).
  * The wires are M ≤ J² + K log₂(e(N+K)/K) (eq. `sharp-wire-budget`), with N ≤ a·k·λ^c.
  * So M = Θ(k n · log(λ^c)) = Θ(k · c(k) · n log log n): **the same product (degree/arity k) × log(sparsity)**, with
    c(k) = Θ(k) from B = λ^{Θ(k)}. A violated clause costs k incidences (degree) instead of k−1 tests (arity); each
    costs log(N/K) instead of log(I/M).
* **Import into `netD`?**
  * The bipartite variable-node layout is already Anthropic's (nodes hold variables, the home h(j) holds the check).
  * Lemma B applies equally to a monomial whose k variables sit at k variable groups: OpenAI pays this as k
    incidence wires, Anthropic as k−1 tests.
  * No saving, so A3 gives no lever on k.
  * OpenAI's useful extra is **branching on the ≤ n/√λ variables in more than D* scopes** (l.130–145), which caps the
    maximum occurrence at D* = ⌈N₀/n⌉√λ. That is used in §5.2.

## 5. Verdict, regimes and the one positive by-product

### 5.1 Ranges (shape, e = 1/√log₂ n; `satw_exponent.py` X5)

| design | exponent / n | largest k with exponent < n | growth of k_max |
|---|---|---|---|
| now (Calabro Δ, Thm D) | e·28k·log(96Δ log 2Δ), log Δ ≈ k log(k/e) | log₂ n = 10⁸ → 4; 10¹⁶ → 257; 10³² → 1.8·10⁶ | ≈ (log n)^{1/4}/√(log log n) (measured 0.242) |
| density 2^k(k/ε)³ (open) | ≈ e k (k + 3 log(k/e)) | 10¹⁶ → 1826; 10³² → 1.9·10⁷ | (log n)^{1/4} (0.250) |
| density (k/ε)³ (**impossible** for k ≳ 3 log log n, Thm S) | ≈ 3 e k log(k/e) | 10¹⁶ → 26016; 10³² → 1.2·10¹² | √log n/log log n (0.483) |

Exhaustive-type #k-SAT bounds of the form 2^{n(1−c/k)} are beaten exactly when the exponent per n is < 1 − c/k.
Up to constants this is the same range as "subexponential", so the k-range column is the comparison.

### 5.2 By-product: one factor of k for formulas of bounded density (proved by inspection; not Lean-checked)

**Corollary 5.1.** There is an absolute constant C such that #k-SAT on formulas with m ≤ d·n clauses, for
3 ≤ k ≤ (log n)^{1/4} and 2 ≤ d ≤ n^{1/(41C₀)}, takes time

  2^{C (k n log(2d) + n)/√log n}.

*Proof sketch.*
1. Branch on all variables occurring in more than D* = ⌈k d⌉⌈√log₂ n⌉ clauses. There are ≤ k m/D* ≤ n/√log n of them,
   so this costs 2^{n/√log n} branches. Each branch is a k-CNF on ≤ n variables with ≤ m clauses and maximum
   occurrence ≤ D* ≤ n^{1/(40C₀)}.
2. Run Steps 1–4 without Step 5 (no sparsification).
   * By Prop. 1.1, U ≤ 6k(n + log 2d) + 28kn log(96 d log 2d) + 2g².
   * The parameters (69) use Δ_occ = D*, so gP/K = o(en) as in Step 4.
   * So one branch costs 2^{O(e k n log 2d)} with e = Θ((log n)^{−1/2}) (Step 6).
3. Using only the Lean-proved (68) with Δ = D*, the bound is 2^{O(k n (log(2kd) + log log n)/√log n)}.

This has one factor of k. Compare Corollary 11's 2^{Ckm/√log m} (k·d·n) and Theorem D's k²: for m = O(n) it gives
2^{O(kn/√log n)}, which makes OpenAI's 2^{O_{k,D}(n/√log n)} explicit in k and D. ∎

**Why this does not extend.** For a general formula, d is the density after sparsification. By Theorem S, some
output has log d ≥ (1−ε)k − O(log k + log log n). By Theorem K, the clause-mark design pays k·n·log d on that output.
The exponent stays Θ(k² e n) for k ≥ C log log n.

### 5.3 Proved vs open

* **Proved here** (with numerical checks):
  * Lemmas A, B, D(i)–(iv), C (n̄-implication) and E;
  * Theorem K inside the model of §2.1;
  * the identity of §2.4;
  * Theorem S;
  * Prop. 1.1 and Cor. 5.1, by inspection of the paper's inequalities. The Lean `Setting` needs a two-parameter Δ;
    this is not formalized.
* **Corrected from the plan:**
  * The hitting bound "I ≥ m − 2^k n̄" is false (counterexample in §2.2). Only the n̄-implication form holds.
  * OpenAI's tests are not variable-based; their arity-2 incidences carry the k as monomial degree.
  * U depends on the density m/n, not on the maximum occurrence Δ.
* **Open:**
  1. A disjoint sparsifier with density 2^{O(k)}·poly(1/ε). It would give exponent O(k² e n + k e n log(1/e)).
  2. A structure-aware kill whose checks are much smaller than m/n̄ (excluded neither by Lemma C nor by Theorem S).
  3. A network outside the clause-mark/monomial paradigm in which a violated clause costs o(k) shared incidences.
     Both engines (Anthropic's netD, OpenAI's bipartite contraction) pay k per violated clause.

## 6. Scripts (all `python3 -I`, all PASS)

| script | checks |
|---|---|
| `satw_exponent.py` / `.out` | X1 Lean `occBound` ≤ printed bound, log Δ/(k log k/ε); X2 OpenAI's B (Θ(k²) in log); X3 the paper's 2.1·10⁻⁴ / ℓ ≥ 23 / log n > 8.5·10⁹ remark; X4 same with poly density; X5 k-ranges and growth exponents |
| `satw_newton.py` / `.out` | N1 σ_i expansion; N2 Lemma 12 and tightness of M′ = ν−1+r; N3 p-adic valuations, bits per mark; N4 parity is the unique fastest check function |
| `satw_pi0_fail.py` / `.out` | §2.4 identity, nonzero witnesses, correct expansion (65) |
| `satw_cover.py` / `.out` | C1 Lemma 13 family vs the averaging bound; C2 n̄-implication after the Step-2 greedy, (63), and the counterexample to the naive hitting bound; C3 rank of equality matrices |
| `satw_sparsity_lb.py` / `.out` | Theorem S: Shearer hit bound, Monte Carlo, closed-form D*, crossover with poly(k/ε) |
