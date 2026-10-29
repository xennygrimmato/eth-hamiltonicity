# The parity barrier in OpenAI's Engine I: exact constraints, a lower bound for every M₀, and what is left open

Status tags: **[P]** proved here (full proof in this file), **[N]** checked numerically/exactly by a script in
`scripts/parity_*.py`, **[C]** conjecture/heuristic, **[K]** known result (cited).

Sources (read only): OpenAI preprint `main_full_version.tex` (ETH family 378): overview §2.6
(l.1022–1428), Definition `def:layout` (l.1714), Lemma `lem:measurement-separation` (l.1781),
Prop. `prop:general-count` and eq. `three-costs` (l.2013–2060), §4 `sec:construction` (l.2073–2845,
in particular eq. `matrix-support-target` l.2164, Lemmas `lem:swaps-matrix`, `lem:swaps-support`,
`lem:swaps-forms`). Lean: `OAI/Algorithms/SubexponentialSAT/LayoutSpec.lean` (structure `Layout`),
`MatrixSupport.lean` (`matrixEntry_support`), `SpectralRank.lean` (`jointMatrix_rank_bound`).

## 0. Verdict (first)

1. **The template is closed.** Every instantiation of OpenAI's M₀-template — *any* matrix M₀
   (commuting with the swaps or not), *any* label set (full ([r]×[r])^Q, a code, a sparse set of occupied
   labels, h copies or one big coordinate set), *any* number Q of points — obeys
   **R ≥ c·Q/√(log n)** on suitable bounded-occurrence inputs, unless the measurements are a constant
   fraction of all occurrences (Theorem 2, via a triangular-submatrix rank bound + the
   Arora–Rao–Vazirani structure theorem). With the paper's full label space it also obeys
   **ε ≥ Pr[Bin(2Q,½) ≥ Q+R]**, i.e. R ≥ (1−o(1))√(Q ln(1/ε)) (Theorem 1/Cor. 1.1), which matches the
   paper's window construction R ≈ √(2Q ln(1/ε)) up to a factor ≤ √2. So the Taylor cost
   (R/Q)log(Q/R) is ≥ Ω(log log n/√log n) and **Engine I in its own template cannot beat
   2^{Θ̃(n/√log n)}**; neither non-commuting M₀ nor structured labels help. [P]
2. **The coordinator's quantum-code hunch is right in shape, but no code theory is needed.** The clean
   problem is min rank(SWAP_{a,d} − N) over N of "a-weight" < R with the d-register free (§1.4); the
   X^{⊗Q} version is a sibling with the same answer. The lower bound is an elementary
   fooling-set/triangular argument (it reproves the exact-agreement degree bound for parity); the
   relevant subspaces have dimension (1−ε)·2^{2Q} and distance 1, far outside the regime of
   Bravyi–Poulin–Terhal-type rate/distance tradeoffs.
3. **What is still open** is only the *general interface* (Definition `def:layout`), which is strictly
   weaker as a constraint than the template: there the measurement part may vary with t in a
   non-polynomial way. §5 gives an exact dual characterisation, shows the template is precisely the
   special case "measurement part polynomial in T", and proves the general interface is genuinely
   stronger (Prop. 5.1, "runs instead of windows": e.g. ε = 0.1 at R = 9 for all Q ≤ 4096, where every
   M₀ needs R ≥ 59 at Q = 4096). But in the regime the engine needs (ε ≲ 1/(rbQ), forced by the
   ℓ₁-height of measurement rows) this gain is a constant factor in R. No construction found beats √Q;
   no lower bound is known for the general interface (§7 states the problem).

(Sections below: 1 constraints; 2 Theorem 1; 3 Theorem 2; 4 quantum-code view; 5 general interface;
6 numerics; 7 consequences.)

## 1. The exact constraints

### 1.1 The interface the counting routine actually needs (Definition `def:layout`, l.1714)

Data, for factor scopes (I_f) on variables [n], integers r ≥ 2, D ≥ 1, 1 ≤ R < Q, 0 < τ ≤ ½:

* (L1) for each t ∈ [Q] a partition [n] = S_{t,1} ⊔ … ⊔ S_{t,r}, |S_{t,g}| ≤ 2n/r;
* (L2) for each factor f a schedule σ_f ∈ [r]^Q (group of f at point t);
* (L3) for each (t,g) an **integer** matrix C_{t,g} with columns S_{t,g}, every row of ℓ₁-norm ≤ D,
  Σ_g c_{t,g} ≤ 2τn rows at each t (the matrices may depend on t);
* (L4) for each occurrence (f,v), v ∈ I_f, a row P_{f,v}(T) ∈ ℚ[T]^{1×n} with **P_{f,v}(0) = δ_v**,
  **deg P_{f,v} ≤ R**, and for every t and every g ≠ σ_f(t):
  ξ ∈ ℚ^{S_{t,g}}, C_{t,g}ξ = 0 ⇒ ⟨P_{f,v}(t), ξ̃⟩ = 0
  (equivalently P_{f,v}(t)|_{S_{t,g}} ∈ rowspace(C_{t,g}) for all g ≠ σ_f(t));
* (L5) bit sizes (denominator (R−1)!Q!).

Cost (Prop. `prop:general-count`, eq. `three-costs`): with total X-degree d = O(n),

  log₂ time ≈ n·[ (R/Q)·log(2Q/R) + τ·log(2D+1) + 2/r ] (up to constants),

the three terms being Taylor data (jets of order q = ⌊d·R/Q⌋ at each point, Σ_{j≤q}2^j C(n,j)
restricted sums), measurement tuples ((2D+1)^{2τn}), and one group (2^{2n/r}).
Note the ℓ₁ bound in (L3) is essential: a rank bound alone is useless (the row (1,2,4,…) separates all
2^n inputs, paper l.1766), so "few measurements" means few rows *of small height*.

The Lean `LayoutSpec.Layout` is the same interface over ZMod p with r = 2 (`support t g`, Bool groups),
Q = p^h − 1 nodes (all nonzero elements of 𝔽_{p^h}), subspaces `K t g` supported in group g with
dim ≥ |V|/4, and `annihilation`: the row at node t kills K t (color e t). The swap matrix is
built per point t on "joint fibres" (`MatrixSupport.matrixEntry`, `jointMatrix`) and its far-support
property is `matrixEntry_support`; the rank defect is the binomial tail (`jointMatrix_rank_bound`).
It is the same template as §1.2 (complementing-swap convention: "agreements ≤ R" there = "mismatches
≤ R−1" here).

### 1.2 The M₀-template (§4 of the paper; how every published instantiation meets (L4))

Auxiliary coordinates B with two schedule maps u ↦ a_u, d_u ∈ [r]^Q (paper: B = ([r]×[r])^Q,
D = |B| = r^{2Q}; an occurrence (f,v) is placed at a coordinate labelled (a_v, σ_f) in one of h copies).
Put **E_{u,w} = {t : a_w(t) ≠ d_u(t)}** ("points at which reading coordinate w from row u leaves u's
group"). The template asks for M₀ ∈ ℚ^{B×B} and an integer matrix C with

* (T1) **M₀ξ = ξ for all ξ ∈ ker C**, i.e. every row of I − M₀ lies in rowspace(C); hence
  #rows(C) ≥ rank(I − M₀), and conversely rank(I − M₀) rows suffice *provided* rowspace(I − M₀) has a
  basis of small ℓ₁-height (the paper uses ±1 product eigenvectors, height D);
* (T2) **support: M₀[u,w] ≠ 0 ⇒ |E_{u,w}| ≤ R − 1** (eq. `matrix-support-target`).

Then P_u(T) = δ_u(I−M₀) + Σ_w M₀[u,w]·φ_{u,w}(T)δ_w with φ_{u,w} = Π_{s∈E_{u,w}}(1 − T/s) satisfies
(L4) with deg ≤ R−1 (Lemma `lem:swaps-forms`), after splitting each row of C by groups (r·c rows per
point). The measurement budget is c ≈ ε·|B| with ε = τ/(r·b) (b = max occurrence).

**Why M₀ = I is not allowed.** (T2) applies to the diagonal: M₀[u,u] ≠ 0 needs d_H(a_u, d_u) ≤ R−1.
For a typical label d_H(a_u,d_u) ≈ (1−1/r)Q ≫ R, so M₀ must vanish on almost the whole diagonal;
the identity is far from the allowed support. (The "killing" polynomial φ_{u,u} would need degree
|E_{u,u}| ≈ Q.)

**Is M₀ restricted to polynomials in commuting operators?** No. (T1)+(T2) are all that is used;
M₀ = V₀ f(W₀) (V₀ = ΠΠ_s, W₀ = ½Σ(I−Π_s)) is the paper's choice. In the swap eigenbasis
M₀ = V₀ g(Π₁,…,Π_Q) acts by χ(σ)g(σ) (χ = parity), so rank(I − M₀) = D·μ_p{g ≠ χ} with
p = (r−1)/(2r): within the commutative algebra the problem is the exact-agreement degree of parity
under the p-biased measure. The theorems below hold for **all** M₀ satisfying (T2).

### 1.3 The clean matrix problem

Define, for a coordinate set B with schedules (a,d), the allowed support
S_R = {(u,w) : d_H(d_u, a_w) ≤ R−1} and

  **ρ_R(B) = min { rank(I − M) : M ∈ ℚ^{B×B}, supp M ⊆ S_R }.**

The template works with budget c iff ρ_R(B) ≤ c (up to the height condition in (T1)). Equivalently,
with V₀ the full swap (V₀ maps u = (a,d) to (d,a)) and N = V₀M:

  ρ_R = min rank(V₀ − N) over N with N[u,w] ≠ 0 ⇒ d_H(a_u, a_w) ≤ R−1,

because d_{V₀u} = a_u. So on B = ([r]^Q)_a × ([r]^Q)_d = H_a ⊗ H_d, **V₀ = SWAP_{a,d} and N ranges over
A_{<R} ⊗ End(H_d)**, A_{<R} = matrices on [r]^Q with entries only between strings at Hamming distance
< R ("a-weight < R"), the d-register unconstrained.

### 1.4 Relation to the coordinator's formulation

"Is there a subspace C of codimension ≤ εD on which V agrees with some low-weight M": yes, exactly —
take C = ker(V₀ − N); codim C = rank(V₀ − N). Two differences from the X^{⊗Q} version: the global
operator is the register swap (it has a-weight d_H(a,d) ≈ (1−1/r)Q on a typical basis state, the
analogue of X^{⊗Q}'s weight Q), and a free ancilla register (d) is available. Both versions have the
same answer (§2, §4).

## 2. Theorem 1: a triangular rank bound valid for every M₀

**Theorem 1 [P].** Let B be any finite coordinate set with schedules a, d : B → [r]^Q and let M satisfy
(T2). For every function φ : [r]^Q → ℝ that is 1-Lipschitz for the Hamming metric,

  rank(I − M) ≥ #{u ∈ B : φ(d_u) − φ(a_u) ≥ R}.

*Proof.* Let U be the set on the right, ordered u₁, u₂, … by non-increasing φ(a_u). For i ≤ j,
φ(d_{u_i}) − φ(a_{u_j}) ≥ φ(d_{u_i}) − φ(a_{u_i}) ≥ R, hence d_H(d_{u_i}, a_{u_j}) ≥ R and
M[u_i,u_j] = 0 by (T2). So (I − M)[U,U] is lower triangular with unit diagonal. ∎

Special case (independent sets): if d_H(A,B') ≥ R then rank(I − M) ≥ #{u : d_u ∈ A, a_u ∈ B'}
((I − M)[U,U] = I_U). Theorem 1 never uses commutativity, the swap structure, or the shape of B; it
uses only that the *target* I is diagonal and the support is "d of the row close to a of the column".

**Corollary 1.1 (OpenAI's full label space) [P].** For B = ([r]×[r])^Q (r even) with every label used
equally often, ρ_R(B)/D ≥ Pr[Bin(2Q,½) ≥ Q + R]. Hence ε ≥ Pr[Bin(2Q,½) ≥ Q+R] = e^{−(1+o(1))R²/Q},
i.e. **R ≥ (1−o(1))·√(Q ln(1/ε))** whenever ln(1/ε) ≫ ln Q. (r odd: same with Bin replaced by a sum of
Bern(q) − Bern(q), q = ⌊r/2⌋/r.)

*Proof.* φ(x) = Σ_t χ(x_t), χ = indicator of a fixed half of [r]; a_u, d_u are independent uniform,
so φ(d_u) − φ(a_u) has the law of Bin(2Q,½) − Q. ∎

The paper's window gives ε_up = Pr[Bin(Q,p) ∉ I] ≈ 2Φ̄(R/(2√(Qp(1−p)))), p = (r−1)/2r, i.e.
R ≈ √(8p(1−p)·Q·ln(2/ε)) → √(2Q ln(2/ε)) for large r. **Lower and upper bounds differ by a factor
≤ √2 in R** (and by ≈ √(4/3) ≈ 1.15 for r = 2, where p = ¼). Whether non-commuting M₀ can close this
constant gap is the only freedom left inside the full-label template (§6 tests it for tiny Q).
Since D = r^{2Q} ≤ poly(n) forces Q ≤ O(log n/log r), Cor. 1.1 already shows the paper's
parameters are optimal for its label space: R/Q ≥ √(ln(1/ε)·2log r/log n)·(1−o(1)).

## 3. Theorem 2: structured or sparse labels and Q ≫ log n do not help either

The scout's hope (a1) had two escape routes left after Cor. 1.1: (i) a label set that is a code /
a sparse set of occupied labels in a much larger [r]^{2Q}, so that Q is no longer tied to log n;
(ii) a non-uniform occupation. Theorem 1 handles both once we can find a good φ, and the
Arora–Rao–Vazirani structure theorem supplies it.

**Definition.** A formula (variables [n], clauses 𝓕) is (γ,κ)-*linked* if for every two disjoint sets
A₀, B₀ ⊆ [n] with |A₀|,|B₀| ≥ γn, at least κn clauses contain a variable of A₀ and a variable of B₀.
(Random b-regular 3-CNF is (γ, γ²b/2)-linked w.h.p. once b ≥ C/γ⁴: the expected number of such
clauses is ≈ 2bγ²n, Azuma in the configuration model gives deviation probability e^{−Ω(bγ⁴n)}, and a
union bound over ≤ 3ⁿ pairs closes. These are bounded-occurrence inputs of Engine I.)

**[K] ARV structure theorem** (Arora–Rao–Vazirani, JACM 2009; form of Arora–Lee–Sachdeva,
arXiv:1102.1456, Thm 1.2). For every c > 0 there are c′, b > 0: if z₁,…,z_n are unit vectors with
‖z_i − z_j‖² + ‖z_j − z_k‖² ≥ ‖z_i − z_k‖² and average ‖z_i − z_j‖² ≥ c, there are S, T with
|S|,|T| ≥ c′n and ‖z_i − z_j‖² ≥ b/√(log n) for all i ∈ S, j ∈ T.

**Theorem 2 [P, modulo ARV].** Let r ≥ 3. Fix any Q, any variable schedules a_v ∈ [r]^Q obeying the
group bound (L1) (|{v : a_v(t) = g}| ≤ 2n/r), any factor schedules σ_f, any coordinate layout
(each occurrence (f,v) is a coordinate with labels (a_v, σ_f); copies, codes, sparse occupation all
allowed) and any M satisfying (T2). If the formula is (c′,κ)-linked, with c′,b the ARV constants for
c = 2(1 − 2/r) ≥ 2/3, then

  R ≤ b·Q/(8√(log n))  ⟹  rank(I − M) ≥ κn/2.

*Proof.* z_v := (Q^{−1/2}·1[a_v(t) = g])_{(t,g)} are unit vectors with ‖z_v − z_w‖² = 2d_H(a_v,a_w)/Q, an
ℓ₁ (hence ℓ₂²) metric, and by (L1) Pr_{v,w}[a_v(t) = a_w(t)] ≤ 2/r, so the average squared distance is
≥ 2(1 − 2/r). ARV gives A₀, B₀ ⊆ [n], |A₀|,|B₀| ≥ c′n, with d_H(a_v,a_w) ≥ Δ := bQ/(2√log n) for
v ∈ A₀, w ∈ B₀. Put φ(x) = d_H(x, a(A₀)) (1-Lipschitz). Take any of the ≥ κn clauses f containing
v ∈ A₀ and w ∈ B₀. If φ(σ_f) ≥ Δ/2, the occurrence (f,v) has φ(d) − φ(a) = φ(σ_f) ≥ Δ/2; otherwise
(f,w) has (−φ)(d) − (−φ)(a) = φ(a_w) − φ(σ_f) > Δ/2. So for ψ = φ or ψ = −φ at least κn/2
occurrences have ψ(d) − ψ(a) ≥ Δ/2 ≥ R, and Theorem 1 applies. ∎

**Consequence.** The template needs at least rank(I − M) ≤ #rows(C) ≤ 2τn measurements per point,
and τ → 0 is necessary for a subexponential bound ((2D+1)^{2τn} ≥ 3^{2τn}). So for large n
R > bQ/(8√log n), the jets have order q = ⌊dR/Q⌋ ≥ Ω(n/√log n), and the Taylor cost
Σ_{j≤q} 2^j C(n,j) ≥ C(n,q) = 2^{Ω(n·log log n/√log n)}. **Every instantiation of the M₀-template, for any
Q, r, label structure and any (non-commuting) M₀, costs 2^{Ω(n log log n/√log n)} on linked
bounded-occurrence formulas.** OpenAI's sharp bound for m ≤ Dn is 2^{O(n/√log n)} via the appendix
(Engine II), so within Engine I the main-text template is tight up to a log log n factor. [P]

Remarks. (1) Theorem 2 uses only constant ε; combined with Cor. 1.1 the full-label template has
R ≥ max(cQ/√log n, √(Q ln 1/ε)). (2) The proof is the "Hamming metrics have observable diameter
≳ 1/√log N" phenomenon: an N-point configuration with balanced coordinates cannot be more
concentrated than the cube on log N coordinates (the repeated cube shows ARV is tight here). (3) The
argument needs the linked structure only to turn ARV's well-separated *variable* sets into many
stretched *occurrences*; it is where the formula's expansion enters (for a formula whose incidence
graph is a disjoint union of tiny pieces, M₀ = I on a schedule with σ_f = a_v works with no
measurements — no lower bound can hold for all formulas).

## 4. The quantum-code reading (coordinator's hunch)

* **Equivalence.** ρ_R = min codim of a subspace C ⊆ H_a ⊗ H_d on which SWAP_{a,d} agrees with an
  operator of a-weight < R (§1.3). For the single-register version V = X^{⊗Q}, M of weight < R:
  rank(X^{⊗Q} − M) = rank(I − X^{⊗Q}M), and X^{⊗Q}M is supported on pairs at distance > Q − R, so
  Theorem 1's argument (U any set of diameter ≤ Q − R, all of whose entries are forced) gives
  **codim ≥ |Ball(Q, ⌊(Q−R)/2⌋)|**, i.e. ε ≥ Pr[Bin(Q,½) ≤ (Q−R)/2] (Kleitman's diameter theorem
  makes the ball the best such U). The commutative construction (g(X₁..X_Q) interpolating parity on R
  middle layers) gives two tails, so for X^{⊗Q} the answer is **Θ(√(Q log 1/ε)) with matching
  exponents** (lower = one tail, upper = two tails). As a by-product: *every real polynomial of degree
  d < Q disagrees with parity on at least a Pr[Bin(Q,½) ≤ (Q−d−1)/2] fraction of the cube*, the
  classical exact-agreement bound (agreement ≤ ½ + O(d/√Q)), now for every operator of weight ≤ d, not
  only diagonal ones.
* **Why code theory does not enter.** The subspaces in question have dimension (1−ε)·2^{2Q}, i.e.
  "rate" 1 − O(ε/Q) and distance 1; Bravyi–Poulin–Terhal / Bravyi–König bounds concern codes with
  growing distance under locality and say nothing here. The relevant phenomenon is concentration of
  measure on the Hamming cube (§2) and, for sparse label sets, its N-point version (ARV, §3). No
  "low-weight logical in a high-rate code" can beat the bound, because the bound is proved for all
  operators of the right support, unitary or not, and all subspaces.

## 5. The general interface is strictly stronger than the template — but not where it matters

### 5.1 Reduction: template = general interface with a T-polynomial measurement part [P]

Fix a shared measurement space Λ = rowspace(C) on the coordinates B (as in the paper; (L3) also
allows Λ_t to depend on t). Write a row as P(T) = e_u + Σ_{k=1}^{R−1}T^kP_k. Condition (L4) at t says
P(t) = λ_t + s_t, λ_t ∈ Λ, s_t supported on S_t(u) = {w : a_w(t) = d_u(t)}. Coordinatewise:

  **row u is feasible ⟺ ∃ λ₁,…,λ_Q ∈ Λ such that for every w with |E_{u,w}| ≥ R the data
  {(0, δ_{uw})} ∪ {(t, (λ_t)_w) : t ∈ E_{u,w}} is interpolated by a polynomial of degree ≤ R−1.**

(Given such λ_t, let P_w be that interpolant; for |E_{u,w}| ≤ R−1 take P_w = δ_{uw}φ_{u,w}-type
interpolants.) If one insists λ_t = λ(t) for a polynomial λ ∈ Λ[T] of degree ≤ R−1, then for every w
with |E_{u,w}| ≥ R the interpolant is forced to be λ_w(T), so λ_w(0) = δ_{uw}: this is exactly
(T1)+(T2) with M₀ row e_u − λ(0). **So the M₀-template is the general interface with the
measurement part polynomial in T; the general interface lets λ_t vary arbitrarily with t.**
Dually, row u is infeasible iff there are ξ_t ∈ Λ^⊥ supported on {w : a_w(t) ≠ d_u(t)} with
Σ_t t^kξ_t = 0 (1 ≤ k ≤ R−1) and Σ_t (ξ_t)_u ≠ 0 (Farkas for linear equations). Theorem 1's
certificate is the special case ξ_t = μ_t·ξ with a single ξ; for the general interface one only gets
the weak bound ε ≥ ((1−1/r)/r)^R/(R) from it, which leaves room.

### 5.2 Gap construction: runs instead of windows [P]

Let J ⊆ {0,…,Q} be a set of eigen-levels, J = J₁ ⊔ … ⊔ J_m its maximal runs of consecutive integers,
Λ = span{ψ : j(ψ) ∉ J} (product swap eigenvectors, as in Lemma `lem:swaps-matrix`), Π_k the
spectral projector of W₀ onto the levels J_k, Π_Λ = I − ΣΠ_k.

**Proposition 5.1.** If every run has |J_k| ≤ R, then the rows
  P_u(T) = δ_uΠ_Λ + Σ_k P^{(k)}_u(T)·Π_k,
where P^{(k)}_u is the paper's row (eq. `swaps-row`) for M_k = V₀f_{J_k}(W₀), satisfy (L4) with degree
≤ R−1 and the shared measurement space Λ. Hence ε = Pr[Bin(Q,p) ∉ J] is achievable at degree R−1
for *any* union of runs of length ≤ R, whereas the template (any M₀) needs one polynomial
interpolating (−1)^j on all of J.

*Proof.* At T = 0 the rows equal δ_u(Π_Λ + ΣΠ_k) = δ_u. Degree ≤ R−1 since deg f_{J_k} ≤ R−1. At t,
P^{(k)}_u(t) = λ_k + s_k with λ_k ∈ rowspace(I − M_k) ⊆ span{levels ∉ J_k}, so λ_kΠ_k = 0, and s_k
supported on S_t(u). It remains to show xΠ_k ∈ Λ + Q^{S_t(u)} for x supported on S_t(u). Split position t
off: W₀ = W′ + ½(I − Π_t) with W′ acting on the other positions, so Π_k = P_sym ⊗ 1_{J_k}(W′) +
P_anti ⊗ 1_{J_k−1}(W′) (P_sym/P_anti the local ±1 eigenprojectors of the swap at t). Let g = d_u(t).
For x = e_{gg}⊗y: e_{gg} is symmetric, xΠ_k = e_{gg}⊗1_{J_k}(W′)y ∈ Q^{S_t(u)}. For x = e_{gh}⊗y (h ≠ g),
with s = e_{gh}+e_{hg}, a = e_{gh}−e_{hg}: xΠ_k = e_{gh}⊗½(A+B)y + e_{hg}⊗½(A−B)y, A = 1_{J_k}(W′),
B = 1_{J_k−1}(W′). For J_k = [α,β], A − B = 1_{β}(W′) − 1_{α−1}(W′). Now e_{hg}⊗z_β = e_{gh}⊗z_β − a⊗z_β with
a⊗z_β of level β+1 ∉ J (maximal run) or zero (β = Q), hence in Λ; and e_{hg}⊗z_{α−1} = s⊗z_{α−1} − e_{gh}⊗z_{α−1}
with s⊗z_{α−1} of level α−1 ∉ J (or zero if α = 0), hence in Λ. Both remainders e_{gh}⊗(·) lie in
Q^{S_t(u)}. Group splitting for r > 2 is automatic because the correction lies in Λ. ∎

The correction terms (−a⊗z_β, s⊗z_{α−1}) depend on t: this is exactly the freedom of §5.1 that the
template lacks.

**Exact check [N]** (`parity_general_interface.py`, `parity_general_runs.py`, r = 2, all level sets J
for Q ≤ 4, all with ε ≤ 0.3 for Q = 5, three for Q = 6; feasibility decided by exact rank over two
primes): the least degree+1 in the general interface equals the **longest run of J** in 72/72 cases
(so Prop. 5.1 is also sharp for these spaces), versus interp-degree+1 for the template with the same
Λ; the general interface needs strictly smaller R in 25 of them (e.g. Q = 6, J = {0,1,2,3,5,6}:
template R = 6, general R = 4, ε = 0.033).

### 5.3 What the gap construction buys

With gaps of one level every R+1 levels (`parity_gap_rule.py`), ε_gap ≈ Σ_{gaps}Pr[Bin(Q,p) = j]:

* for ε ≳ 1/√Q the gaps sit inside the bulk and **ε_gap ≈ 1/(R+1) independently of Q**: e.g.
  p = ¼, ε = 0.1: R_gap = 9 for Q = 256…4096 while *every* M₀ needs R ≥ 15, 30, 59 (Cor. 1.1).
  So **the general interface strictly beats the template's lower bound** — Theorem 1 is a theorem
  about the template, not about Definition `def:layout`. [P, exact binomial sums]
* for ε ≪ 1/√Q only the two gaps next to the window matter, ε_gap ≈ 2·pmf(Qp ± R/2) instead of the
  two tails, a gain of a factor ≈ R/σ² ≈ √(log(1/ε)/Q) in ε, i.e. R² drops from 8σ²ln(1/ε) to
  8σ²ln(1/(εσ)): **only a constant factor in R once ln(1/ε) ≳ ln Q**.

**The engine needs the second regime.** The measurement rows are eigenvectors of ℓ₁-height up to 2^Q
(r^{2Q} in the paper's bound), so the cost term τ·log(2D+1) ≈ εrb·Q·log r forces ε ≲ 1/(rbQ) ≪ 1/√Q.
Even with hypothetical height-poly(Q) rows (ε ≈ η/(rb log Q)), the bulk-gap regime gives R ≈ 1/ε ≈ r²b,
and balancing (R/Q)log(Q/R) against 2/r with Q ≈ log n/log r gives rate (log n)^{−1/3}: *worse* than
the window. Hence **no eigen-level measurement space, in either interface, beats 2^{Θ̃(n/√log n)}** [P for
the constructions; the exact admissibility rule for eigen-level spaces is proved in one direction
(Prop. 5.1) and verified exactly in the other for Q ≤ 6].
Direct check of Prop. 5.1 [N]: `parity_gap_construction_check.py` builds the rows explicitly
(Q = 4, J = {0,1,2,4}, R = 3; Q = 4, J = {0,1,3,4}, R = 2; Q = 5, J = {0,1,2,4,5}, R = 3) and verifies
P_u(0) = δ_u and, at every point and row, that the out-of-group part lies in Λ (residual ≤ 6·10⁻¹⁵).

## 6. Numerics (r = 2, exact unless stated)

Scripts in `scripts/`, outputs alongside (`.out`).

* `parity_template_bounds.py` — full label space, ε = fraction measured, p = ¼:
  LB (Cor. 1.1, every M₀) vs WIN (paper) vs SYM (best symmetric g, all level sets, exact) vs GEN (best
  multilinear g, exhaustive over agreement sets, Q ≤ 4). Sample (ε):

  | Q | R | LB (all M₀) | WIN | SYM | GEN |
  |---|---|---|---|---|---|
  | 3 | 2 | 0.109 | 0.156 | 0.156 | 0.156 |
  | 4 | 2 | 0.145 | 0.262 | 0.262 | 0.227 |
  | 4 | 3 | 0.035 | 0.051 | 0.051 | 0.051 |
  | 8 | 5 | 0.0106 | 0.0273 | 0.0273 | – |
  | 12 | 7 | 0.0033 | 0.0143 | 0.0143 | – |

  For R ≥ 3 the best symmetric g is always the window; non-symmetric commutative g helps only at tiny
  R (Q = 4, R = 2). R needed at fixed ε (Part B): R_LB/√(Q ln(1/ε)) → 0.61…0.87 and
  R_win(r→∞)/√(Q ln(1/ε)) → 1.09…1.29 for Q up to 4096; ratio R_win/R_LB ≈ 1.5 (→ √2 as ε → 0).
  **The curves R(Q) at fixed ε are √Q for both; there is no Q-dependence beyond √Q to exploit.**
* `parity_exact_minrank.py` — exact ρ_R for Q = 2, 3 (D = 16, 64): the max triangular set (exact ILP
  with lazy cycle cuts) vs the commutative optimum, plus an alternating-least-squares search for
  smaller-rank non-commutative completions:

  | Q,R | potential LB | max-triangular LB | commutative opt | non-commutative found |
  |---|---|---|---|---|
  | 2,1 | 5 | 6 | 6 | – (= LB) |
  | 2,2 | 1 | 1 | 1 | – |
  | 3,1 | 22 | 28 | 28 | – |
  | 3,2 | 7 | 8 | 10 | **8** |
  | 3,3 | 1 | 1 | 1 | – |

  So ρ_R is determined exactly in all five cases (lower bound attained), and at (Q,R) = (3,2) a
  **non-commuting M₀ beats every commutative one (rank 8 vs 10)** [N: float, forced-entry residual
  2.6·10⁻¹⁵, singular values …5.25, 1.4·10⁻¹⁵ at the rank cut; ‖[M,Π_s]‖ ≈ 24–39, so M is far from the
  swap algebra; `parity_noncomm_certify.py`]. This is the constant-factor slack between Cor. 1.1 and
  the window, realised; it cannot change the √Q scaling (Theorems 1–2).
* `parity_general_interface.py`, `parity_general_runs.py` — §5.2 (72 level sets, exact over two primes).
* `parity_gap_rule.py` — §5.3 (R needed by LB / window / gap rule at fixed ε, Q ≤ 4096).

## 7. Consequences and the precise open statement

**What is settled.**
1. Coordinator's question, as posed (min rank(V − M) over M supported on S_R): **R = Θ(√(Q log 1/ε))
   for the full label space, constants within √2**, for every M, commuting or not (Thm 1, Cor. 1.1);
   and R ≥ cQ/√log n for every label structure and every Q on linked inputs (Thm 2). The rate of the
   M₀-template is therefore tight at 2^{Θ̃(n/√log n)}; a sharpening to n/(log n)^{1/2+δ} is impossible
   inside it.
2. The barrier is *not* "commutativity": non-commuting M₀ exist that beat the commutative optimum
   (§6), but only by constants. It is concentration of measure for Hamming configurations
   (cube isoperimetry for B = ([r]²)^Q, ARV for arbitrary N-point label sets).

**What is open (precisely).** Definition `def:layout` itself. In the auxiliary-coordinate form:

> Given schedules a, d : B → [r]^Q with balanced a-coordinates, points 1..Q, and measurement spaces
> Λ_t ⊆ ℚ^B (t ∈ [Q]) spanned by integer rows of ℓ₁-height ≤ H, find rows P_u(T) ∈ ℚ[T]^B with
> P_u(0) = δ_u, deg P_u ≤ R−1, and P_u(t) − λ_{u,t} supported on {w : a_w(t) = d_u(t)} for some
> λ_{u,t} ∈ Λ_t. Minimise max_t dim Λ_t/|B| =: ε. **Is R ≥ c√(Q·log(1/ε)) (or R ≥ cQ/√log|B|) forced when
> ε·log H ≤ 1/(r·b)?**

Known about it: (i) the template is the sub-case λ_{u,t} = λ_u(t) polynomial (§5.1); (ii) the dual
certificate characterisation (§5.1); (iii) the general interface really is stronger — Prop. 5.1
achieves ε ≈ 1/(R+1) at R independent of Q, below the template bound — but in the regime forced by
measurement heights (ε ≲ 1/(rbQ) for eigenvector rows) the gain is a constant factor in R;
(iv) a lower bound in this regime would need an argument that couples the t-dependent corrections
across points; the single-certificate (Lagrange on R points) argument only gives ε ≥ (cst/r)^R. A
route beyond √log n would need, simultaneously, measurement rows of height 2^{o(Q)} spanning a space
of codimension ≥ (1 − 1/(r b log H))|B| *and* t-dependent corrections that exploit it — nothing in the
eigen-level family does this (§5.3).

**Recommendation.** Stop pursuing (a1) as "find a better M₀": it is closed. The only live variant is
the general interface with low-height, t-dependent measurements, and every structure tried (window,
symmetric/non-symmetric commutative, non-commutative M₀, runs-with-gaps, codes/sparse labels via
Theorem 2) is capped at √Q or worse. Expected payoff: low.

## References

* S. Arora, S. Rao, U. Vazirani, Expander flows, geometric embeddings and graph partitioning, JACM 56 (2009).
* S. Arora, J. R. Lee, S. Sachdeva, A reformulation of the Arora–Rao–Vazirani structure theorem,
  [arXiv:1102.1456](https://arxiv.org/pdf/1102.1456) (Thm 1.2, the form used in §3).
* Lecture notes on ARV: [arXiv:1607.00854](https://arxiv.org/pdf/1607.00854).
* D. J. Kleitman, On a combinatorial conjecture of Erdős (diameter theorem), JCT 1 (1966) — §4.
