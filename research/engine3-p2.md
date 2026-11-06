# Engine 3, Proposal P2, computed: clause-product designs with t-dependent measurement spaces on small expanders

6 Nov 2026. Research note, no commits. Implements P2 of `engine3-openai-route.md` (§1.1, §2.2, §2.5, P2, O2).
Definitions used: OpenAI `def:layout` (l.1714) and the (r,τ,D)-design of the main text (l.690–721) in
`main_full_version.tex`; Dias–Lima [DL] Def. 5.1 and §9 (arXiv 2611.00517); `permanent/parity-barrier.md` §5.1
(template = general interface with a polynomial measurement part), Thms 1–2.
Scripts: `research/scripts/engine3-p2/` (list in §8). Tags: **[R]** proved here or in a cited source,
**[N]** computed exactly (or exact evaluation of a heuristic search's output), **[C]** heuristic/conjecture.

---------------------------------------------------------------------------------------------------

## 0. Verdict

1. **The encoding is validated.** [N] On OpenAI's auxiliary array B = ([2]^4)², window {0,1,2} (degree 2), the
   paper's explicit rows satisfy our constraint system exactly; our solver, with t-dependent spaces allowed, finds
   the same minimum degree (2) and proves degree 1 infeasible. The same holds for windows {0,1} and {1,2}
   (degree 1), and for the template pushed forward to a real 3-CNF (n = 16). Theorem 1's triangular bound holds:
   9 ≤ rank(I − M₀) = 13 (and 37 ≤ 67, 37 ≤ 94).
2. **In every search, the best design uses singleton rows e_a.** [N + C] We ran 945 annealing runs over
   partitions, assignments and singleton sets (stage 1), and 73 general-row runs that start from them (stage 2)
   with rows of height ≤ 2: pairs e_a + c·e_b, 2e_a ± e_b, group sums, signed and subset sums, and random
   {−2..2} rows. **Stage 2 never beat stage 1 strictly** (0 of 73 runs).
   - **Exhaustive neighbourhoods.** We ran 138,592 exact single-slot tests on 9 designs, putting every {−2..2} row
     into every slot. No non-singleton row ever improved a design. The only improvements, 2 cases, came from
     singleton-for-singleton swaps that lowered Σ R_o but not R_max. At ρ = 1 no non-singleton row ever tied. At
     ρ = 2 the ties with a changed space (48) that we printed are rows e_a + c·e_b with e_a the other row of the
     slot, so they span a pair of singletons. Searches started from random non-singleton rows end at R = 2–3, never below the singleton optimum (2–3),
   with at most one non-singleton row. Dense rows (group sums, signed sums, random dense) give R = 3 at Q = 4 and
   4–5 at Q = 8. That is never better than using no measurements at all (ρ = 0 optimum: 2 at Q = 4, 3–4 at Q = 8). In other words, the measurements that work are DL §9's naive route,
   "measuring the cut variables one by one".
3. **Feasibility in P2's "gain" sense holds at n ≤ 24, but it means nothing.** With ρ = 2, Q = 8 the bound
   R ≤ Q/4 = 2 is met on every instance (R = 0–2). The reason is that r·ρ = 8 singleton rows per point measure
   1/3 to 1/2 of all variables when n ≤ 24. The per-point cost then exceeds 2^n everywhere (e.g. L3, n = 24, Q = 10,
   ρ = 2: log₂ cost/point = 52 against n = 24).
   - **Trend at fixed ρ.** With r = 4, R/Q (and the smoother mean_o R_o/Q) stays flat or grows with n. Example,
     L3 at Q = 8: mean R_o/Q = 0.083 → 0.096 → 0.123 at ρ = 2, and 0.18 → 0.19 → 0.21 at ρ = 1.
   - **Trend at fixed Q/√n.** For n = 16, Q = 4 against n = 24, Q = 5, and for n = 16, Q = 8 against n = 24, Q = 10,
     R/Q does not decrease for ρ ≥ 1. For ρ = 0 it drifts down slightly, from 0.36 to 0.32 for L3.
   - **No decay anywhere.** With groups of fixed size s = 4 (r = n/4, close to the √n-size groups P2 targets),
     everything is flat in n.
4. **The 2×2-minor obstruction generalises, proved.** [R] (Lemma 4.) Take any ρ+1 occurrences with distinct own
   variables. Whenever all of them are foreign at t and their variables lie in one group h with dim R_{t,h} ≤ ρ,
   the (ρ+1)×(ρ+1) own-coefficient minor vanishes at t. This happens at no more than Σ_j R_{o_j} ≤ (ρ+1)R points,
   whatever the heights.
   - **Corollary 5.** On formulas where a constant fraction of variables is foreign at every balanced partition
     (expanders), R ≥ c(r,ρ,b)·Q for **every** design with ≤ ρ rows per group.
   - **For P2's grid (r = 4), decay of R/Q is therefore impossible**, and O2 holds at bounded r with no polylog.
     The numbers agree: 0 violations of Lemma 4 on 8 designs, and the bound is attained with equality on some
     tuples.
   - **What stays open is r → ∞.** Corollary 5 weakens there to R ≳ Q·r^{−ρ}, and this is exactly P2's target
     regime (r ≈ √n, ρ = O(1)). Exact computation at n ≤ 24 cannot reach it, because there ρ/s is never small.
5. **Comparisons.** At these n, OpenAI's R ≈ √(8Q ln(6r²λ)) is 13.8–22.2, larger than Q itself, so the template's
   parameter formula is vacuous here. "Template bound" below means Q/√ln n, i.e. Thm 2 with c = 1: the ARV
   constant is unknown, so Thm 2 cannot be tested numerically. Our R sits below Q/√ln n for ρ ≥ 1 and below the
   trivial 0.75Q in all cases. Dense/generic rows land in the trivial regime: worst-occurrence systems are full
   rank, with R_o ≈ (Σ_i K_i − #multipliers)/|comp| ≈ Q(1−1/r) − Qρ(r−1)/n (§5.3).

Net assessment for P2: **no evidence of a gain, and a proof that none is possible at bounded r**. The question that
matters (r ≈ √n, ρ = O(1), heights 2^{o(√n)}) is not decidable by computation at n ≤ 24. It is O2 with r → ∞, and
Lemma 4 is the best tool available for it.

---------------------------------------------------------------------------------------------------

## 1. What exactly was implemented

**Design** (Def. `def:layout` items 1–4 = [DL] Def. 5.1(c)). Points t = 1..Q, r groups. Per point:
- a partition with |S_{t,h}| = n/r exactly (balanced; `def:layout` allows ≤ 2n/r);
- an assigned group α_t(e) per clause;
- for each (t,h), a list of ≤ ρ integer rows supported in S_{t,h}, spanning R_{t,h}. ρ bounds the rows of
  **every** group, including the assigned ones.

**Unknowns.** For each occurrence o = (e,v), P_o(T) = e_v + Σ_{k=1}^R T^k c_k, c_k ∈ ℚ^n. R is the degree: the
[DL]/P2 convention, which is OpenAI's "R − 1".

**Constraints.** For all t and all h ≠ α_t(e): P_o(t)|_{S_{t,h}} = Σ_j μ_{o,t,h,j}·row_j. This is linear in the
c_k and the multipliers μ. One equation per (t, coordinate i with part_t(i) ≠ α_t(e)); the entries are t^k and the
row coefficients, all integers.

**Facts used by the solver** [R, elementary]:
- (i) Occurrences decouple: the constraints of o involve only P_o and its own μ's.
- (ii) The system of o splits into connected components (coordinate i is linked to the rows of its group at its
  foreign points). Only the component of v carries the inhomogeneity; every other component takes the zero
  solution. So R_o is the least R at which v's component is consistent, and R = max_o R_o.
- (iii) L_o ≤ R_o ≤ N_o. Here L_o = #{t : v foreign at t and no vector of R_{t,part_t(v)} has a nonzero
  v-coordinate}, where p_v(t) = 0 is forced, and N_o = #foreign points of v, where p_v = Π(1 − T/t) always works.
- (iv) If all rows are singletons, R_o = L_o exactly (coordinates decouple), so stage 1 is combinatorial.

**Arithmetic.** Consistency is tested by one elimination of [A | b] mod p = 2147483629. Every reported design is
re-verified over ℚ (sympy `DomainMatrix` over QQ, exact ranks): R_o feasible and R_o − 1 infeasible, for every
occurrence. Every stage-2 output and every final design passed (`exact_verified: true` in `stage2*.out`).
`test_solver.py` checks the component reduction against the full n-coordinate system and mod-p against ℚ on
3,648 random coupled systems with mixed dense rows: 0 disagreements.

**Instances** (ambiguities in §6). All bounded-occurrence; primal treewidth upper bounds (min-fill) are given.
- **L3**: random 3-uniform, 3-regular *linear* 3-CNF (every variable in exactly 3 clauses, no two clauses
  sharing two variables), m = n, M = 3n. Treewidth upper bounds 8, 10, 10 at n = 16, 20, 24.
- **G3 / G4**: clauses = edges of a random connected cubic / 4-regular graph with girth ≥ 4. This is the literal
  "primal graph cubic/4-regular with girth ≥ 4"; clauses have size 2. M = 3n / 4n. Treewidth upper bounds 5, 5, 6
  and 6, 8, 8.
- Literal signs are irrelevant: feasibility depends only on the incidence structure.

**Searches.**
- **Stage 1** [C search, N evaluation], `stage1_singleton.py`. Simulated annealing (4·10⁵ moves; 3 seeds per
  cell) over partitions (swaps), assignments and singleton sets, energy Σ_o 5^{R_o}; we keep the
  lexicographically best (max R_o, Σ R_o). Variants:
  - "fixed": one t-independent measured set A with ρ members in every group at every point, i.e. Λ = span(e_A).
    This is a template-type design (§4, Lemma 6).
  - "rscale": r = n/4, groups of size 4.
- **MILPs** [N, HiGHS]. `milp_singleton.py` gives the exact optimum of the singleton class (small cases; time
  limited otherwise). `milp_onepoint.py` gives F*(ρ), the minimum number of unabsorbed foreign occurrences at one
  point. Since Σ_o R_o ≥ Q·F*, this yields the rigorous bound R ≥ ⌈Q F*/M⌉ for singleton designs and for ρ = 0.
- **Stage 2** [C search, N evaluation], `stage2_general.py`. Annealing over rows from the height-≤2 candidate
  families above, plus assignment changes and partition swaps. Exact per-occurrence R_o (mod p) after each move;
  4000 moves at ρ = 1 and 1500 at ρ = 2, for every (family, n, Q, ρ ≥ 1) at r = 4 (ρ = 2 only for Q ≥ 6). Modes:
  - `mixed`: starts from the stage-1 design;
  - `mixedrand`: starts from random non-singleton rows;
  - `dense`: group/signed/random dense rows only.
- **Exhaustive single-slot neighbourhoods** [N], `neighbourhood.py`. For a design, every slot (t,h,row), and
  every row with entries in {−2..2} supported in S_{t,h} (up to sign; support ≤ 3 at n = 20, 24), we recompute
  all R_o exactly.

## 2. Validation on OpenAI's template [N]

`validate_template.py r Q A0 R_OAI [FAM n]`, outputs `validate_template.out`, `validate_template_instance.out`.

| B, window | c_B = D·Pr[W∉I] | rank(I−M₀) | (T2) violations | Thm 1 bound (best of 2^Q signed φ) | explicit rows satisfy constraints | general-interface min deg (orbit reps k=0..4) | template-subclass min deg |
|---|---|---|---|---|---|---|---|
| r=2,Q=4, I={0,1,2} | 13 | 13 | 0 | 9 ≤ 13 | yes (exact) | 0,1,2,2,2; deg 1 infeasible for k=3,4 | 0,1,2,2,2 |
| r=2,Q=4, I={0,1} | 67 | 67 | 0 | 37 ≤ 67 | yes | 0,1,1,1,1; deg 0 infeasible for k≥2 | same |
| r=2,Q=4, I={1,2} | 94 | 94 | 0 | 37 ≤ 94 | yes | 0,0,1,1,1 | same |

Here k is the number of positions with a_u ≠ d_u; the orbit representatives cover all of B by symmetry.

**Pushed forward to L3, n = 16** (r = 2, Q = 4, I = {0,1,2}, random a_v, d_f; 48 occurrences in 3 copies of B):
- the pushed-forward rows satisfy every constraint and P(0) = e_v, exactly;
- the pushed-forward measurement spaces have dims 3–7 per group (group sizes 6–10), ℓ₁ ≤ 3;
- our solver's max R on that design is 2, the template's degree.

So the solver reproduces a known feasible design at OpenAI's R and finds nothing below it. For these level-set
spaces the general interface gives no extra freedom (consistent with `parity-barrier.md` §5.2: general = longest
run = template for a single window).

## 3. Main table, r = 4 [N evaluation of best-found designs; C that they are optimal]

Each cell gives R_max and mean_o R_o / Q, best over all searches (`final_tables.out`).
- "fixed Λ": template-type singleton designs (t-independent A), for ρ = 1 and ρ = 2.
- LB: rigorous ⌈Q F*(0)/M⌉ for ρ = 0, from the exact one-point MILP; given only where F* was proved optimal.
- MILP singleton exact optima (`milp.out`): L3 n=16, Q=4 gives R = 2 (ρ=0) and R = 1 (ρ=1), proved. Elsewhere the
  MILP is time-limited and its primal solutions are no better than the annealing ones.

| fam n | Q | ρ=0 | ρ=1 | ρ=2 | fixed Λ (ρ=1,2) | LB ρ=0 | Q/√ln n | OAI √(8Q ln 6r²λ) | 0.75Q |
|---|---|---|---|---|---|---|---|---|---|
| L3 16 | 4 | 2 .333 | 1 .182 | 1 .083 | 2 2 | 2 | 2.40 | 13.8 | 3.0 |
| L3 16 | 8 | 4 .362 | 2 .182 | 1 .083 | 3 3 | 3 | 4.80 | 19.5 | 6.0 |
| L3 16 | 10 | 4 .377 | 3 .198 | 1 .083 | 4 4 | 3 | 6.01 | 21.8 | 7.5 |
| L3 20 | 4 | 2 .325 | 1 .192 | 1 .079 | 2 2 | 2 | 2.31 | 14.1 | 3.0 |
| L3 20 | 8 | 3 .346 | 2 .190 | 1 .096 | 3 3 | 3 | 4.62 | 19.9 | 6.0 |
| L3 20 | 10 | 4 .317 | 3 .197 | 1 .090 | 4 4 | 3 | 5.78 | 22.2 | 7.5 |
| L3 24 | 4 | 2 .319 | 1 .212 | 1 .104 | 2 2 | – | 2.24 | 14.1 | 3.0 |
| L3 24 | 5 | 2 .361 | 2 .203 | 1 .111 | 2 2 | – | 2.80 | 15.7 | 3.8 |
| L3 24 | 8 | 3 .335 | 2 .210 | 2 .123 | 3 3 | – | 4.49 | 19.9 | 6.0 |
| L3 24 | 10 | 4 .324 | 3 .206 | 2 .115 | 4 4 | – | 5.61 | 22.2 | 7.5 |
| G3 16 | 8 | 3 .247 | 1 .091 | 0 .000 | 3 2 | 2 | 4.80 | 19.5 | 6.0 |
| G3 24 | 8 | 3 .247 | 1 .120 | 1 .016 | 2 2 | – | 4.49 | 19.9 | 6.0 |
| G3 24 | 10 | 3 .229 | 2 .101 | 1 .022 | 3 3 | – | 5.61 | 22.2 | 7.5 |
| G4 16 | 8 | 3 .312 | 2 .127 | 1 .010 | 3 2 | – | 4.80 | 19.5 | 6.0 |
| G4 20 | 8 | 3 .298 | 2 .138 | 1 .038 | 3 3 | – | 4.62 | 19.9 | 6.0 |
| G4 24 | 8 | 3 .289 | 2 .143 | 1 .053 | 3 3 | – | 4.49 | 19.9 | 6.0 |
| G4 24 | 10 | 4 .282 | 2 .167 | 1 .064 | 4 3 | – | 5.61 | 22.2 | 7.5 |

(All 135 cells, Q ∈ {4,5,6,8,10}, are in `final_tables.out`.)

**One-point optima** [N], `milp_one.out`. F*(0) = 14/48 (L3, n=16), 16/60 (L3, n=20) and 9/48 (G3, n=16) were
proved optimal; the other ρ = 0 cases are time-limited, with primal values 19/72 (L3, n=24), 12/60, 11/72 (G3) and
16/64, 20/80, 20/96 (G4). With singleton rows the best one-point designs found leave:
- L3, ρ = 1: 8/48, 10/60, 15/72 occurrences unabsorbed;
- L3, ρ = 2: 4/48, 5/60, 9/72;
- G3, ρ = 2: 0, proved, at n = 16 and n = 20. For G3 at ρ = 2, one point already absorbs everything, so R = 0:
  a single measured separator with no interpolation at all.

**Group size s = 4 (r = n/4)** [N eval / C opt], `stage1_rscale.out`. Mean R_o/Q at Q = 8:
- L3: ρ = 0: .362/.375/.377; ρ = 1: .182/.194/.227; ρ = 2: .083/.083/.085 (n = 16/20/24);
- G4: ρ = 1: .127/.141/.146; ρ = 2: .010/.017/.022.

Flat or rising.

**Cost model** (`costs.out`). Per point, log₂[C_q · 2^{rows} · r·2^s] with q = ⌈(MR+1)/Q⌉ − 1. It exceeds n in
every cell. Examples:
- L3 n = 16, Q = 10: 31.4 (ρ = 0), 35.3 (ρ = 1), 29.1 (ρ = 2);
- L3 n = 24, Q = 10: 46.0, 50.0, 52.1.

At these sizes no design in the clause-product scheme is cheaper than brute force. The numbers above are
structural, not algorithmic.

**Heights.** Every best design has only singleton rows: ℓ₁ = 1, measurement range {0,1}. The largest ℓ₁ seen in any
stage-2 or dense design is 8 (≤ 2·n/r by the height-2 cap). The "2^{Θ(n)} range" failure mode never arises here,
because heights were capped by construction. More to the point, large-ℓ₁ rows (group sums) are exactly the ones
that hurt (§5.3).

## 4. Structural results [R]

**Lemma 4 ((ρ+1)-minor lemma; generalises [DL] §9's 2×2 fact).**
- *Setting.* Let o_1..o_k (k = ρ+1) be occurrences with pairwise distinct own variables v_1..v_k. Let
  Δ(T) = det[(P_{o_j}(T))_{v_i}]_{i,j}.
- *Claim.* Δ(0) = det I = 1 and deg Δ ≤ Σ_j R_{o_j}. At every t where all v_i lie in one group h with
  α_t(e_j) ≠ h for all j and dim R_{t,h} ≤ ρ, every row (P_{o_j}(t))|_{S_{t,h}} lies in R_{t,h}. The k×k
  submatrix then has rank ≤ ρ < k, so Δ(t) = 0. Hence such "co-absorption" points number at most
  Σ_j R_{o_j} ≤ kR.
- *Remarks.* The row heights play no role. Occurrences of the *same* variable are unconstrained, as [DL] notes.
- *Check* [N] (`minor_check.out`): 8 designs (dense, random-start and singleton, ρ = 1, 2). 0 violations; the
  ratio max count/Σ R reaches 1.0, so the bound is attained.

**Corollary 5 (counting).** Let V_{t,h} ⊆ S_{t,h} be the variables having a foreign occurrence at t, and b the
maximum occurrence. Then

  Σ_t Σ_h C(|V_{t,h}|, ρ+1) ≤ (ρ+1)·R·b^{ρ+1}·C(n, ρ+1).

*Proof.* Each (ρ+1)-set X ⊆ V_{t,h} gives a co-absorbed tuple at t (choose one foreign occurrence per variable).
X has at most b^{ρ+1} tuples, each co-absorbed at most (ρ+1)R times.

*Consequence.* Suppose every balanced r-partition leaves ≥ βn variables with a foreign occurrence, whatever the
assignment. This holds for expanders: cut clauses ≥ cn, so β ≥ c/b. Convexity then gives
R ≥ Q·r·C(βn/r, ρ+1)/((ρ+1)b^{ρ+1}C(n,ρ+1)), which tends to Q·β^{ρ+1}/((ρ+1)b^{ρ+1}r^ρ).
- **At fixed r and ρ, R/Q is bounded below by a constant independent of n and of the heights.** So the P2 grid
  (r = 4) cannot show decay. For ρ = 1 the bound reads R ≳ Q/r: this is [DL]'s "r ≳ Q/R".
- For r ≈ √n it gives only R ≳ Q·n^{−ρ/2}, which is no contradiction with the P2 target R/Q ≈ n^{−1/2} once
  ρ ≥ 1. The averaged bound is numerically weak at our sizes (R ≥ 0.006–0.16, `minor_check.out`); the
  pointwise form is what bites.

**Lemma 6 (template subclass in variable coordinates; = `parity-barrier.md` §5.1 transcribed).**
- *Definition.* Suppose the measurement part is polynomial: P_o(t)|_{S_{t,h}} = λ_o(t)|_{S_{t,h}} for foreign
  (t,h), with λ_o ∈ Λ[T] and Λ ⊆ ∩_t ⊕_h R_{t,h} shared (so dim Λ ≤ rρ).
- *Claim.* Then o is feasible at degree R iff e_v ∈ Λ + span{e_i : K_i(o) ≤ R}, where
  K_i(o) = #{t : part_t(i) ≠ α_t(e)}.
- *Proof.* d = P_o − λ_o vanishes at the K_i foreign points of each coordinate i, so d_i ≡ 0 when K_i > R.
- *Consequence.* At most dim Λ ≤ rρ "far" variables are rescued across all points together; t-dependent spaces
  rescue rρ variables *per point*.
- *Data.* The "fixed Λ" column (Λ = span e_A) gains at most 1 over ρ = 0 and is 1–2 worse than the t-dependent
  designs at Q ≥ 6.

This is the variable-coordinate face of `parity-barrier.md` Thm 1. Thm 2 (R ≥ cQ/√log n) is asymptotic, with an
unknown ARV constant; it is consistent with, but not testable by, these numbers.

## 5. Answers to the questions P2 asks

1. **Feasible/infeasible per parameter set.** Every design reported is exactly verified: feasible at R_o, and
   infeasible at R_o − 1 or blocked by the lower bound L_o.
   - Minimum R found (§3): 1–4 at ρ = 0 … 2 and Q = 4 … 10. R ≤ Q/4 at Q = 8, ρ = 2 on all 9 instances.
   - Proved minima: L3 n=16, Q=4: R = 2 (ρ=0), 1 (ρ=1), via MILP over the singleton class. When ρ = 0 that class
     is the whole design space (no rows, so R_o = N_o by §1 (iii)); at ρ = 1 it covers singleton designs only. Rigorous ρ = 0 lower bounds ⌈Q F*/M⌉ are in the LB column, e.g. 3 at
     Q = 8, 10 for L3 n ≤ 20; the annealing found 3–4.
   - These are minima over the searched designs, not over all designs [C], except where stated.
2. **System sizes and ranks** (`system_sizes.out`, exact over ℚ).
   - Singleton designs: tiny systems. For L3 n=24, Q=8, ρ=1, the worst occurrences have 2–4 equations × 1–4
     unknowns; at R = 2, rank A = rank[A|b]; at R = 1, rank[A|b] = rank A + 1.
   - Dense ρ = 1, L3 n=16, Q=8: 96 equations × 104 unknowns at R = 5, ranks 96 = 96 (feasible); at R = 4,
     96 × 88 with ranks 84 vs 85 (infeasible). There L_o ∈ {0,1}, so the trivial lower bound is vacuous and the
     obstruction is genuine coupling.
   - Dense ρ = 2: 96 × 112 at R = 4 (ranks 96/96); 96 × 96 at R = 3 (ranks 90/91, 92/93).
3. **The dense regime is the trivial regime.** For dense rows the component of v is all of [n]. Feasibility needs
   n·R + #μ ≥ #independent equations = Σ_i K_i ≈ nQ(1−1/r), i.e. R ≳ Q(1−1/r) − Q(r−1)ρ/n. For n=16, Q=8 this
   gives 4.5 (ρ=1) and 3 (ρ=2); the observed values are 5 and 4. This is the "R ≥ Q(1−1/r) − O(1)" evidence
   against that P2 mentions, and it occurs exactly for the rows (group sums) that are cheap in height. Sparse rows
   avoid it only by being singletons in effect.
4. **R/Q vs n at fixed Q/√n.** It does not decrease for ρ ≥ 1 (pairs (16,4)/(24,5) and (16,8)/(24,10)). At fixed
   Q and ρ ≥ 1 it is non-decreasing in n. With s fixed (r = n/4) it is flat. For ρ = 0, mean R_o/Q is flat at about
   0.33 (L3), 0.25 (G3) and 0.30 (G4), which is the per-point cut fraction F*/M ≈ 0.27–0.29 plus imbalance.
5. **Does the [DL] §9 obstruction generalise?** Yes, in the form of Lemma 4, for any number ρ of rows and any
   heights. Empirically it is the operative obstruction: every attempt to absorb two distinct variables with one
   row worsened the design. Turning Lemma 4 into R ≥ Q/polylog(n) for r ≈ √n is exactly O2 and remains open;
   Lemma 4 + Corollary 5 settle only the bounded-r case.

## 6. Readings of ambiguous points (and alternatives run)

- **"Cubic/4-regular primal graph with girth ≥ 4".** A 3-CNF's primal graph contains a triangle per clause, so
  read literally this forces 2-clauses: families G3, G4. We also ran the natural 3-CNF reading, L3 (3-regular
  linear hypergraph; primal graph 6-regular). Both were run; the conclusions agree.
- **Tovey copies** of a random 3-CNF at density 4.26 on 6–8 variables have 3m ≈ 77–102 variables, outside
  n ≤ 24. Not run.
- **"Height ≤ 2"** read as entries of absolute value ≤ 2; ℓ₁ and measurement ranges are reported separately.
  Group sums have ℓ₁ = n/4.
- **R** is the degree bound, as in [DL] Def. 5.1(a). OpenAI's R in `def:layout`/§4 is the window length = degree + 1.
- **ρ** is the maximum number of rows in each group, including the clause's assigned group. Groups are exactly
  n/r. Alternative run: r = n/4 with s = 4 fixed.
- **"Template bound R ≥ cQ/√log n"** is tabulated with c = 1 (Q/√ln n); the true c (ARV) is unknown.

## 7. What would change the verdict

- A design at r ≈ √n with ρ = O(1) and R/Q → 0 would need, by Lemma 4, the co-absorbed (ρ+1)-tuples to be spread
  thin over points.
- Equivalently, the foreign variables of each group at each point would have to vary so much across points that
  no (ρ+1)-set recurs more than (ρ+1)R times.
- The singleton-row data suggest the cheapest way to do this is to rotate which variables are measured. That
  costs one row per absorbed variable per point, so total absorption ≤ Q·r·ρ against Θ(Qn) foreign incidences.
  R/Q then stays ≳ (cut fraction) − rρb/M, which is constant unless rρ = Θ(n), i.e. τ = Θ(1).
- A proof of O2 at r ≈ √n would have to show that non-singleton rows can never beat this "one row per variable"
  accounting by more than a polylog factor. Lemma 4 shows they cannot co-absorb ρ+1 distinct variables
  repeatedly; what is missing is a way to combine the tuples across different groups and points (the
  t-dependence). [C]

## 8. Scripts and outputs (all in `research/scripts/engine3-p2/`)

- `p2common.py` — instances, per-occurrence system with component reduction, mod-p consistency, exact ℚ ranks,
  min R_o.
- `test_solver.py` → `test_solver.out` — 3,648 checks: component vs full system, mod p vs ℚ; 0 disagreements.
- `validate_template.py` → `validate_template.out`, `validate_template_instance.out` — §2.
- `stage1_singleton.py` → `stage1.out` (675 runs, r = 4, incl. fixed-Λ), `stage1_rscale.out` (270 runs, r = n/4);
  designs in `designs/` (about 3 MB of pickles).
- `milp_singleton.py` → `milp.out`; `milp_onepoint.py` → `milp_one.out`.
- `stage2_general.py` → `stage2.out` (73 runs, mixed), `stage2_rand.out` (4, random start), `stage2_dense.out` (4).
- `neighbourhood.py` → `neighbourhood.out` (9 designs, 138,592 tests), `neighbourhood_rho2_span.out` (ρ = 2 rerun
  that classifies whether tied rows change the space).
- `minor_check.py` → `minor_check.out` (Lemma 4 on 8 designs).
- `system_sizes.py` → `system_sizes.out` (exact sizes/ranks).
- `final_tables.py` → `final_tables.out`; `costs.py` → `costs.out`.
- Grids: `grid1all.txt`, `grid_rscale.txt`, `grid2.txt`/`grid2b.txt`, `grid_milp.txt`, `grid_one*.txt`;
  `batch3.sh` / `batch3.cmds`.
