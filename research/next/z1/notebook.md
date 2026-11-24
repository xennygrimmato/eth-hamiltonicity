# z1 notebook: Route 2 (p parallel classes of AG(2,g)) and Route 4 (engine over F₂)

24 Nov 2026. Executor z1. Tags: [R] proved, [N] computed (script named), [C] conjecture,
[R|FH] proved under the flat hypothesis, [R|PH] under the planar hypothesis.

Sources: `next/ideas-3sat.md` (Routes 2, 4), `engine3-STATUS.md`, `engine3-open-door.md` §1.4–1.7, §2.3–2.7,
`vpvnp/b2/notebook.md` and scripts (`far_opt.py`, `verify_flat.py`, `metric_lp.py`).

## Log
- 0:00 read sources; set up folder.
- 0:20 wrote `ag_floor.py` (table), `check_orth.py` (independent finite-M checker). 0:45 table g = 2..5 (g = 5 still running).

## 1. Route 2, step 1: the floor table [first version, 0:50]

**Setting.** Level on AG(2,g): K = g² nodes, all C(K,2) edges as ONE configuration (so edges of merge classes are
included: an edge of class c is internal to merge c, Δ^c_e = 0, and costs 0 there). Merges = p of the g+1 parallel
classes. ρ is normalised by ALL edges, C(K,2)λ, because that is the recursion's denominator (e_{ℓ+1}S_{ℓ+1} = e_ℓ·cost).
PΓL(2,g) is transitive on every p-set of classes for g ≤ 5, so one price gives V ≥ (Σ_k b_k)/p [R].

**Closed forms [R].**
- Orthogonal price (hubs of merge k on a regular simplex in its own orthogonal block, u_e ∥ Σ_kΔ^k_e):
  **ρ_orth(p,g) = (√(p−1) + (g+1−p)/√p)/(g+1)** — a lower bound on ρ [R|FH]. Checked per merge with exact distances
  at M = 10⁷ (`check_orth.out`, all 14 (g,p) agree to 5 digits).
- **Cap of the far-leg Euclidean method [R]:** Σ_e|Σ_kΔ^k_e| ≤ √E·(Σ_e|Σ_kΔ^k_e|²)^{1/2}, and the cross terms
  Σ_e⟨Δ^k_e,Δ^{k′}_e⟩ vanish for k ≠ k′ over all pairs (two lines of different classes meet in exactly one point;
  checked numerically, `check_orth.out`), so the method can never certify more than **√(g/(p(g+1)))**. At p = g+1
  this equals ρ_orth: the orthogonal price is optimal there.
- Pigeonhole/star (Theorem 1 generalised, every field): ρ ≥ g/((g+1)p).
- "sep" = the floor if merge-class edges are kept as separate raw configurations (Route 2 as first written):
  ((p−1) + (g+1−p)/√p)/(g+1). At p = g+1 this is g/(g+1): no gain at all. **Internal edges only help if they are
  bundled into the same configuration as everything else.**

| g | p | ρ_orth [R/FH] | method cap | Euclid opt [N] | line price [R, uncond.] | star [R] | sep | 1/√p | reading |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 2 | 0.569 | 0.577 | 0.569 | 0.500 | 0.333 | 0.569 | 0.707 | = Anthropic level at g=2 (App. B + straight edges): floor attained |
| 2 | 3 | 0.471 | 0.471 | 0.471 | 0.333 | 0.222 | 0.667 | 0.577 | K₄ with 3 matchings; smallest instance below the p=2 value |
| 3 | 2 | 0.604 | 0.612 | 0.604 | 0.389 | 0.375 | 0.604 | 0.707 | = Anthropic level at g=3, attained |
| 3 | 3 | 0.498 | 0.500 | 0.498 | 0.333 | 0.250 | 0.644 | 0.577 | first ≤ 1/2 under FH |
| 3 | 4 | 0.433 | 0.433 | 0.433 | 0.292 | 0.188 | 0.750 | 0.500 | all classes; orth optimal |
| 4 | 2 | 0.624 | 0.632 | 0.624 | 0.400 | 0.400 | 0.624 | 0.707 | Anthropic, attained |
| 4 | 3 | 0.514 | 0.516 | 0.512* | 0.333 | 0.267 | 0.631 | 0.577 | |
| 4 | 4 | 0.446 | 0.447 | 0.445* | 0.292 | 0.200 | 0.700 | 0.500 | |
| 4 | 5 | 0.400 | 0.400 | (running) | | 0.160 | 0.800 | 0.447 | all classes |
| 5 | 2..6 | 0.638, 0.524, 0.455, 0.408, 0.373 | | (running) | | | | | |
(* SLSQP found slightly less than the closed form: local optimum; the closed form is the valid bound.)

**One-paragraph reading.**
1. For p = 2 the flat floor *with* internal edges equals exactly what Anthropic's level achieves at every g
   ((g−1)/(g+1) rectangles at 1/√2, 2/(g+1) straight edges at 1/2) [R|PH]: the accounting is calibrated.
2. **The floor does not stay ≥ 1/√2: it drops like 1/√p**, and internal edges lower it slightly further
   (ρ_orth·√p = (√(p(p−1)) + g+1−p)/(g+1) < 1). So the "door is open in the flat case" for every p ≥ 3, and
   below 1/2 from p = 4 (and p = 3 at g ≤ 3). There is no new barrier.
3. But internal edges are a **lower-order effect**: for fixed p and g → ∞ (which the squaring recursion needs),
   ρ_orth → 1/√p and the cap → 1/√p, i.e. exactly b2's fully-crossing floor; α′_flat = ½ log₂ p. Route 2 therefore
   reduces to Route 1's question (is 1/√p attainable for p ≥ 3?), not to a new one.
4. **Unconditional line prices also decay like 1/√p** (≈ E|S−S′|/p with S a sum of p pairwise independent bits,
   ≈ 1/√(πp) ≈ 0.56/√p) [R for each table entry, asymptotic form C]. So neither floor closes the door for growing
   p; equally, no unconditional floor stops α′ → ∞ as p → ∞.
5. p = g+1 (all classes): ρ ≥ √g/(g+1) ≈ K^{−1/4} per level; iterated with K_{ℓ+1} ≈ K_ℓ² this gives
   e(K) ≳ K^{−1/2}·(log K)^{O(1)} — the same order as b1's oblivious floor 1/(16√K). So the AG(2,g)-all-classes tower
   is *flat-optimal up to constants*: if its flat floor were attained, 3-SAT would run in 2^{n^{1−1/18+o(1)}}
   (K ≈ n^{1/9}) [D, modulo the term-count caveat of the ideas file].
