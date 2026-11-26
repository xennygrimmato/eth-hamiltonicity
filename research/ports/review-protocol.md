# Referee report: `protocol/notes.md` (explicit level-1 protocol on K_{2,3}, rate 6/(4+√10))

Referee scripts are in the scratchpad (`ref/mylp.py`, `ref/search.py`, `ref/buckets.py`, `ref/cnt.py`) and were written
independently of the notes' scripts. Sources checked: the paper text (App. A.3, B.1–B.4) and the Lean files
`Paper/Identity.lean` (`prop_identity`), `Nc/Cross/Psi.lean` (`matM`) and `Paper/States.lean` (`stateCount`).

## Verdict summary (weakest point first)

| # | Item | Verdict |
|---|---|---|
| 1 | (c) max over term types equals the all-middle value | **gap, numerical only** (as the notes say: [N]). It is supported by an independent check. Without it, every finite B still gives a rate 1/n*(B) that a finite set of LPs proves. |
| 2 | (f) "smallest instance" | **correct with fix**. The arithmetic is confirmed. "First instance above 3/4" means the first one found in a one-parameter scan, not a proved minimum. The margin 0.7529 rests on float LPs. |
| 3 | (e) dual / optimality of level 1 | **correct as [N]**. Rerun: 0.837118 on a 12-point p:q grid, the same symmetric metric. The binding family holds exactly by Cauchy–Schwarz. |
| 4 | (c) cover → single restriction, who knows the word, rank accounting, time-sharing | **correct** |
| 5 | (d) cost of the shared index | **correct** (and conservative) |
| 6 | (b) Lemma A.3 with hubs at real parties | **correct** |
| 7 | (a) Prop. B.2/B.3, the matrix reading, over ℤ | **correct** |

The statement that is actually proved: Proposition P1 holds with rate ≥ 1/n*(B) for every fixed B, over every field.
The values are n*(2) = 1.2029076, n*(4) = 1.20188, n*(8) = 1.19860 and n*(16) = 1.19643, so the rate is ≥ 0.83582 at B = 16.
This rests on finitely many LPs, which are floating-point now and could be made exact. The supremum over B equals
1/max_{circle} LP, and that maximum equals (4+√10)/6 only numerically.

---

## Item 7 — (a) the crossing identity [AN, Prop. B.2/B.3]

**Exact statement** (paper l. ~1335 ff.; Lean `prop_identity`):
- Σ₁ and Σ₂ are the sets of all symbols (I, J), with |I| = |J|, of fixed size and energy (n₁, e₁) and (n₂, e₂).
- Θ = 2(e₁+e₂), and P(N) = `stateCount N` = #symbols of energy ≤ N.
- There are **integer** tensors Ψ₀, …, Ψ_Θ with:
  - (a) Σ_N Ψ_N = [a=c][b=d];
  - (b) Ψ_N = Σ_{k<(N+1)P(N)} g_k(s_a,s_d) h_k(s_b,s_c);
  - (c) the same with (N′+1)P(N′) terms of the form g(s_a,s_b)h(s_c,s_d), where N′ = Θ−N.

All functions are ℤ-valued. A decomposition with k terms over ℤ therefore reduces to k terms over every field, and the sign ε = ±1 is a unit everywhere, so **"over every field" is justified**.

**Matrix reading.** I compared the reading in `crossing_identity_modp.py` entry by entry with the Lean `matM`, built as
`fromBlocks blX blU (−(blU on swapped words)ᵀ) blY`. Rows and columns are ordered a, d | c, b. All 12 off-diagonal blocks agree, including the signs and the transposed index conventions in (d,a), (c,d) and (b,a). (In my text copy the table in the paper is in fact legible, and it agrees too.) **The reading is correct.**

**Asymptotics (B.3 proof).** Take E_i = ⌊p²n₀⌋ and ⌊q²n₀⌋, and a pigeonhole class with e_i ≤ E_i. Then:
- ln D₁ = (p+o(1))κ√n₀ and ln D₂ = (q+o(1))κ√n₀.
- Term N has r² = (Θ−N)/n₀ (cut ab|cd, bound (c)) and r′² = N/n₀ (cut ad|bc, bound (b)).
- So r² + r′² = Θ/n₀ ≤ 2(p²+q²).
- ln((N+1)P(N)) ≤ ln(Θ+1) + κ√N, so the error is O(log n₀) = o(√n₀).

The notes' labelling (r on {u₁,v_i}|{u₂,v_j} and r′ on {u₁,v_j}|{u₂,v_i}, with (a,c,b,d) = (u₁,u₂,v_i,v_j)) is consistent with this. **Correct.**

**Rerun** of `crossing_identity_modp.py`:
- (1,4,1,4): dimensions 2×2, Θ = 16, the top coefficient is zero, (a) holds with sign +1. Ranks across ad|bc are 1, 3, 4, …; across ab|cd …, 3, 1.
- (2,12,2,12): dimensions 5×5, Θ = 48, (a) holds with sign +1. Ranks across ad|bc for N = 0, 2, …, 14 are 1, 3, 7, 11, 16, 21, 23, 24, then 25 (full) up to N = 48, mirrored across ab|cd. This is exactly as printed in the notes, and every rank is ≤ its bound (e.g. N = 8: 16 ≤ 9·P(8) = 108).

My independent count gives P(0..12) = 1, 1, 2, 2, 4, 4, 7, 7, 12, 12, 19, 19, 30. This equals Σ_{m≤E/2} p(m) (the Frobenius bijection), as used in `level1_instance.py`.

## Item 6 — (b) Lemma A.3

Exact statement (l. 1085–1113): if t on I₁ ⊔ I₂ is a sum of r products, then t is a restriction of
Π_{p∈I₁}⟨n_p⟩_{p o₁} · ⟨r⟩_{o₁o₂} · Π_{p∈I₂}⟨n_p⟩_{p o₂}, "and this remains true when o₁ and o₂ are identified with
given parties" (push-forward). When a hub coincides with a party of the term, a self-wire becomes a local vector; when o₁ = o₂, the hub wire is local. Both are fine.

The network a term is restricted from has these wires:
- dimension D₁ from a = u₁ and from c = u₂ to their hubs;
- dimension D₂ from b and from d to their hubs;
- one hub wire of dimension ρ (the rank bound of the bucket).

The table of four options in §2.1 is correct. For example, "c via u₁" puts Q on u₁v_i, r on u₁v_j and P on u₂v_j. **Correct.**

## Item 4 — (c) the main risk: one restriction versus a sum

1. **Who knows the word.** No party has to "know" it classically. T_K = Σ_w T_w with T_w = (⊗_p A_{p,w}) S^{⊗n′}.
   Then T_K = (⊗_p Σ_w A_{p,w} ⊗ e_w^*)(S^{⊗n′} ⊗ GHZ_M), with GHZ_M = Σ_w e_w^{⊗5}. Each party's single fixed map is
   block-diagonal, controlled by its copy of the index. The index is the **whole word** w ∈ [B]^{3K}, not only its
   type, so M = B^{3K}. This is what step 4 of §2.3 says. ✔
2. **Cost of GHZ_M.** ⟨2⟩ on five parties is a restriction of the 4 binary wires of any spanning tree of K_{2,3} (Lemma A.2, last claim), hence of S. So GHZ_M ≤ S^{⊗⌈3K log₂ B⌉}. Per block this is 3 log₂ B bits on every edge; the notes charge it on all 6 edges, though only 4 carry it. It is O(1) against Θ(κ√n₀) bits of supply per block, so it is negligible for fixed B as n₀ → ∞. ✔
3. **Rank accounting.** The rank bound is used only for each bucket tensor Ψ_β = Σ_{N∈β} Ψ_N, whose rank on each cut is at most Σ_{N∈β} (bound) = exp(max + O(log Θ)). Each factor Ψ_β^{(k,e)} of a word gets its own A.3 decomposition and network. A word-term is the tensor product of its factors, so it is a restriction of the tensor product of the chosen networks. The rank of a sum of words is never used. ✔
4. **Same supply for all words.** Each word's network is routed onto binary wires; the load on an edge is ⌈Σ log₂(dims)⌉ ≤ n′. Words with a smaller load pad, since ⟨1⟩ ≤ ⟨2⟩. All words are therefore restrictions of the one S^{⊗n′}. ✔
5. **Time-sharing.** Within one word, the choice per block is a product over blocks of per-block restrictions. Rounding ⌊λ_π g_τ⌋ / ⌈λ_π g_τ⌉ costs at most B³·M·L on an edge. Because the cover index is the whole word, the assignment may depend on the word. ✔
6. **Fractional routing.** A wire of dimension D splits into ⌈log₂ D⌉ binary wires, which can be routed separately; the ceiling losses are O(K) bits, against K·κ√n₀. ✔

**Recomputation of the game with my own LP.** Options: both pairings × 25 ordered hub pairs per pair; every produced wire
routed along **all** simple paths of K_{2,3}. Units Q = 1, P = 1/3, ρ = √10/3, A = 4/3.
- Trivial ranks: 4/3 (routing). ✔
- All-middle: **1.1937129434 = (4+√10)/6**. ✔ Exact lower bound: with the uniform edge price 1/6, every option of a pair has total edge load ≥ A+ρ (minimum checked over all 50 options), so the value is ≥ 3(A+ρ)/6. The cyclic mixture of the notes meets this; I checked its six edge loads by hand, each (A+ρ)/2. So the all-middle value is [R].
- Other types: (0,0,0) 0.5556; (0,π/4,π/2) 0.7105; (0.3,1.2,0.7) 0.9561; (π/4,π/4,0) 1.0000; (0.6,0.6,0.6) 1.1026; (0.9,0.9,0.9) 1.1409.
- Maximum over the type grids: 9³ and 17³ both give 1.1937129 at (π/4,π/4,π/4), with neighbours at 1.1756. 40 Nelder–Mead runs from random starts give 1.19371300, which is LP tolerance (5·10⁻⁸).
- **Bucket game n*(B)**: B equal intervals of N/n₀, with corner bounds r̄ = √(Θ/n₀ − x_lo) and r̄′ = √x_hi, all B³ types:

  | B | n*(B) | rate 1/n*(B) |
  |---|---|---|
  | 2 | 1.2029076 | 0.83132 (matches the notes) |
  | 4 | 1.2018755 | 0.83203 |
  | 8 | 1.1986027 | 0.83430 |
  | 16 | 1.1964314 | 0.83582 |

  These values decrease towards 1.19371, consistent with an O(1/B) gap. They are the honest finite-B rates.

The remaining [N] point is that max over the circle of LP(τ) is attained at all-middle. LP(τ) is neither convex nor concave in (r, r′), so the grid evidence is not a proof. A proof could be made from the bucket game itself: n*(B) ≤ (4+√10)/6 + ε(B) with ε(B) → 0 is equivalent to the claim, and it could be certified by a branch-and-bound over bucket boxes with exact dual certificates. The notes label the claim [N] correctly in §2.2 and §2.3. The abstract's "rate 6/(4+√10)" should read "every rate below 1/lim n*(B), with lim n*(B) = (4+√10)/6 [N]".

## Item 5 — (d) shared index

Verified in Item 4, points 1–2. Two minor remarks:
- The cost is ⌈3K log₂ B⌉ **copies of S**, not "bits" on unspecified edges; the notes do write S^{⊗(n′+⌈3K log₂ B⌉)}, which is right.
- The order of limits is fine either way. With B fixed: K → ∞ removes B³ML/K, and n₀ → ∞ removes 3 log₂ B/U and the O(log Θ)/U rank error, where U = κ√n₀/ln 2. Then B → ∞.

## Item 3 — (e) dual check

Rerun of `level1_dual.py 3 6 12`: R = 0.837118 in 6/6 starts, at the metric |uv| = 1, |u₁u₂| ≈ 1.298, |v_iv_j| ≈ 1.9565. On the fine grid the notes report 0.83765, approaching 0.83772. Closed form: 6/((1+1/√10) + 3(1+3/√10)) = 6/(4+√10) = 0.837722. ✔

The binding family (u₁u₂; v_iv_j) with corner hubs needs p|u₁u₂| + q|v_iv_j| ≤ p+q+√(p²+q²). For the symmetric metric this is (p+3q)/√10 ≤ √(p²+q²), which is Cauchy–Schwarz: **exact**, tight at p:q = 1:3. That the other instances hold, and that this is the global minimum, is [N] (non-convex SLSQP). This item is about the optimality of level 1 only; the protocol does not depend on it.

## Item 2 — (f) smallest instance

My independent counts give log₂|Σ(8,436)| = 42.55499 and log₂|Σ(21,3000)| = 127.80667, as in the notes. A rerun of `level1_instance.py 8 436 21 3000` gives:
- saving 7.744 bits;
- LP loads 166.563 (acyclic) and 166.490 (cyclic), +3 for the cover;
- m_blk = 127.665;
- rate **0.75291**. ✔

Nearby instances: (7,380; 19,2500) gives 0.74579; (8,400; 20,2800) gives 0.74146 (D₁³ and D₂ mismatched); (9,500; 22,3300) gives 0.75282.

Fix: "the first instance above 3/4 has wires ≈ 2^128" is the first point of a one-parameter scan:
- 2 buckets, p:q ≈ 1:3, largest class per energy, proved rank bounds.
- Other bucket counts, ratios or class choices were not optimised, so this is not a minimality statement.
- The margin (0.4%) rests on float LPs (request 2 of the notes, exact LP, is the right fix).

"No gain at small size": confirmed. At 5×5 every term with 16 ≤ N ≤ 32 has full rank 25 on both cuts, so the per-block saving is 0 and the +3 cover cost makes it worse than routing.

## Item 1 — what is proved

- **Proved, modulo exact verification of finitely many LPs:** for each B there is an explicit family T^{⊗m} ≤ S^{⊗n}, over every field, with m/n → 1/n*(B). All o(n) terms are accounted for: the cover index, the bucket log Θ, rounding, ceilings and the o(1) in the class sizes. B = 16 gives > 0.8358; B = 2 gives 0.83132.
- **Imported:** B.2, Lean-checked in [AN]; the reading of the matrix agrees with the Lean source.
- **Exact:** the all-middle value (4+√10)/6 (explicit mixture plus uniform price).
- **Numerical:** sup_B 1/n*(B) = 6/(4+√10), via max over the circle at all-middle; level-1 optimality (§2.4); §4 (0.854).
- **Not refereed here:** §3.3 (small-size obstructions for arbitrary protocols) and §3.4 beyond the d = 2 identity, which is correct: δ_acδ_bd − δ_adδ_bc = ε_abε_cd.
