# Referee report: Theorem W, Lemma S and the class of crossing-generated covers (`attain-notes.md` §5, §1.2, §1.3, §2)

Referee notes, 26 Nov 2026. Nothing here is committed. I checked every claim myself, with my own scripts in
`/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/refW/`. I did not reuse the author's code.
I did not use `attain/out/`.

Tags: **[R]** verified here in full (by hand, or by exact computation); **[D]** argued here, proof sketched;
**[N]** numerical (script named); **[C]** conjecture; **[X]** wrong as stated.

Scripts:
- `refW/lemS_test.py`: Lemma S on random wire systems in ℝ², ℝ³ (SOCP) and in metric trees (exact, vertex positions).
  It includes the degenerate shapes: shared hub, crossing a hub–hub bond, parallel wires, a = d, coincident legs.
- `refW/lemS_norm.py`: the same test in the ℓ¹ and ℓ^∞ planes, which are not CAT(0). This is the power check.
- `refW/disc_loss.py`: the exact discretisation loss of the B.2 certificates against the circle. It uses the true P(E) and
  the true largest classes.
- `refW/psi_ranks.py`: an independent construction of the Ψ_N of Prop. B.2, in exact integer arithmetic (python-flint).
  It computes their true flattening ranks across all three cuts.
- `refW/lp1.py`: an independent implementation of the level-1 LP of §2.

---

## 0. Verdict in brief

| # | Item | Verdict |
|---|---|---|
| 1 | **What Theorem W bounds (attack 1(a))** | **Correct only as a statement about certified costs.** c_k(t_leaf) ≤ cost_k(W_leaf) is an upper bound, and nothing bounds the true D1 cost of a leaf tensor from below. The wording "level value" in §0, §5.3 Consequences, §6 and the corollary is **[X]** and must be replaced by "certified level value". |
| 2 | Class §5.1: Khoruzhii / Sra inside? (1(c)) | **Wrong justification, true conclusion after a repair.** Khoruzhii's identity, which is Sra's (CR), is *not* a coarsening of B.2; it is a different identity. It is inside a natural enlarged class: crossing identities whose certified bond boxes cover the circle arc. Theorem W holds for that class with the same proof [R]. |
| 3 | Class §5.1: sums and regrouping of terms, Ψ_N combined across N (1(b)) | **Correct**, with the natural certified cost of a sum (direct-sum network) [R]. Covers that are not trees of moves are outside. |
| 4 | "Increase bits" on a leg wire; hub identified with a leg | **Minor gap, repaired.** As written, either move breaks the bit count at the legs used in (S2). Both are equivalent to moves that keep the invariant, at no extra leaf cost [R]. |
| 5 | Accumulation of ε, "any depth" (attack 3) | **Gap as written.** The displayed inequality of Theorem W is correct, but Lemma 5.2's ε is at least κ′ ≈ 2.6 bits per crossing. So "any depth" does not follow for branches with ≳ λ crossings. **Repair:** the exact per-crossing loss is 0. This is [N] exhaustively for all class energies ≤ 300, and on a grid up to energy 1200; for larger energies it is [D] (sketch via Hardy–Ramanujan). With it, Theorem W has no error term at all. |
| 6 | **Lemma S** | **Correct** [R]. The weighted two-bimedian inequality holds with equality of all cross terms (§2). The degenerate cases (i), the end-sharing cases (ii) and the normalisation (iii) are all fine. Numerics: no violation in 650+ instances in ℝ², ℝ³ and trees, and many tight cases. The same test finds violations (gap −0.59) in the ℓ¹ and ℓ^∞ planes, so the test has power and the lemma really uses curvature. |
| 7 | Leaf step (S2), multi-group merges, L, H_k, δ_k (attack 2) | **Correct** [R], with the invariant of item 4. These are exactly the quantities of `notes.md` §2. |
| 8 | Theorem W's projection step | **Minor gap:** projections onto closed convex sets need completeness, while Lemma S is stated without it. Pass to the completion. Not needed at all once item 5's zero loss is used. |
| 9 | "No count of terms", the rank-one extreme (attack 4) | **Correct and not vacuous.** The class contains no move that produces bond-free pieces; circle covering is the operative hypothesis. The theorem is tight on the rectangle (App. B attains it). |
| 10 | Consistency checks (attack 5) | All inequalities point the right way. |
| 11 | Cost table §1.2 (attack 6) | Row "four different groups" **[X]**: S = p+q+min(p,q), not p+q+2min(p,q); §2.2's "≥ 1+1/√2" should read 3/2 at p = q. The LP code (`game1.py::consts`) computes S correctly, so no number in §2 changes. The other rows are verified. The true ranks of Ψ_N are below their certificates. |
| 12 | Two-sided cuts lemma §1.3 | **Minor gap:** it omits the three-node case (a triangle of the net, which exists in every group). Its consequence (all edges are merge-class) survives [R]. |
| 13 | Level-1 LP table (attack 7) | **Reproduced** with my own LP: 0.569036 (K₄, w = (½,½,0)) = (2+√2)/6; 0.695399 (AG(2,3), uniform w); also 0.603553 and 2/3 [N]. |
| 14 | Corollary for F₂^m nets | **Survives in the certified form, given the Q1 placement** (§6). |

---

## 1. Attack 1(a): what is bounded — certified costs, not tensors [R]

§5.1 defines the leaf cost as the min 0-extension (5.1) of the derivation's wire system, and states
c_k(t_leaf) ≤ cost_k(W_leaf) (push-forward along π). That inequality is correct, and it is an **upper** bound on the
true D1 cost of the leaf tensor. Theorem W proves a lower bound on cost_k(W_leaf). Hence:

- **What is proved:** for every crossing-generated tree and every CAT(0) placement, some leaf has
  **certified** cost ≥ λ(L − H_k)/δ_k under every merge k (minus the ε term, see §3).
- **What is not proved:** anything about c_k(t_leaf), the D1 cost that `ports/c1d1` D1.1 and `attain-notes.md` §1.1 use in
  the level value. An engine that runs these covers pays c_k(t_leaf), which may be smaller.

This is not a hypothetical gap. Exact ranks from `refW/psi_ranks.py`, with classes (n,e) = (2,12) and (2,12), Θ = 48, dimension 5:

| N | 2 | 4 | 6 | 8 | 10 |
|---|---|---|---|---|---|
| true rank of Ψ_N across ad\|bc | 3 | 7 | 11 | 16 | 21 |
| certificate (N+1)P(N), capped at 25 | 6 | 20 | 25 | 25 | 25 |

The true ranks are below the certificates, and they reproduce `ports/protocol/notes.md` §1.3 independently. The third cut
is also below its trivial bound at the middle term: rank of Ψ_24 across ac|bd = 15 < 25. Likewise for (1,6),(1,6):
Ψ_12 has rank 6 < 9.

Beyond single Ψ_N, the D1 cost minimises over *all* networks on the groups. A leaf tensor, a product and composition of
many pieces, may have a network cheaper than its derivation's.

**Repaired statement.** "Every crossing-generated cover, *with costs certified by its derivation* (rank certificates
of the crossing identities, Lemma A.3 networks, routing, nesting), has a term of certified cost ≥ … under every merge."

This is a barrier for a **proof method**: any engine analysis whose cost bounds come only from these certificates
cannot certify a value below F_CAT. It is not a barrier for the tensors. Combining Theorem W with true costs would need
a lower bound on D1 costs. The only known such tool is the price method, which needs the placement to be a price, and
then Theorem W is not needed.

The text that must change:
- §0, row "Theorem W": it says "with certified costs"; this is fine, but the row "Floor for the crossing-generated family" omits it.
- §5.3, "Consequences 1–3": "level value" must become "certified level value".
- §6: "crossing-generated covers of every depth are stuck at exactly 1/√2" must say certified.
- The corollary in the brief.

§5.3 "What the theorem is and is not" already says that "true ranks below the certificates" are outside the class. But
the gap is wider than true ranks of the Ψ_N: it is the D1 cost of the whole leaf tensor.

## 2. Lemma S [R]

I re-derived the proof line by line.

**Threshold as a supremum.** For o = o′ the child is ≥ parent pointwise, by the triangle inequality. So the child
value with bond r is ≥ v iff r·|oo′| ≥ N₁ for all configurations with o ≠ o′. Hence r_c = sup N₁/|oo′| (its positive
part), the threshold itself is admissible, and r_c ≤ p+q (since N₁ ≤ p|a¹c¹| + q|b¹d¹| − legs ≤ (p+q)|oo′|). This needs
no attained infimum, no compactness and no properness. A point "at infinity" never occurs, because X is a metric
space; far legs only enter placements through limits (§6).

**Step (i).** In a CAT(0) space, t ↦ |γ_t(x,x′) γ_t(y,y′)| is convex (C.4(a)), also when some endpoints are fixed.
`rest` is a positive combination of such terms.

**Step (ii) with shared ends.** Every party y of the parent gets one interpolated position γ_t(pos¹(y), pos²(y)), and
the crossed wires' ends use the same positions. So a = b (shared hub), a = d, parallel wires (a = b and c = d), or a
crossed wire that is a hub–hub bond created earlier all give a consistent parent configuration. The parent inequality
rest(pos^t) + p|a^tc^t| + q|b^td^t| ≥ v holds by the definition of v. ✔

**Step (iii)** pairs a with (o, w), b with (o, w′), c with (o′, w′) and d with (o′, w). These are the correct partners in the
two children. ✔

**Step (iv)** is the triangle inequality. ✔

**The weighted two-bimedian inequality.** I proved it directly. With β_x = γ_t(o,w), β_v = γ_t(o′,w′), β_y = γ_t(o,w′),
β_u = γ_t(o′,w), apply the weighted CN inequality |zγ_t(x,y)|² ≤ (1−t)|zx|² + t|zy|² − t(1−t)|xy|²:
- once from β_x to the segment [o′,w′],
- then from o′ and from w′ to the segment [o,w],
- and likewise for |β_yβ_u|².

The result is (1−t)²|oo′|² + t²|ww′|² + t(1−t)(|wo′|² + |ow′|² − |ow|² − |o′w′|²) for the first term. The second term is
the same with the bracket negated. The sum is exactly 2(1−t)²|oo′|² + 2t²|ww′|². So `notes.md` Prop. 3.1 is not even
needed, only CN. ✔

**Final step.** Λ(1−t) = λ₁ and Λt = λ₂, so Λ²[(1−t)²|oo′|² + t²|ww′|²] = a₁² + a₂². Then a₁r_c + a₂r_b ≤ √(2(p²+q²))|a|
for all a ≥ 0, which gives the circle. The case a₁ = 0 gives t = 1, and the interpolation is configuration 2. ✔

**Normalisation (iii) of the brief.** In VP-paper B.3 the units are κ√n₀ nats, the bonds satisfy r² + r′² = Θ/n₀, and
Θ = 2(e₁+e₂). With p = log₂|Σ₁| ≤ κ′√e₁ (κ′ = κ/ln 2), this gives 2(p²+q²) ≤ κ′²Θ. That is the radius of the certificate
curve N ↦ (κ′√(Θ−N), κ′√N). So Lemma S's circle and B.2's circle are the same circle. What Theorem W needs is: one N
whose certified pair (b_c(N), b_b(N)) dominates (r_c, r_b) coordinatewise. That is Lemma S together with §3. ✔

**Numerics [N]** (`refW/lemS_test.py`): gap = 1 − (r_c²+r_b²)/(2(p²+q²)); bisection tolerance 10⁻⁶.

| space | instances | min gap | gap < 10⁻³ (tight) | gap < −10⁻⁴ |
|---|---|---|---|---|
| ℝ² | 150 | −2.5·10⁻⁷ | 16 | 0 |
| ℝ³ | 100 | −4.7·10⁻⁷ | 16 | 0 |
| star tree, 3–4 arms (exact) | 253 | −3.7·10⁻⁷ | 70 | 0 |
| ℓ^∞ plane (not CAT(0)) | 120 | **−0.588** | 38 | 2 |
| ℓ¹ plane (not CAT(0)) | 120 | **−0.584** | 31 | 1 |

All five shapes (generic, shared hub, hub–hub bond, parallel, a = d) occur at least 18 times in the tree runs, with no
violation.

The ℓ^∞ violation (`lemS_norm.py`, seed 7): p = 0.511, q = 1.219, thresholds r_c = 1.599, r_b = 1.73 = p+q. Both
children need nearly the trivial bond. So in normed planes the Steiner crossing inequality fails, and the curvature
input is essential.

## 3. Discretisation and accumulation (attack 3)

**Lemma 5.2 [R].** The proof is correct as written. Every step checks: 2(p²+q²) ≤ κ′²Θ; the choice N = min(Θ, ⌈r′²/κ′²⌉);
Θ − N ≥ r²/κ′² − 1; and the deficit bound ε ≤ κ′(1+√N₀) + (p+q)η̄(N₀). But ε ≥ κ′ for every crossing.

**Theorem W as displayed is correct:** cost_k ≥ [λ(L−H_k) − D·Σ_s ε(p_s,q_s)]/δ_k. So is its "in particular" for
**bounded depth**. But nothing bounds the number of crossings on a branch. Nesting does not shrink bonds (a bond is
≈ √(p²+q²) ≥ max(p,q)), so a cover can place λ^{Ω(1)} crossings of λ-size wires on one branch. Then D·Σε exceeds λL,
and the bound is empty. So the claims "any depth", "all depths", "of any depth" in §0, §5.3 and §6 are **not justified
by Lemma 5.2 [gap]**.

**Repair: the loss is exactly 0.** The adversary loses nothing if some N has
min(b_c(N), p+q) ≥ r and min(b_b(N), p+q) ≥ r′ for every (r, r′) on the arc r² + r′² = 2(p²+q²), 0 ≤ r, r′ ≤ p+q. The loss
is monotone in the radius, and p = log₂|Σ₁| ≤ log₂(largest class of energy e₁). So it suffices to check the largest
classes. The (N+1) factor can even be dropped, using only b ≥ log₂P(N).

`refW/disc_loss.py` [N], exact partition counts:
- all 11 175 pairs of even energies 4 ≤ e₁ ≤ e₂ ≤ 300: largest loss 3.6·10⁻¹⁵ bits, i.e. 0;
- grid {4,…,40} ∪ {60, 80, …, 1200}, with and without the (N+1) factor (3 003 pairs, p up to 77 bits): loss 0.

**Why there is slack asymptotically [D, sketch].** Put F(E) = log₂²((E+1)P(E)). A sufficient condition is
F(Θ−N) + F(N−1) ≥ 2(p²+q²) for all N. By Hardy–Ramanujan:
- log₂((E+1)P(E)) = κ′√E + ½log₂E + O(1);
- the largest class of energy e has log₂ = κ′√e − (5/4)log₂e + O(1), since the Durfee-size distribution has width
  ~ n^{1/4} around p(n).

So the left side exceeds κ′²(Θ−1) by order √Θ·log Θ, while the right side is below κ′²Θ by order Σ√e_i·log e_i. Making
this rigorous needs explicit error terms in Hardy–Ramanujan, which is routine.

**Repaired Theorem W.** With the zero-loss lemma, the bound is exactly cost_k(W_leaf) ≥ λ(L − H_k)/δ_k. There is no o(λ),
no diameter D, no dependence on depth or size, and the projection step is not needed (see item 8). Until the lemma is
proved for all energies, state it as: "zero loss [N] for all classes of energy ≤ 1200 (exhaustively ≤ 300); hence exact
for covers whose crossings use such classes; for larger classes, loss ≤ ε(p,q) per crossing, Lemma 5.2". Alternatively,
"exact, given the zero-loss lemma [D]".

**Projection step (item 8).** In an incomplete CAT(0) space, nearest-point projection onto a closed convex hull may not
exist. Pass to the completion, which is CAT(0) and has the same Steiner values by density. The hull of the legs has
diameter ≤ D, because closed balls are convex. Correct after this remark.

## 4. The class of covers (attack 1(b), 1(c)) and the leaf step (attack 2)

**Khoruzhii and Sra [X as justified; true after repair].** §5.1 says "Coarsenings such as Khoruzhii's two pieces are
covers by sums of the Ψ_N", and §5.3 lists "Khoruzhii's two-piece form (a coarsening), Sra's Lemma 4.2 nesting" as
inside. This is false. Sra's (CR) is "the integral crossing lemma of Khoruzhii (2026, Lemma 1)"
(`hx/pdf/2611.01066.txt`, l. 70). Khoruzhii's decomposition δ_ikδ_jl = Σ_s (A_s)_ij(B_s)_kl + (C_s)_il(D_s)_kj
(`hx/kh.txt`, eq. (6)) comes from a Fock-space identity, not from the Frobenius-symbol determinant of B.2. Its pieces
are not sums of the Ψ_N.

**Repair [R].** The proof of Theorem W uses only the following property of a crossing identity:

> (Circle covering.) It writes ⟨|Σ₁|⟩_ac⟨|Σ₂|⟩_bd as a sum of pieces, each with certified bonds (ρ_i, ρ′_i) across
> ab|cd and ad|bc. The boxes [0,ρ_i]×[0,ρ′_i] cover the arc {r²+r′² = 2(p²+q²)} ∩ [0,p+q]², up to ε.

Khoruzhii's two pieces have certified bonds (log₂ r, p+q) and (p+q, log₂ r), with log₂ r ≈ √(p²+q²) (r ≤ 2HQ(H+E),
n ≤ Q(H)/2H). Every point of the arc has min(r_c, r_b) ≤ √(p²+q²). So the two boxes cover the arc, and the adversary
takes R when r_c ≤ log₂ r and C otherwise. Whether the lower-order terms of Khoruzhii's counts give zero loss I did not
check; I do not have his count Q. Sra's Lemma 4.2 crosses two hub–hub bonds (the U_α⊗V_α and X_β⊗Y_β factorisations are
A.3 networks) with this identity, so it is inside the enlarged class. Note also that Sra's leaves are "rank one across a
transversal cut", that is, two-hub networks, which fits (5.1).

**Sums and regrouping [R].**
- A term that is a sum of leaves t_j, certified by the direct-sum network, has certified cost
  Σ_{GG′} log(Σ_j d^j_{GG′}) ≥ max_j cost_k(t_j), plus at most log(#j) bits on a spanning tree if the supports are
  disconnected. So grouping never lowers the certified cost below the adversary's leaf.
- Σ_{N∈S}Ψ_N realised with one cut has bond log Σ_{N∈S}(rank certificate) ≥ b(N) for each N ∈ S. It is inside "certified
  bonds or larger", and the adversary's N selects it.
- What is excluded: identities that are not trees of moves, and covers mixing tree terms with arbitrary other terms. The
  adversary may be forced into one of the latter.

**Invariant at the legs (item 4) [gap, repaired].** (S2) needs the wires at each leg to carry exactly λ bits. Two allowed
moves break this:
- "increase bits" applied to a wire at a leg;
- Lemma A.3 with a hub identified with a leg.

Both are equivalent to keeping the invariant:
- A leg wire (ℓ,y;M) with M > λ: (A⊗id)⟨2^M⟩ is a restriction of ⟨2^λ⟩_{ℓz}⟨2^M⟩_{zy}.
- A hub merged into leg ℓ is a restriction of an aux party z joined to ℓ by a λ-bit wire. Party z applies ℓ's map; ℓ reads.

With π(z) = π(ℓ) the leaf cost does not change, and v is unaffected. So normalise covers this way. The text "a leg is
never used as a hub" should be extended to "and leg wires are never enlarged; route through an auxiliary party first".

**Leaf step (S2) [R].** Put each aux party y at o^k_{π(y)} for an optimal π.
- An aux–aux wire has length ≤ δ_k·[π(u)≠π(v)].
- A leg–aux wire has length ≤ |ℓ o^k(ℓ)| + δ_k·[π(ℓ)≠π(y)].
- A leg–leg wire is bounded by both legs' hub distances plus δ_k.

With λ bits per leg, the sum is λH_k + δ_k·cost_k. This holds for any number of groups and any assignment of hubs to
groups. L, H_k and δ_k are exactly those of the price value b_k = (L−H_k)/δ_k in `notes.md` §2. ✔

The level value then follows: max_i min_k cost_k ≥ λ·min_k b_k (one placement), and ⟨w, c⟩ forms by choosing placements.

**Other realisations.** The single hub, the third cut ac|bd with 2min(p,q) bits, and the trivial bonds p+q never lower v,
by the triangle inequality (and r_c, r_b ≤ p+q). I found no certificate-based realisation of a Ψ_N outside these: the
certificates are ranks across two bipartitions only. ✔

## 5. "No count of terms" and the extremes (attack 4) [R]

The adversary's argument follows one branch and never counts leaves, so the bound is independent of the number of terms.
This does not clash with the fact that 2^{p+q} rank-one terms give cost 0. A rank-one decomposition is not generated by the
moves: every leaf of a crossing step carries bonds dominating some point of the circle, and the cover does not choose N.
In the enlarged class of §4 the operative hypothesis is exactly circle covering: the boxes of the rank-one decomposition
are {(0,0)} and do not cover the arc.

The theorem is not vacuous. On the two-merge rectangle the flat orthogonal-simplex placement (Euclidean, hence CAT(0))
gives 1/√2, which App. B's covers attain.

## 6. Consistency checks (attack 5)

- **Rectangle:** bound 1/√2, App. B attains 1/√2. ✔
- **K₄:** level-1 value 0.5690 ≥ every certified lower bound (floor 0.4714). ✔
- **K_{2,3}:** the analogue of Theorem W there would say that crossing-generated protocols have rate ≤ inf over CAT(0)
  placements of the cut-type ratio, which is 3/√10 = 0.9487 by Lemma H_m. The explicit level-1 protocols have rate
  0.8367 < 0.9487. Constructions sit on the "worse" side of the CAT(0) quantity in both games (rate ≤ bound there,
  cost ≥ bound here). The direction is consistent. ✔
- **Δ₃:** "≥ 2/3" uses the nine-tripod placement, a product of trees, hence CAT(0). This is legitimate without the price
  hypothesis, in the certified form. ✔

## 7. Cost table §1.2 and the level-1 LP (attacks 6, 7)

**Table.** I recomputed every row by enumerating hub groups for the realisations single hub, cut c, cut b and cut ac|bd
(`refW/lp1.py::realis_consts`).
- Rows 1 (a∼b, c∼d: min(r, p+q)), 2, 3 (a∼b only: min(p+q, min(p,q)+r, 2min(p,q)+r′)), 4 and 6 (a∼c, b∼d: 2min(p,q))
  are correct.
- **Row 5** (four different groups) is **[X]**. The single hub at the group of a costs q+p+q, and at b's group p+p+q, so
  S = p+q+min(p,q). The correct entry is min(p+q+min(p,q), 2min(p,q)+min(r,r′)), not min(p+q+2min(p,q), …). At p = q and
  θ = π/4 the third-merge cost of a rectangle piece is 3p = 1.5 per bit, not 2+√2 = 3.41p. So §2.2's "(1/√2, 1/√2,
  ≥ 1+1/√2)" should read "(1/√2, 1/√2, 3/2)".
- Nothing downstream changes. §2.2 only uses "≥ raw", and `game1.py::consts` computes S as a minimum over hub groups, so
  the LP was right.

**True ranks [R]** (`refW/psi_ranks.py`): the identity (a), deg Ψ ≤ Θ and the certificates (b), (c) hold exactly for
(1,6,1,6), (2,12,2,12) and (1,8,2,14), with no violations. For the two-group rows (1, 2, 6) the true D1 cost is the
log-rank of the flattening, which is at or below the certified entries (§1).

**LP [N]** (`refW/lp1.py`: own constraint generation, θ grid of 100 001 points, which gives lower bounds to ~10⁻⁵):

| level | w | mine | notes |
|---|---|---|---|
| K₄ | (½,½,0) | 0.569036 | 0.569036 = (2+√2)/6 ✔ |
| K₄ | uniform | 0.666664 | 0.666667 ✔ |
| AG(2,3) | uniform | 0.695399 | 0.695399 ✔ |
| AG(2,3) | (½,½,0) | 0.603553 | 0.603553 ✔ |

## 8. Two-sided cuts lemma §1.3

Two cuts aligned with two merges force every cell into one node, so the support is contained in a rectangle. ✔

For three merges the sign vectors need pairwise distance ≥ 2. This allows **three** nodes (+++, +−−, −+−): a triangle of the
net (two nodes in a row, two in a column, two in a diagonal), which exists in every Latin square. The proof says "at most
four nodes … this is a K₄", which omits this case. The K₄ case, with 2(c−c′) = 0, is correct.

**Repair:** "at most four nodes, pairwise collinear (a triangle, or a K₄, the latter only with 2-torsion); all edges among
them are merge-class edges". The consequence for generic edges is unchanged. The lemma is not used in Theorem W.

## 9. The corollary for 3-nets of F₂^m

**The consumed quantity.** I did not referee the Q1 placement. Its value is exactly the quantity Theorem W consumes
(`q1-notes.md` l. 66): L, H_k and δ_k as in `notes.md` §2, b_k = Σ_e s^k_e/δ_k, δ_k = √2.

**Finite T.** The legs are actual points at finite T (Prop. 2.1: s = 2T+1 − 2√(T²+½)). Theorem W applies at each fixed T.
- With the zero-loss lemma: exactly cost_k ≥ λΣ_e s^k_e(T)/√2 for every T, then let T → ∞.
- With Lemma 5.2 only: fix T, then let λ → ∞, with D ~ 2T fixed, for branches with o(λ) crossings.

**Collinear (rank-one) edges.** They are placed by Lemma 1.4 at finite T, and their finite-T savings, including the
O(1/T) negative savings of the common class, are part of b_k. For q = 2, p = 3 there are no rank-one edges of other slopes
(E_other = 0).

**What survives.** If the Q1 placement stands (filtration space CAT(0), Prop. 2.1, Theorem A), then on the 3-net of F₂^m
(g = 2^m) every crossing-generated cover in the enlarged class has the following property. The class is: B.2 or any
circle-covering crossing identity, Lemma A.3 networks, routing, identification, nesting of any depth, any number of terms,
leg invariant as in §4, certified costs (5.1). The property: some term has **certified** cost

    ≥ λ·E·[(g−2)/(√2(g+1)) + 1/(g+1)] − o(λ)   under each of the three merges at once,

that is, certified level value ≥ 1/√2 − (3/√2 − 1)/(g+1) = 1/√2 − 1.121/(g+1).

The conditions:
- "any depth" needs the zero-loss lemma ([N] up to energy 1200, [D] beyond); otherwise it holds for o(λ/κ′) crossings
  per branch;
- it is unconditional in the sense of no spectral or contracting hypothesis;
- it says nothing about the true D1 costs of these terms.

With the level-1 upper bound (two-merge rectangle value → 1/√2), the certified value of this family is 1/√2 only in the
limit g → ∞. For finite g there is an O(1/g) window between the two bounds: at g = 4, W gives 0.4828 and level 1 gives
0.6243. "Stuck at exactly 1/√2 at every nesting depth" (§5.3 item 2) should read "certified level value
∈ [1/√2 − 1.121/(g+1), level-1 value], both → 1/√2".

## 10. Requested edits to `attain-notes.md`

1. **Theorem W, its consequences, §0 and §6:** say "certified level value" (§1 of this report).
2. **§5.1:** replace "coarsenings such as Khoruzhii's … are covers by sums of the Ψ_N" by the circle-covering class of §4.
   Keep Khoruzhii and Sra inside via that class.
3. **§5.1:** add the leg invariant and its normalisation (no enlargement of leg wires; hubs merged into legs replaced by
   aux parties plus a λ-bit wire).
4. **Theorem W:** either restrict "any depth" to o(λ) crossings per branch, or add the zero-loss lemma with its status
   ([N] ≤ 1200, [D] beyond). With it, drop D and ε.
5. **Theorem W proof:** pass to the completion before projecting (or drop the projection step, given item 4).
6. **§1.2, table row 5:** S = p+q+min(p,q). **§2.2:** third-merge cost 3/2 at p = q.
7. **§1.3:** include the triangle case.
8. **§5.3 Consequence 2 and §6:** O(1/g) window at finite g.

Lemma S itself needs no change. Its proof is complete as written, and the bimedian step needs only CN.
