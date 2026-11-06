# Engine 3: status of the attack on the 1/log K rate (paused 6 Nov 2026)

Goal: a counting mechanism for the clique sum whose exponent per edge bit e(K) decays faster than 1/log K.
Anthropic's recursion squares K per level and gives e(K) = Θ((log K)^{−α′}) with α′ = log₂(1/ρ). So any
level with ρ < 1/2 that plugs into a squaring recursion gives α′ > 1 and e = o(1/log K). That would break the
"dense wall" (permanent beyond Ryser, dense TSP/HC beyond Held–Karp, chromatic number). Polynomial decay of e
would refute the Satisfiability Hypothesis (Stearns–Hunt).

This file is the index. Each note below is self-contained, with exact statements and tags
([R] proved, [N] exact computation, [C] heuristic or conjecture).

## Where it stands

1. **Two merges: closed.** Every level with two merges has ρ ≥ 1/2, whatever the pieces, hyperedge pieces
   included [R]. This is Theorem 1 of `engine3-delta3-proof.md`: uniform quantum functional on the groups,
   subadditivity, then pigeonhole. It extends Majdoddin's two-merge floor (arXiv 2610.41622, Prop. 4.8,
   Thm 4.13) from his rewrite-and-merge class to all pieces, and closes his "open door" for two merges. The
   proof runs over ℂ via CVZ quantum functionals; for other fields it runs via Strassen's support functionals
   (flagged).
2. **Three or more merges: the only door left for α′ > 1.** With p merges the same pigeonhole gives only 1/p.
   The smallest open instance is Δ₃ (three anti-diagonal triangles of the 3×3 grid) with rows, columns and
   diagonals as merges.
   - Floors on that instance: game floor 4/9 (flattening + CVZ + core); pigeonhole 1/3.
   - Small block sizes: ρ < 1/2 is refuted exactly at N₀ = 2 and N₀ = 4 for every number of piece types T
     [N] (`scripts/engine3-delta3-3m/floor_finite.out`, `floor_assign.out`).
   - Larger block sizes: from N₀ = 8 on, the finite certificates no longer refute T ≥ 4 [N]
     (`floor_scaled.out`). The asymptotic question is open.
   - ALS three-merge searches at N₀ = 2 found no identity. Best residual 0.63 with bonds (4,4,4); the others
     are 0.86–0.96.
   - This run was stopped before its note was written; the scripts and outputs are in
     `scripts/engine3-delta3-3m/`.
3. **Polynomial decay** needs configurations of growing arity, Ω(log K/log g) nodes [R]
   (`engine3-open-door.md` §1.10). The trade must sit on "two-cell" edges routed along the incidence graph.
   - On the smallest instance, the incidence 8-cycle, flattenings certify only 9/12 on the two-cell edges, so
     they cannot forbid a trade [N].
   - Every two- and three-term identity there is excluded exactly at N₀ = 2 [N] (`engine3-cycle8.md`).
4. **OpenAI's mechanisms** are single-level, with caps of a different nature from Anthropic's. No route to
   o(1/log) is visible in them (`engine3-openai-route.md`).
   - The D.1 2-adic decomposition lands exactly on the flattening floor N⁴ at K₄ (`engine3-p3.md`).
   - On clause-product designs, a new (ρ+1)-minor lemma proves R/Q ≥ const at any fixed number of groups
     (`engine3-p2.md`).
   - The r ≈ √n regime, where a 2^{Õ(√n)} design is not excluded, remains open.

## Results worth keeping (candidate material for a paper)

**Proved [R]:**
- Theorem 1: ρ ≥ 1/2 for all two-merge levels, arbitrary pieces.
- Core-floor theorem: ρ ≥ max over cores H of E_cross(H)/E. This closes Majdoddin's configuration C, every
  two-lines configuration, and (together with exact flattening certificates) the AG(2,4) instances he names.
  It answers his Open Problem 4 and the non-product part of Open Problem 5 at those instances
  (`engine3-open-door.md` §2.3–2.7).
- Theorem 2: diagonal pieces admit no trade, so ρ = 1 on that class (Loomis–Whitney, every field)
  (`engine3-delta3-proof.md`).
- Theorem A: pieces that are products over the three triangles of Δ₃ admit no trade, ρ = 1 (9-party CVZ). The
  Cohn–Umans / STPP route is one-sided (`engine3-delta3-cohn-umans.md`).
- (ρ+1)-minor lemma for OpenAI-type clause-product designs (`engine3-p2.md` §4).
- Growing-arity proposition for polynomial decay (`engine3-open-door.md` §1.9–1.10).

**Exact computations [N]:**
- 8-cycle certificate D₈ = 13/20, two-cell part 9/12.
- Δ₃ flattening floor 4/9 for every block size.
- Exact refutations of all small identities on C, Δ₃ (two and three merges at N₀ ≤ 4) and the prism.
- The K₄ D.1 cost is exactly N⁴.

**Corrections recorded:** the trade criterion is Definition 7's accounting (naming per direction, piece
types); the first version wrongly let Strassen "trade" (`engine3-open-door.md` §1.7, erratum).

## Notes, in reading order

| file | content |
|---|---|
| `engine3-literature.md` | literature: Zhou 2026 (rank route closed: asymptotic rank of K_n = flattening floor), CVZ, ARC, SOS composition, Curticapean's (2−ε)^n permanent |
| `engine3-open-door.md` | exact formulation; core floor; design principle; arithmetic of ρ → e(K); growing arity; corrected criterion |
| `engine3-search.md` | first search on C: non-local terms pass the k-local barrier by a constant factor only |
| `engine3-openai-route.md` | OpenAI interpolation and Theorem D.1 rate analysis; proposals P1–P4 |
| `engine3-p2.md`, `engine3-p3.md` | P2 (clause-product designs) and P3 (D.1 pieces at K₄): negative |
| `engine3-delta3.md`, `engine3-delta3b.md` | Δ₃, two merges: exact negatives at N₀ = 2, 4 |
| `engine3-cycle8.md` | 8-cycle and prism: certificates and exact negatives |
| `engine3-delta3-cohn-umans.md` | group-algebra route; Theorem A |
| `engine3-delta3-proof.md` | Theorem 1 (two merges ⇒ ρ ≥ 1/2), Theorem 2, straightened-edge family |
| `scripts/engine3-delta3-3m/` | three-merge Δ₃ (stopped; floors and ALS outputs, no note yet) |
| `scripts/engine3-pmerge/` | p-merge floor theory (stopped early; entropy and rank LPs, no note yet) |

## Next steps when resumed

1. Three merges on Δ₃ at block size N₀ ≥ 8. This is where the finite certificates stop working.
   - Either prove a game floor of 1/2 for p ≥ 3 merges, which would close the α′ > 1 door completely and make
     1/log K optimal for all grid levels.
   - Or search structured many-piece identities there, seeded by the CKSU degree-2 pieces and the
     straightened-edge family.
2. Write Theorem 1, the core floor and Theorems A/2 into the barrier paper (package `09-barrier`) as a new
   section, before it is submitted.
3. Polynomial-decay side: a Lemma-4.11-type theorem for two-cell edges (`engine3-open-door.md` §5.5(c)).
