# Novelty audit, 5 November 2026

What was searched (5 Nov 2026, ~19:00 UTC):

- **Hexagon.** All 716 works (1 Sep – 5 Nov), using the public query API (`/api/query?search_query=all:*&max_results=2000`). Titles and abstracts were grepped for every topic below. The full text of all 181 works since 26 Oct in cs.\*, math.NT, math.CO or quant-ph (excluding our own) was also grepped.
- **arXiv.** The API was searched for ETH, #SAT, tensor contraction, prime counting, Eulerian, class number, non-residue, root finding, quasi-Riemann and deterministic polynomial factorization, for papers since 20 Sep. Full text was read for 2610.41622 and 2611.00517.
- **OpenAI catalogue.** `openai/math` CONTENTS.md at origin/HEAD 4eaee87 (29 Oct), 378 entries.
- **Web.** Searches covered Zenodo, alphaXiv and general web.

## Verdict per result

| Result | Status | Closest prior/parallel work |
|---|---|---|
| Polynomial roots mod p (roots-note) | **Superseded.** Do not submit as is. | OpenAI #142, *Deterministic polynomial factorization over prime fields* (4 Oct 2026): complete factorization over F_p in deterministic time poly((deg f+1) log p). This gives roots mod p in polynomial time. |
| Least root mod composite m | Probably a corollary of known work. | Shunia 2610.00711 factors m in 2^{O(n/√log n)}. OpenAI #142 handles p, and Hensel/root clusters plus CRT handle prime powers. Fixed degree gives at most d^{ω(m)} = 2^{O(n/log n)} combinations. |
| Least quadratic non-residue (classnumber note, 2611.00115) | **Superseded.** | OpenAI #003, *The quasi-Riemann hypothesis* (30 Sep 2026): Dirichlet L-functions are zero-free for Re s > 7/8. By the standard argument the least non-residue is polylogarithmic in p, which gives polynomial time. Our sentence "Burgess is the best unconditional bound" is out of date. |
| Least square root mod m (2611.00115) | Probably a corollary of known work. | Shunia factoring, OpenAI #142 and the 2^{ω(m)} CRT combinations. |
| Class number h(−N), divisor and σ sums, Gauss circle (2611.00115) | No duplicate found. | Vega 2611.00086 (4 Nov) puts h(−d) in FP^{Σ2P}, a different kind of statement. Frei–Sofos–Widmer 2610.18491 apply quasi-RH to class groups but give no algorithm. |
| Parity of π(x) on intervals (2611.00116) | No duplicate found. | Polymath (TCH12) O(x^{1/2−c}). |
| Eulerian circuits (2611.00088) | No duplicate found. | Bhattacharjee 2610.00594 counts Eulerian *orientations*; already cited. |
| Factoring (factoring-note) | Already framed as a second, independent proof. | Rudich–Rousseau 2610.00600; Shunia 2610.00711. |
| Crossover note | **Superseded.** Majdoddin cites our research/crossover.md. | Majdoddin 2610.41622 (30 Oct) cites our 29 Oct crossover.md as [4], checks our numbers and goes beyond them. Also Szeider (Zenodo 23688832, 27 Oct) and Dias–Lima 2611.00517 (31 Oct). |
| Barrier note | **Overlaps; must be repositioned before submission.** | Majdoddin §4 shows every grid algorithm in a rewrite-and-merge class has exponent ≥ 1/log₂K per edge bit (Thm 4.13, Cor 4.19), and that two balanced homogeneous merges give ≥ (log₂K)^{−3}. Dias–Lima prove cost-model limits for OpenAI's interpolation scheme. |
| Circuit note | Not a duplicate; cite. | Wu–Wang 2611.02560 (2 Nov) extends OpenAI's bound to extended gate bases. |
| Survey note | Add citations. | Majdoddin; Dias–Lima; Szeider; MIT Hardness Group 2611.02650 (SH ⇔ Weak ETH); Wu–Wang 2611.02548 and 2611.02560; Nguyen 2611.00004; Li 2610.00613; Vega 2611.00086. |
| Quantum, HC revision | No new overlap found. | — |

## Follow-up (5 Nov, later)

- **Roots.** A fresh `leanchecker --fresh EthFollowup.ModP.FinalRoots` replay exited 0. polyRoot_TM_rate and the related theorems are kernel-checked. The result is still shelved for publication because of OpenAI #142.
- **Non-residues.** OpenAI's quasi-RH preprint (30 Sep) itself states the least non-residue bound n(p) ≤ C(log p)^A and polynomial-time square roots mod p, as its Corollary 1.2. Class-number v2 credits that corollary.
