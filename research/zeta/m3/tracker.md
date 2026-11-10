# Tracker continuation (m3, successor of h2) — refresh 10 Nov 2026
Continues h2/tracker.md (do not duplicate; read that first). Tags as there: FACT = primary source read; CLAIM = author's
statement, unchecked; SPEC. Sources polled today: arXiv API (math.NT, simple zeros / critical line / pair correlation /
Montgomery, newest first), Zenodo API (all zeta-zero records 7–10 Nov; full text "Chirre"; "simple zeros" since 15 Oct;
creator Fabbian), Hexagon API (q = zeta, zeros, simple zeros, critical line), riemannzeta.fun, GitHub repo search
(pushed since 1 Nov), rStation paper list.

## 1. New or newly-relevant items
| date | item | link | content | status |
|---|---|---|---|---|
| 15 Sep | Fabbian P1, Thm A/B | zenodo 22778066 | full read: see m3/fabbian.md. Thm B + §4.7(b) = our "Lemma Z" (prior art) | FACT (read), CLAIM (computer part) |
| 7 Oct | Fabbian P2 barriers | zenodo 23198632 | full read: m3/fabbian.md §3 | FACT (read) |
| 29 Sep | Fabbian, optimised Lamzouri inequality, short intervals | zenodo 23027645 | Gram-type S(Z) ≥ x+(|Z|−x)²/N_m; "simple or real" in short intervals conditional on Wang 2609.07918 | CLAIM (abstract) |
| 29 Sep | Fabbian, weight-2 newforms prime level | zenodo 23025218 | C_MT = 0.6725 on harmonic average, no GRH, heights (log N)^η..(log N)^A | CLAIM (abstract) |
| 20 Oct (v1.3.0) | Bhattacharjee–Bhattacharya | zenodo 23489033 | 0.6732896 via ten-consecutive-zero window LP; method cap 0.67357 | CLAIM |
| 2 Nov (v0.02) | Santibáñez-Leal, three-point kernel bound | zenodo 23895875 | proportions withdrawn (depended on withdrawn Wang 2609.24167); ratio theorem kept | CLAIM |
| 2 Nov | J. Singh, conditional 76.7% simple via twisted dispersion | zenodo 23899228; Hexagon 2611.00059 (5 Nov, revised: Z' at close pairs, π²/15) | under RH + a Bombieri–Vinogradov-type conjecture on a bilinear sum beyond θ = 1/2 | CLAIM, conditional |
| 9 Nov | C. Kim, isolated zeros | zenodo 24064967 | ≥ 0.672468 of zeros have both neighbouring gaps > 2πc/log X for c ≤ 1e−5 (refines Lamzouri 0.6552 small-gap) via shifted mollified moment | CLAIM (abstract) — relevant to x2's gap line |
| 9 Nov | B. Lee, signed Fourier multiset / FREE-ABSORB | zenodo 24089689, 24081890 | conditional ≥ 0.5023 "locally isolated" zeros | CLAIM, conditional |
| 10 Nov | L. Kornmann, conditional r-gaps | zenodo 24095120 | RH + resonance method, small/large r-gaps for a positive proportion | CLAIM (abstract) |
| 6 Nov | Cruañas Pardo; 8–10 Nov R. Mori ×6 | zenodo 24020195; 24047155–24086959 | smallest eigenvalue of windowed Weil forms ~ e^{−4πX} (RH); "rigidity ⇔ simplicity" | CLAIM; not proportion results |
| 9 Nov | D. Hess, three-point correlation numerics IV | zenodo 24094318 | R3 vs Conrey–Snaith ratios formula on 1.47e8 zeros | CLAIM (numerics) |
| 9 Nov | riemannzeta.fun | riemannzeta.fun | record still 67.3638876665% (Knausgård 9 Nov 14:31); no entry > 0.674; none CGdL-type | FACT (site) |
| 9 Nov | n0zer0d4y/simple-zeros-hilbert-robin-epstein (GitHub) | github | 0.672724 refining Wang (withdrawn inputs); MV constant > π+1.19e−3 | CLAIM |
| 6 Nov | reggaesharkk/riemann-bandwidth1-verification | github / zenodo 23244818 | ">79%" explicitly OPEN; 68.82% conditional | CLAIM, self-declared open |
arXiv: no new item on proportions of simple/critical zeros since 2611.05000 (3 Nov); latest math.NT hit 2611.10726
(RH criterion, 7 Nov, unrelated). Hexagon: nothing on proportions since h2's pass except 2611.00059 above.

## 2. Prior-art verdicts (task from lead)
- Lemma Z: **prior art = Fabbian P1 Thm B + Rem 4.7(b)** (cleaner: exact weight removal, T-independent (C)); cite it.
- 0.677610 (h3 explicit kernel) and 0.67585 (h5 mixture): **not found** in any source polled (details m3/fabbian.md §5).
- Unconditional CGdL-type statement at all depths: nobody claims it; Fabbian states it as Conjecture 10.3 (open).

## 3. Hunches update
- H13 (Fabbian P2 §11): escapes = inhomogeneity in pair mass; exact first-shell treatment; non-fixed charges. SPEC by author.
- H14 (m3 [C]): every Fabbian witness that excludes a proof class for g_A also excludes it for the MT kernel, whose (C) is
  true (Lamzouri). So the only mechanism known to prove (C) at all depths is rank/inertia; a CGdL-type all-depth proof
  likely needs to route the deep-pair part through an inertia argument (e.g. via the mixture with MT). Untested.

## 4. Not reachable / not read
X, Lean Zulip; rStation post bodies; GitHub API for unattached repos (READMEs via raw only); Devine 22066689 text.
