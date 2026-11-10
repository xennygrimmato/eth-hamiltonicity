# Tracker (h2): work and discussion on "beyond 2/3" for zeta zeros — last refresh 10 Nov 2026 (two passes)

Companion to `h2/novelty.md` (full tables, citations, theorem numbers). Tags: **FACT** = read in the primary source
today; **CLAIM** = stated by its author, unrefereed, not checked by us; **SPEC** = speculation (theirs or mine).

## 1. Timeline of work since Aug 2026 (one line each)

| date | item | link | content | status |
|---|---|---|---|---|
| 10–11 Aug | Anthropic post + Claude preprint | anthropic.com/research/riemann-zeta ; www-cdn.anthropic.com/564f962e…pdf, …95c24693…pdf | 2/3, 0.6725; Remark 1.1: ceiling 0.68185; 0.70/0.80/0.90 need form factor on support 1.04/1.26/1.70 | FACT |
| 11–13 Aug | ainta, tawanerguo-cn, trmdy/Y. Shi, AMTOPA (GitHub/Zenodo) | github.com/ainta/zeta-simple-zeros etc. | first "stability refinements": inner products of zero vectors are K(γ−γ'), so the orthogonal extremal of rank–trace is not realisable; 0.67300–0.67341 via k-consecutive-zero inequalities | CLAIM |
| 13 Aug | Alpöge–Furman arXiv:2608.13637 | arxiv.org/abs/2608.13637 | Thm A, B; Remarks: ξ' 0.858/0.869, family average 0.811/0.905 (no proof), HL*(4) ⇒ 13/18 | FACT |
| 17 Aug | Yang–Yang, Zenodo 21975237 | doi.org/10.5281/zenodo.21975237 | "0.7962" from trace moments ≤ 6 | CLAIM; conflicts with A–F §7.2(e); treat as wrong until shown |
| 17–18 Aug | Hua–Yang arXiv:2608.16034, 2609.27808 | arxiv | prime-modulus family, heights near-microscopic to polylog; constants unchanged | FACT |
| 30 Aug–18 Sep | K. Singh, Zhaoyi-Tian (Lean), Gebendorfer ×3, Rakitin, Freund PR 888, Schäfer, Chandru | Zenodo / GitHub | 0.67345–0.673492; Gebendorfer: "periodic-mixture obstruction" | CLAIM |
| 2 Sep | Lamzouri arXiv:2609.02882 | arxiv | Hilbert-space reproof; simple-or-on-line 0.88762 | FACT |
| 7 Sep | Wang arXiv:2609.07918 | arxiv | short intervals | FACT |
| 21 Sep | Wang arXiv:2609.24167 | arxiv | +6.7e-8; **withdrawn 6 Oct** | FACT |
| 27 Sep | Knausgård arXiv:2609.33043 | arxiv | distinct 0.83699 (clipped matrix inequality) | FACT |
| 1 Oct → | riemannzeta.fun ("Riemann.fail") Lean leaderboard | riemannzeta.fun ; github.com/josusanmartin/riemann | 51 kernel-checked records, 0.67285 → **0.6736389** (9 Nov, Knausgård refining Bei Yi) | FACT (site) |
| 3 Oct | D'Souza release v1.0 | github.com/Oliverds321/simple-zeros | ζ: simple 0.6752 (Lean), distinct 0.8376; family q ≤ Q: 0.7235 unconditional, 0.9059 given Jutila + Montgomery density estimates | CLAIM (Lean statements exist; not rebuilt) |
| 6 Oct | Knausgård arXiv:2610.08965 | arxiv ; github.com/kristianmk/839 | 0.673538 / 0.839005 / 0.889315; ceilings 0.67383 (simple-points interaction), 0.68185 / 0.84093 (any window) | FACT |
| 9 Oct | Aryan arXiv:2610.12853 | arxiv | imaginary-part identity; "clustering barrier" analysis | FACT |
| 15 Oct | Tyagi, Hexagon 2610.00252 | hexagonmath.org/abs/2610.00252 | finite model: half-bandwidth cubic trace is "absorbed" (no gain) | FACT (abstract) |
| 16 Oct | Cobeli–Zaharescu arXiv:2610.23467 | arxiv | > 8/9 simple or on line | FACT |
| 16 Oct | Angón–Ross–Tang–Zhao arXiv:2610.22927 | arxiv | consecutive moderate gaps | FACT |
| 17 Oct | Arias de Reyna arXiv:2610.24612 | arxiv | human exposition | FACT |
| 19 Oct | Lamzouri arXiv:2610.26841 | arxiv | 13/20 isolated zeros; 31% for combinations of two L-functions | FACT |
| 19–20 Oct | Bondarenko–Heap 2610.26038; Durkan–Pearce-Crump 2610.28527 | arxiv | small gaps ≤ 1/2 (RH; unconditional for Dirichlet L, infinitely often) | FACT |
| 3 Nov | Baluyot–Conrey–Irfan–Snaith arXiv:2611.05000 | arxiv | long Dirichlet polynomials of (ζ'/ζ)^k, conditional | FACT |
| 5 Nov | rStation paper 109 | rstation.ai/problems/riemann_hypothesis/papers/109 | "Off-line zeros of any depth can be hidden from the two-thirds pair-correlation certificate" | CLAIM (title/abstract only) |
| ongoing | GettysburgResearch/riemann (Agentic Polymath); elCanosail/riemann-conjecture; teal-sea/zeta-lab; zach7036 | GitHub | barrier maps; no result beyond the above | CLAIM |
OpenAI catalogue: nothing on this problem (003 quasi-RH is unrelated; see novelty.md §3). Anthropic repo:
`anthropics/formal-math/zeta23` (also `anthropics/zeta-23-lean`); no follow-up theorem found there.

## 2. Hunches: how to go beyond, or why it is stuck

Forums searched today: MathOverflow, Mathstodon (Tao), Reddit r/math and r/slatestarcodex snapshots, Lobsters,
news blogs. **Finding: no technical hunch by Tao, Radziwiłł, Buzzard, Turnage-Butterbaugh, Alpöge or Furman was
found in public forum posts** (Tao's relevant public statements are about "proof digestion", not the mathematics;
Reddit/Lobsters threads are non-technical; X and Lean Zulip are not indexed by the tools available — not
searched, **unverified**). The technical hunches are in papers and repositories:

| # | who / where | idea (two sentences) | assessment |
|---|---|---|---|
| H1 | Claude–Alpöge–Furman, arXiv:2608.13637 Remark 7.2; D'Souza family paper | Average over primitive characters q ≤ Q: the large sieve keeps the prime-side diagonal dominant up to X ≤ Q^{2−ε}, so the admissible bandwidth grows from 1 to 3/2 (smooth weights kill the Farey spoke 1/q) and beyond with a "shell" kernel. Claimed constants 0.7235 (proved in Lean per author), 0.811 (stated, no proof), 0.9059 (given two density estimates). | FACT that the mechanism is standard (Özlük, CLLR under GRH). **Most promising route to a clean new theorem**: a complete proof of ≥ 0.81 without density hypotheses, or other families (dyadic q, prime q, real characters, GL(2)), is unclaimed. Risk: D'Souza's unrefereed work may already contain most of it. |
| H2 | Aryan, arXiv:2610.12853 §3.2–3.4 | The 2/3 argument survives even when clustering cancels all negative spectral mass B of the off-line part; to go beyond one must prove B cannot vanish. His new imaginary-part (odd-kernel) identity is a sign-sensitive statistic that might see the arrangement of positive/negative directions. | SPEC by the author ("we do not pursue"). Interesting because it is new *unconditional* data from primes ≤ T. Caveat (mine): the 0.68185 ceiling is realised by on-line configurations, so off-line information alone cannot pass 0.6819 unless the new statistic also constrains on-line multiple/close zeros. Worth a small-case test. |
| H3 | A–F §7.2(d)–(f); Claude preprint Remark 1.1 | With k trace moments the sharp bound is a Chebyshev–Markov–Stieltjes/Christoffel-function bound; unconditionally tr G^k is known only for X^k ≤ T^{2−ε}, so at X ≈ T only k = 2. Form factor on support 1.04 would already give 0.70; HL*(4) gives 13/18. | FACT (as stated in the paper). The needed extra support is tiny (4%) — any unconditional one-sided information on F(α), 1 < α < 1.04, or a third trace at *reduced* bandwidth 2/3 mixed with the second at bandwidth 1, would break the ceiling. But see H6: the cubic term at half bandwidth appears to give nothing. |
| H4 | Chirre–Gonçalves–de Laat (2020); raised again by A–F ("a regime the present method does not enter"); h1's note on the board | Under RH, F(α) ≥ 0 for |α| > 1 lets one use kernels with negative Fourier transform outside [−1,1] (0.6792). BGST Thm 1 states F is nonnegative unconditionally for the complex-zero form factor. | SPEC: transferring this needs the zero side to be read positively, which is exactly what fails off the line; in the Gram formulation K̂ = ψ*ψ ≥ 0 is forced (h1). Payoff capped at 0.6792 < 0.68185, but that would still beat 0.6736. h4 (T2) owns this. |
| H5 | ainta; Knausgård 2610.08965 §1, §7; Gebendorfer | Zero vectors are not free: ⟨v_γ, v_γ'⟩ = K(γ−γ'), and N points at density 1 must interact; a local k-point inequality gives extra energy linear in the number of simple/double points. Ceilings: 0.67383 for simple-point interaction, 0.68185 for any window (law of period 256). | FACT. This line is nearly exhausted (0.67364 vs 0.67383 for the simple scheme; 0.6818 overall); gains require much heavier certificates. Not a good use of effort. |
| H6 | Tyagi, Hexagon 2610.00252 | In a finite circle model, adjoining a half-bandwidth signed cubic trace to the two-moment data does not change the optimum (exact absorption) in the atom-only class. | CLAIM, finite model only. Suggests the unconditional third moment (bandwidth ≤ 2/3) is useless — consistent with elCanosail's estimate "tr G^3 → ~0.676" being optimistic. Would be worth confirming by h3's LP. |
| H7 | Lamzouri 2609.02882 (remark on BGST Thm 3(iii), "observation of Soundararajan"); 2610.26841 | Simplicity and horizontal position are rigidly linked: (N_s+N_0)/2 ≥ 0.836 and simple-or-on-line ≥ 0.888; isolated zeros (gaps both sides > c) are automatically simple and on the line, 13/20 of zeros. | FACT. Suggests a different target: mix gap statistics (unconditional moderate-gap proportions) with the certificate. Proportion gain unclear. |
| H8 | elCanosail/riemann-conjecture README; Reddit/Lobsters commenters | "Information barrier": 2/3 is optimal for (tr G, ‖G‖²) at bandwidth ≤ 1; breaking it needs RH-type pointwise integrality (0.68185), Hardy–Littlewood (bandwidth > 1), trilinear Kloosterman improvements, or a hybrid mollifier + pair correlation ("redundant under RH, incompatible without"). | CLAIM by an AI-assisted amateur repo; items 1–3 agree with A–F and Knausgård, the hybrid verdict is unargued. |
| H9 | Goldston et al., survey arXiv:2511.20059 (Feb 2026 version) | "Not assuming RH is not enough; you have to take seriously the possibility that RH is false" — the box hypothesis results; PCC ⇒ 100% simple and on line without RH (GLSS). | FACT (background). Implies: any unconditional extension of the form factor beyond support 1, even in averaged or one-sided form, converts directly into proportions. |
| H10 | rStation paper 109 (5 Nov) | Off-line zeros of any depth can be hidden from the two-moment certificate. | CLAIM. Consistent with Aryan's extremal picture (off-line pairs spectrally like double zeros). |
| H11 | h2 (mine) | Use ζ and ξ' *jointly*: A–F get 0.869 for ξ' with the same inputs; multiple zeros of ξ are zeros of ξ', and real zeros interlace (Rolle), so a joint Gram matrix / cross pair-correlation of zeros of ξ and ξ' at bandwidth 1 is unconditional data not contained in the ζ form factor on [−1,1]. The extremal configuration for ζ (N/6 double points) forces N/6 common zeros, which the cross-correlation should detect. | SPEC, untested. Check first whether the prime side of the cross term is computable (explicit formula for ξ'/ξ' is not a prime sum — Farmer–Gonek–Lee work under RH via ξ'/ξ; this may be the obstruction). |
| H12 | h2 (mine) | Hybrid with Levinson: the mollifier method certifies ≥ 0.4075 simple critical zeros by sign changes; these are *specific* zeros. If they could be shown to be spread among the "uncertified third", proportions would add. | SPEC; no known mechanism to make the two certificates see different zeros (elCanosail: "incompatible"). Low. |

## 3. Three most promising (posted to the board)
1. H1 families/bandwidth > 1 via large sieve — clean unconditional theorem available; check D'Souza overlap.
2. H3+H2 "new unconditional statistic beyond the bandwidth-one form factor": tiny extra support (1.04) suffices
   for 0.70; candidates: Aryan's odd-kernel identity, cross-correlation with ξ' (H11), averaged/one-sided F(α).
3. H4 importing F ≥ 0 outside [−1,1] (BGST Thm 1 is unconditional) into a Lamzouri-type Hilbert inequality — cap
   0.6792, would be a record if the positivity transfer can be made to work; obstruction stated by h1.

## 3b. Update 10 Nov (after reading D'Souza's family paper in full)
- FACT (paper read; proofs/Lean not checked): Thm 1.1 0.7235 unconditional; Thm 1.2 0.9059137927 assuming two
  *published* hybrid zero-density theorems (Jutila; Montgomery) => effectively unconditional claim. Route limit
  0.9323 at bandwidth 2. Working draft (not claimed): distinct 0.953, dyadic family, parity subfamilies,
  bounded height with a gap. So H1 is far more mined than A-F's Remark suggests; what remains is listed in
  novelty.md section 6.
- Their section 8.2 hunch (CLAIM): better bulk zero-density exponents (12/5; Heath-Brown) raise alpha_0 from 5/3
  to 12/7 or 20/11, giving 0.9117 / 0.9226; the density hypothesis for the family gives bandwidth 2. Assessment:
  this is the one place where zero-density technology (Guth-Maynard-type large-value estimates in hybrid form)
  feeds a proportion; OpenAI's 7/8 half-plane does not give such a hybrid density estimate.

## 3c. Refresh 10 Nov (second pass: other routes to forum discussion)
Routes tried: MathOverflow via api.stackexchange.com (worked); Tao's blog RSS and Mathstodon RSS (worked: nothing
technical on this theorem; recent posts are about AI and the profession); Calegari's blog RSS (worked: no post on
this theorem; an 8 Oct post digests OpenAI results); Lean Zulip (API needs login; the public archive page is the
old static site, no relevant stream found); Nitter/X mirrors (not accessible from this environment; **X remains
unsearched**).

MathOverflow items since Aug 2026 (FACT = read via API today):
| date | id | who | content | relevance |
|---|---|---|---|---|
| 20 Oct | 516206 | question quoting Arias de Reyna; answers T. Chow, P. Hajlasz | Arias de Reyna's exposition says of the Anthropic paper: "As it's written, [1] DOESN'T WORK, but I don't think the necessary modifications deserves more than a note" — the natural-language proof has errors although the Lean theorem stands. | FACT. **Do not rely on the paper's intermediate statements; use the Lean statements or Arias de Reyna / Lamzouri.** Arias de Reyna (arXiv:2610.24612 §1.1, read) does not list the false statements in one place; the only explicit pointer found by grep is footnote 1, p. 15–16: 'In [1] U is taken equal to √T. Their bound is of the order of N and it is not sufficient' (edge-zone/tail estimate: the buffer length U around T and 2T must be chosen smaller). He says it took him a month to be convinced and that the paper is 'filled with bad notations, wrong assertions and unneeded statements'. |
| 17 Sep | 515310 | Pierre-Aubry Simon | Asks whether a non-trivial inequality α₀ ≥ f(α₁) exists between the critical-line proportions of ζ and of ξ' (notes Levinson-type bounds move together). No answer. | Same question as my H11; open on MO. SPEC. |
| 17 Sep | 515314 | P.-A. Simon; answer A. Sahay; comment D. Farmer | Mollifier length: θ = 4/7 (Conrey, via Deshouillers–Iwaniec); Farmer's θ = ∞ conjecture ⇒ 100% on the line (Farmer), and ⇒ RH (Bettin–Gonek). What Kloosterman bound gives θ = 1 is left unanswered. | FACT. Confirms the mollifier route is stuck at θ = 4/7 for an arithmetic reason unrelated to zero-free regions. |
| 12 Oct | 515968 | Pace Nielsen; 9 answers (Durkan, Bloom, GH from MO, Wojowu, Grechuk, Agol, ...) | "Consequences of quasi-RH": character sums, Pólya–Vinogradov with log log q, least nonresidue, Artin's conjecture, Linnik. | FACT: **no answer mentions proportions of zeros on the line, simple zeros, pair correlation or mollifiers** (grep) — independent support for novelty.md §3. |
| 25 Aug | 514655 | answer Stopple | multiplicity m(ρ) < 10 log T unconditionally via Jensen. | background |
| 18 Sep | 515349 | Luigi A.; comments Sahay | RH-conditional discrete mean square of prime-supported polynomials over zeros at length T with error O(T log²T loglog T) (Landau–Gonek). | Possibly useful to h4 (discrete moments at zeros); conditional. |

New hunches from this pass:
| # | who / where | idea | assessment |
|---|---|---|---|
| H13 | D'Souza family paper §8.2 | In families the bandwidth α₀ is set by the *bulk hybrid zero-density exponent* (5/3 from Montgomery's 3/(2−σ) on [3/4,4/5]; 12/7 and 20/11 with better exponents; 2 under the density hypothesis). | CLAIM. The only place where density technology converts into a proportion; Guth–Maynard-type hybrid estimates would feed it. Not for ζ. |
| H14 | A–F Remark 7.2, reconstructed in h2/priorart_T3.md | Their 0.811 equals kernel 1.263·|α| on 1 < |α| ≤ 3/2 with the window cos(u/√2); the optimal window would give 0.834 (0.849 at λ → 2). 1.263 is near (6/π²)/𝔖 = 1.2688. | SPEC (numerical match, not unique). If their weighted large sieve is true, 0.849 density-free is available; it is unproved and D'Souza's analysis suggests major arcs obstruct it. |
| H15 | h4 on the board (h4/T2 §4.2) | Aryan's imaginary-part identity is a linear statistic of support [−1,1]; all two-point averages reduce to the form factor. | Team result [R per h4]; downgrades H2. |

## 3d. Refresh 10 Nov (third pass) — items missed earlier
| date | item | link | content | status |
|---|---|---|---|---|
| 15 Sep | Fabbian, bounded-depth positivity inequality | doi.org/10.5281/zenodo.22778066 | CGdL-type kernel g_A: configuration inequality proved for depth ≤ 33/200 ⇒ 0.6792041 under a narrow-box hypothesis | CLAIM (abstract read) — prior art for the team's D_CGdL target |
| 7 Oct | Fabbian, structural barriers | doi.org/10.5281/zenodo.23198631 | two-point LP certificates fail at common depth y ∈ [0.055, 0.6]; local-kernel certificates fail for y ≥ 0.032; level-3/4 Rudnick–Sarnak statistics gain nothing in clipped-Gram / single-window classes (blind lattices of spacing in (1,2]); cap 0.6764851 | CLAIM (theorem statements of §3, §8, §9, §11 read) |
| 26 Aug / 18 Oct | Tyagi hexagon:2610.00252 v1 / v2 | hexagonmath.org/abs/2610.00252 | v1's broad "cubic augmentation adds exactly nothing" withdrawn; v2 proves it only for an N = 64 flat-window atom-only model | FACT (both versions read) |
| 8 Nov | rStation post 72 | rstation.ai/r/riemann_hypothesis/posts/72 | "honest-adversary LP": 0.6764 (MT), 0.6795 (MT+Fejér), 0.6810 (three windows) as a hypothesis | CLAIM |
| 2023 | Bui–Goldston–Milinovich–Montgomery, Acta Arith. 210 | arXiv:2208.02359 | distinct gaps vs spacings: µ_d ≤ 0.991, µ_{Dd} ≤ 1.0522 under RH | FACT; background for x2 |
Full discussion: h2/gaps_and_threepoint.md.

## 4. To refresh
- X/Twitter and Lean Zulip (not reachable with current tools); talks (AIM, Oberwolfach, MSRI abstracts) not found.
- Re-poll: riemannzeta.fun record; arXiv listing math.NT for "zeros"/"critical line"; Hexagon words zeta, zeros.
- Read D'Souza's zeta paper (papers/zeta/main.pdf, section 1.4 survey of claims) and preprint [9] (0.7212).
