# Novelty note: proportion of zeta zeros simple and on the critical line (as of 10 Nov 2026)

Author: helper h2. Sources checked today: arXiv API (abstracts + PDFs of the papers marked V), Hexagon API
(single-word queries zeta, zeros, simple, Montgomery, pair, correlation, critical, proportion, Weil, Hermitian,
Levinson, mollifier, multiplicity, distinct, gaps, Riemann, Dirichlet, density, ...), the OpenAI catalogue
(`scratchpad/hx/oai-new.md`), the quasi-RH preprint text (`scratchpad/hx/oai003/p.txt`), GitHub READMEs,
riemannzeta.fun, web search. Tags: **V** = I read the primary source today; **S** = taken from a secondary source
(named); **M** = from memory, not re-verified today; **U** = claim exists but unrefereed/unverified.

## 0. Bottom line

1. **"Beat 0.6725 unconditionally" is NOT open.** It has been done repeatedly since mid-August 2026, always by
   small amounts and always inside the same framework (trace + Montgomery energy at Fourier support [-1,1], plus a
   computer-assisted local inequality for k consecutive zeros). Best values:
   - arXiv, Lean + 3 "search returned true" axioms: **0.673538** simple and on the line, **0.839005** distinct,
     0.889315 simple-or-on-line — Knausgård, arXiv:2610.08965 (6 Oct 2026), Thms 1.3, 1.1, 1.5. **V**
   - Lean-kernel-verified leaderboard riemannzeta.fun ("Riemann.fail", repo josusanmartin/riemann), three standard
     axioms only, statement = distinct zeros on the line: **0.6736388767** (Knausgård, 9 Nov 2026, refining an
     entry of Bei Yi; 51 records since 1 Oct). **V** (site read today; proofs not read).
2. **There is a proved ceiling for the whole framework: 0.68185** (simple on the line) and **0.84093** (distinct):
   Alpöge–Furman §7.2 "bandwidth-one ceiling" (Lean `Zeta23.PairCeiling.ceiling_law256`, enclosures by interval
   arithmetic) and Knausgård Thm 7.7 / Cor. 7.9 (own certified law, period 256, p = 0.6818277). For the
   "interaction of simple points only" scheme the ceiling is 0.67383 (Knausgård Prop. 7.3). So the open and
   meaningful targets are: (a) anything **> 0.6819** for zeta (needs new arithmetic input: pair correlation beyond
   support 1, a third moment, or a hybrid), (b) families, (c) closing 0.6736 → 0.6818 (crowded, incremental).
3. **OpenAI's quasi-RH (Re s > 7/8 zero-free) gives nothing for these proportions** (§3).
4. Families: prior art exists (Hua–Yang; D'Souza 0.7235 unconditional, 0.9059 given two hybrid zero-density
   estimates; A–F Remark claims 0.811 with proof omitted). See §4 for what is unclaimed.

## 1. What has appeared since 1 Aug 2026

### 1a. arXiv (all V unless marked)
| date | id | authors, title | content |
|---|---|---|---|
| 13 Aug (v2 19 Aug) | 2608.13637 | Alpöge, Furman, *More than two thirds of the zeta zeros are simple and on the critical line* | Thm A: N_0^s ≥ (2/3)N, N_d ≥ (5/6)N; MT window 0.67250, 0.83625. Thm B: same for a fixed primitive Dirichlet L. Remarks (draft v5-18, §7): ξ' 0.85838 / 0.86864 simple on line (Lean); family average q ≤ Q with weights (1−q/Q)^2: 0.811 / 0.905 "details omitted, not in Lean"; under RH distinct ≥ 0.85082; hypothesis HL*(4) ⇒ 13/18; ceiling 0.6818. |
| 17 Aug (v2 24 Aug) | 2608.16034 | Hua, Yang, *Simple and distinct zeros in a prime-modulus Dirichlet family from near-microscopic to polylogarithmic heights* | Thm 2.1: all nonprincipal χ mod prime q, unweighted, (log log q)^{1+η}/log q ≤ T ≤ (log q)^A: 0.67250 / 0.83625. Bandwidth 1 only. |
| 18 Aug (listed Sep) | 2609.27808 | Hua, Yang, *Gevrey localization for simple and distinct zeros in a prime-modulus Dirichlet family* | growing-height companion; constants 2 − 1/c*_λ with λ_bw ≤ 1; no gain over 0.6725. |
| 2 Sep (v2 8 Sep) | 2609.02882 | Lamzouri, *A new proof that more than 2/3 of the zeros ... are simple and on the critical line* | Thm 1.1: reproof via one Hilbert-space inequality + BGST pair correlation; new: simple-or-on-line ≥ 0.88762, (N_s+N_0)/2N ≥ 0.83625. |
| 7 Sep | 2609.07918 | B. Wang, *Simple critical zeros and distinct zeros ... in short intervals* | same constants in short intervals (pair correlation in short intervals). |
| 14 Sep | 2609.15329 | Pearce-Crump, *Optimising Selberg's method for critical zeros* | 6.78% from Selberg's method (context only). |
| 21 Sep, **withdrawn 6 Oct** | 2609.24167 | B. Wang, *Proportions of the non-trivial zeros ...* | claimed C_0 + 6.67·10^{-8}; withdrawn ("New method is need to obtain good improvement"). |
| 27 Sep | 2609.33043 | Knausgård, *More than 83.69% of the zeros ... are distinct* | N_d/N ≥ 0.8369928 (matrix inequality with clipping + imported 7-point inequality). |
| 6 Oct | 2610.08965 | Knausgård, *More than 83.9% ... distinct and more than 67.35% simple and on the critical line* | Thm 1.1: 1645064/1960733 = 0.839005; Cor 1.2: simple ≥ 0.678009; Thm 1.3: N_0^s/N ≥ 0.673538; Thm 1.4: average ≥ 0.836769; Thm 1.5: simple-or-on-line ≥ 0.889315. Ceilings Prop 7.2, 7.3, Thm 7.7, Cor 7.9. Lean, 3 extra axioms. Contains the best survey of ~20 unrefereed claims. |
| 9 Oct | 2610.12853 | Aryan, *On the Imaginary Part of ζ'/ζ* | new zero-side identity (odd companion of the Fejér kernel); exposition of the matrix argument; hunch: sign-sensitive extra statistic could bound "clustering" (§3.4). No new proportion. |
| 16 Oct | 2610.23467 | Cobeli, Zaharescu, *More than 8/9 zeros ... are simple or on the critical line* | Thm 1: ≥ 0.88893 (> 8/9). Superseded numerically by Knausgård 0.88932 (10 days earlier!). |
| 16 Oct | 2610.22927 | Angón, Ross, Tang, Zhao, *Unconditional bounds for two, three and four consecutive moderate gaps ...* | positive proportions 0.3450, 0.1813, 0.0175 (Gonek–Sahay question). |
| 17 Oct | 2610.24612 | Arias de Reyna, *Human Exposition of Claude's 2/3 Theorem* | exposition. |
| 19 Oct (v2 26 Oct) | 2610.26841 | Lamzouri, *Isolated zeros of the Riemann zeta function and zeros of linear combinations of Dirichlet L-functions* | Thm 1.1: ≥ 13/20 of zeros are c-isolated for some c>0 (> 1/2 for c = 1/6); Thm 1.3: k = 3,4,5 consecutive moderate gaps; Thm 1.5: ≥ 31% of zeros of b_1 L(s,χ_1)+b_2 L(s,χ_2) on the line with odd multiplicity (was 7.4·10^{-9}). |
| 19 Oct | 2610.26705 | Gonçalves, Kerr, Klurman, Vedana, *The Riemann zeta function at the zeros of real-rooted trigonometric polynomials* | at most 2/3 of zeros of a real-rooted trig polynomial are zeta zeros (Li–Radziwiłł generalised). Different "2/3". |
| 19 Oct | 2610.26038 | Bondarenko, Heap, *Half-sized gaps between zeros* | RH ⇒ liminf normalised gap ≤ 1/2. |
| 20 Oct | 2610.28527 | Durkan, Pearce-Crump, *Small and large gaps between zeros of Dirichlet L-functions* | unconditional: infinitely many gaps < 1/2+ε for every fixed primitive Dirichlet L; RH: positive proportion for ζ; large gaps > 3.63. |
| 3 Nov | 2611.05000 | Baluyot, Conrey, Irfan, Snaith, *Almost primes in short intervals and averages of long Dirichlet polynomial approximations to (ζ'/ζ)^k* | conditional (RH + shifted moments) asymptotics for mean squares of *long* truncations of (ζ'/ζ)^k — exactly the kind of input "support > 1 / higher trace" would need; conditional only. |
Also: 2608.07399 Bondarenko–Heap (Siegel zeros ⇒ small gaps, RH); 2610.05227 Sugiyama–Suriajaya (weighted one-level density); 2610.26575 Basak–Castillo–Zaharescu (RH); 2610.31744 Bober–Ge–Milinovich (gap bias family).
No post-August arXiv paper by Goldston, Turnage-Butterbaugh, Chirre, Carneiro, Bui, Radziwiłł or Chandee on this
question was found (author queries run today; Suriajaya and Baluyot have the unrelated papers above; Aryan has
2610.12853). Conrey and Goldston are thanked by Anthropic for examining the paper.

### 1b. Unrefereed repositories / Zenodo (U; list from Knausgård 2610.08965 §1 and refs; READMEs of the starred ones read today)
0.67300 ainta (GitHub, 11 Aug)*; 0.67305 and distinct 0.83652, simple-or-on-line 0.88855 Chandru (Zenodo 22701203);
0.67319 tawanerguo-cn; 0.67331 trmdy / Y. Shi (Zenodo 21926962); 0.67337 D'Souza*; 0.673399 Devine (Zenodo
22066689; also "conditional advances beyond 67.92%"); 0.6734 Zhaoyi-Tian (Lean); 0.67341 AMTOPA; 0.673425 Schäfer;
0.673451 K. Singh; 0.673476–0.673477 Gebendorfer (3 Zenodo drafts), Rakitin; 0.673492 Freund (draft PR 888,
GettysburgResearch/riemann)*; distinct: Santibañez-Leal 0.83737, D'Souza 0.83757 (Lean) / 0.83805 (one external
certificate). D'Souza also: simple zeros anywhere 0.675159 (Lean, std axioms) / 0.676103.
**Outlier, almost certainly wrong as an unconditional claim:** H. Yang, S. Yang, Zenodo 21975237 (17 Aug),
"More than 79.62% ... simple and on the critical line" (0.7962 / 0.8981) from trace moments of order ≤ 6. Its own
authors grade the analytic part unverified; A–F §7.2(e) says tr G^k is available unconditionally only for
X^k ≤ T^{2−ε}, and derives 13/18 from the 4th moment only under the hypothesis HL*(4). Treat as [C].

### 1c. Hexagon (V, API today)
No Hexagon paper improves or extends Alpöge–Furman's proportion. Nearby: 2610.00252 Tyagi, *Cubic augmentation of
a two-moment model* (finite model: adding a half-bandwidth cubic trace gives **no** gain over the two-moment
optimum in an atom-only class; not a statement about zeta); 2611.00059 J. Singh (Z' at close pairs, conditional);
2610.00634 Fraccaro (6th moment lower bound); 2610.00343 Caceres. Quasi-RH follow-ups: 2610.00178 Bhattacharya
(*Unconditional implications of the Quasi-Riemann Hypothesis*), 2610.00200 Cureton–Thorner, 2610.00216 Hu,
2610.00220 Rubinstein–Restrepo Borrero, 2610.00458/00716 Winarski, 2610.00655, 2611.00082, 2611.00080 Liu,
Landau–Siegel variants 2610.00311 Green, 2610.00409 van Dijk, 2610.00461 Guo, 2610.00466 Frei–Kai, 2610.00545
Pollack, 2610.00228 Bhargava. None concerns proportions of zeros on the line, simple zeros, or pair correlation.

### 1d. OpenAI catalogue (V)
Only entry 003 concerns zeta zeros: *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8* (30 Sep 2026,
Thm 1.1), alternate 11/12 proof (5 Oct), *Uniform exclusion of Landau–Siegel zeros* (1 Oct). No catalogue entry on
proportion of zeros on the line, simple zeros, pair correlation, gaps between zeros, or mollifiers (grep today).

## 2. State of the art table

N = zeros with multiplicity; N_0 on line; N_0^s simple and on line; N_s simple; N_d distinct.

### 2a. Unconditional, zeta
| quantity | value | source | tag |
|---|---|---|---|
| N_0/N | > 0 | Selberg 1942 | M |
| N_0/N | 0.3420 (>1/3); 0.3474 | Levinson, Adv. Math. 13 (1974) 383–436; 1975 | S (Arias de Reyna) |
| N_0^s/N | ≥ 0.3474 | Heath-Brown, BLMS 11 (1979) (Levinson's zeros are simple; also Selberg) | S |
| N_0/N, N_0^s/N | 0.4088, 0.4013 | Conrey, J. reine angew. Math. 399 (1989) 1–26 | M |
| N_0/N, N_0^s/N | 0.4105, 0.4058 | Bui–Conrey–Young, Acta Arith. 150 (2011) | M |
| N_0/N | 0.4128 | Feng, J. Number Theory 132 (2012) (uses mollifier length 4/7; the length has been questioned, 0.4107 with θ<1/2) | M |
| N_0/N, N_0^s/N | 0.417293 (>5/12), 0.407511 | Pratt–Robles–Zaharescu–Zeindler, Res. Math. Sci. 7 (2020) no. 2 | S (A–F, Lamzouri, Knausgård agree: 5/12 and 0.4075) |
| N_0^s/N | 2/3; 0.672500 | Alpöge–Furman 2608.13637 Thm A(i); reproved Lamzouri 2609.02882 Thm 1.1 | V |
| N_0^s/N | **0.673538** | Knausgård 2610.08965 Thm 1.3 (computer-assisted, unrefereed) | V |
| N_0^*/N (distinct on line) | **0.6736389** | riemannzeta.fun record 9 Nov 2026 (Lean kernel + nanoda) | V (site) |
| N_s/N (anywhere) | 0.678009 | Knausgård Cor 1.2 (= 2·0.839005 − 1) | V |
| N_d/N | 0.63952; 0.6603; "> 70%" | Farmer 1995; Wu, Q. J. Math. 66 (2015); Ki–Lee, Funct. Approx. 47 (2012) Thm 5 | S. NB A–F cite 0.6603 as previous record, Lamzouri and Knausgård cite Ki–Lee 70% — inconsistent in the literature; not checked. |
| N_d/N | 5/6; 0.836250 | A–F Thm A(ii); Lamzouri Thm 1.1 | V |
| N_d/N | **0.839005** | Knausgård Thm 1.1 | V |
| simple or on line | 0.88762; 0.88893; **0.889315** | Lamzouri Thm 1.1; Cobeli–Zaharescu 2610.23467 Thm 1; Knausgård Thm 1.5 | V |
| (N_s+N_0)/2N | 0.83625; **0.836769** | Lamzouri Thm 1.1; Knausgård Thm 1.4 | V |
| c-isolated zeros | 13/20 (some c>0); >1/2 (c=1/6) | Lamzouri 2610.26841 Thm 1.1 | V |
| ξ' zeros simple on line | 0.79874; 0.85838 / 0.86864 | Conrey 1989; A–F Remark (ξ'), Lean | V (draft) |
| method ceiling (bandwidth one, two moments) | 0.68185 / 0.84093 | A–F §7.2; Knausgård Cor 7.9 | V |

### 2b. Conditional, zeta
| hypothesis | quantity | value | source | tag |
|---|---|---|---|---|
| RH | N_s/N | 2/3 | Montgomery, Proc. Sympos. Pure Math. 24 (1973) | S |
| RH | N_s/N | 0.6725 | Montgomery (–Taylor), ICM 1974 Proc. (1975) | S |
| RH | N_s/N | 0.6727 | Cheer–Goldston, Proc. AMS 118 (1993) | M |
| RH | N_s/N | 0.6792 | Chirre–Gonçalves–de Laat, Adv. Math. 361 (2020) 106926 (SDP, uses F ≥ 0 outside [−1,1]) | S (A–F, Lamzouri; Goldston et al. survey says "67.92%") |
| RH + GLH | N_s/N, N_d/N | 19/27 = 0.7037; 0.8456 | Conrey–Ghosh–Gonek, Proc. LMS 76 (1998) | S (Lamzouri) |
| RH | N_s/N | 19/27 | Bui–Heath-Brown, BLMS 45 (2013) 953–961 | S |
| RH | N_d/N | 0.8477; 0.85082 | CGdL 2020; A–F §7.3 (cubic weight + BHB), remark only | S / V (draft) |
| RH | MT window optimal among windows | Carneiro–Chandee–Littmann–Milinovich, Crelle 725 (2017) Cor. 14 | S (A–F) |
| zeros within b/log T of line | N_0^s/N ≥ 2/3 (b = 0.3185), 0.6725 (b = 0.001) | Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh arXiv:2501.14545; Goldston–Suriajaya | S (Lamzouri) |
| PCC (no RH) | 100% simple and on line | Goldston–Lee–Schettler–Suriajaya (2025), extending Gallagher–Mueller 1978 | S (survey arXiv:2511.20059 Thm 5) |
| form factor on (−λ,λ), λ ≈ 1.04 / 1.26 / 1.70 | 0.70 / 0.80 / 0.90 by A–F route | Claude/Anthropic preprint Remark 1.1 | S |
| HL*(4) | 13/18 | A–F §7.2(f) | V (draft) |
| Alternative Hypothesis | almost all zeros simple (under RH) | Baluyot et al. / Lagarias–Rodgers | M, unverified |
| RH | smallest gap liminf ≤ 0.5154; ≤ 1/2 | Preobrazhenskii 2016 et al.; Bondarenko–Heap 2610.26038 | M / V |

### 2c. Families of Dirichlet L-functions
| hypothesis | statement | source | tag |
|---|---|---|---|
| none | each fixed primitive χ: 0.6725 / 0.83625 | A–F Thm B | V |
| none | prime q, all χ, short to polylog heights: 0.6725 / 0.83625 | Hua–Yang 2608.16034 Thm 2.1 | V |
| none | primitive χ mod q ≤ Q, T = (log Q)^{r+ε}, r ≥ 3: **0.7235** simple on line (earlier 0.7212) | D'Souza, github Oliverds321/simple-zeros v1.0, family paper (Lean, std axioms) | U (README + abstract read) |
| Jutila + Montgomery hybrid zero-density estimates (published theorems, entered as hypotheses in Lean) | same family: **0.9059** | D'Souza, "Shell theorem" | U |
| none (proof omitted) | weights (1−q/Q)^2, bandwidth 3/2: 0.811 / 0.905 | A–F Remark (Dirichlet on average) | V (draft), unproved in print |
| none | 56% of zeros of the family on the line (mollifier + asymptotic large sieve) | Conrey–Iwaniec–Soundararajan, Crelle 681 (2013) | M |
| GRH | 11/12 = 91.7% simple (q-aspect, support 2) | Özlük 1996; Chandee–Lee–Liu–Radziwiłł, Q. J. Math. 65 (2014) | M |
| GRH | 93.22%; 0.9350 | Sono 2016; CCLM 2017 / CGdL 2020 | M, constants not re-verified |
| none | linear combinations of two L(s,χ): 31% on line | Lamzouri 2610.26841 Thm 1.5 | V |

## 3. Does the quasi-Riemann hypothesis help? **No.**

Statement used: every Dirichlet L-function incl. ζ is zero-free in Re s > 7/8 (OpenAI 003, Thm 1.1); Hexagon
refinements only move 7/8 to 0.8734 for Hecke L-functions (Liu 2610.00655, 2611.00082) or change the family.
- The preprint itself says zero-density estimates "address a different question" and proves none; its listed
  corollaries are least nonresidue / deterministic square roots (Cor. 1.2), not anything near Re s = 1/2.
- Levinson–Conrey proportions are limited by the admissible **mollifier length** θ (4/7 via Kloosterman sums),
  i.e. by off-diagonal terms in twisted second moments of ζ on the line; a zero-free half-plane does not lengthen
  mollifiers. Even full RH is not known to do so.
- The pair-correlation route is limited by the **Fourier support** of the form factor (|α| < 1 ⇔ Dirichlet
  polynomials of length ≤ T). Beyond 1 one needs prime-pair (Hardy–Littlewood) information; RH does not give it,
  a fortiori a 7/8 half-plane does not. A–F use no zero-free region or density estimate at all (their inputs:
  explicit formula, N(t,t+1) ≪ log t, Stirling, Chebyshev–Mertens, Montgomery–Vaughan), and their constants are
  already those one gets under RH; the ceiling 0.68185 holds for RH-satisfying configurations too.
- The box hypothesis of BGST/Goldston–Suriajaya needs all zeros within o(1/log T) of the line; a strip of
  half-width 3/8 is useless for it.
- Where a zero-free half-plane *could* matter is only in error terms/uniformity (e.g. cleaner tails in family or
  short-interval versions, removing a zero-density hypothesis such as the two estimates in D'Souza's Shell theorem
  — but those estimates concern zeros close to 1/2 at the (log Q)^{-θ} scale and are not implied by 7/8).
- Bhattacharya's Hexagon list of "unconditional implications" (2610.00178, abstract only read) concerns results
  needing a fixed half-plane; no proportion-of-zeros result is among the announced ones. **Unverified beyond the
  abstract.**
Net: no new proportion, no longer mollifier, no longer Dirichlet-polynomial range.

## 4. What is open and unclaimed (as far as today's search shows)

Open, meaningful:
1. **N_0^s/N > 0.68185 (or N_d/N > 0.84093) for ζ unconditionally** — nobody claims it credibly (Yang–Yang 0.7962
   is unverified and conflicts with A–F §7.2(e)). Requires leaving "bandwidth-one, two moments".
   Sub-statement that would already be new: any *unconditional* evaluation or one-sided bound of a statistic not
   determined by the form factor on [−1,1] (third trace on a short window; Aryan's imaginary-part statistic;
   a lower bound for the negative spectral mass B of the off-line part; hybrid with a Levinson mollifier count).
2. **Families, fully proved and above 0.7235 without zero-density hypotheses**; the A–F claim 0.811 at bandwidth
   3/2 has no published proof. Also unclaimed: dyadic q ∈ (Q/2, Q]; prime moduli with bandwidth > 1 (Hua–Yang have
   bandwidth 1); bounded height T = O(1) (low-lying zeros, where one-level density and the device could combine);
   real characters / quadratic twists; GL(2) (holomorphic forms in level or weight aspect; Rudnick–Sarnak range is
   shorter); distinct-zero constants for families beyond 0.905 claimed.
3. **Distinct zeros**: 0.839005 proved (U), ceiling 0.84093 — gap 0.0019 only; beyond 0.841 open as in 1.
4. **Small gaps unconditionally for ζ**: Durkan–Pearce-Crump state < 1/2+ε for primitive Dirichlet L-functions;
   positive proportion of small gaps for ζ only under RH. Lamzouri/Angón et al. have moderate (large-ish) gaps.
   An unconditional positive proportion of gaps < c·mean with explicit c < 1 from the device looks unclaimed
   (not searched exhaustively: **unverified**).
5. **Other L-functions individually**: A–F say inputs hold for Davenport–Heilbronn/Epstein; a stated theorem for
   degree-2 L-functions (where N ~ (T/π) log T and support is 1/2) is not in the literature found.
Closed / crowded (do not spend effort): beating 0.6725 by 10^{-3}; reproofs; short intervals (Wang); simple-or-
on-line (Lamzouri, Cobeli–Zaharescu, Knausgård); isolated zeros (Lamzouri); expositions.

## 5. Who is working on it
Lamzouri (2 papers); Knausgård (2 papers + leaderboard record); Biao Wang; Hua–Yang (families); Cobeli–Zaharescu;
Aryan; Arias de Reyna; Angón–Ross–Tang–Zhao; Durkan, Pearce-Crump; Bondarenko–Heap; Gonçalves–Kerr–Klurman–Vedana;
a large amateur/AI-assisted crowd (riemannzeta.fun: Lavery, typh, Chandru, Y. Shi, Li Xiang, ajp88, R. Khan,
Bei Yi; GettysburgResearch "Agentic Polymath"; D'Souza; Axiom formalised Lamzouri's theorem per aiprovedwhat.com,
**S**). Nothing public yet from Goldston, Turnage-Butterbaugh, Chirre, Carneiro, Bui, Radziwiłł, Chandee.

## 6. Addendum (families, after reading D'Souza's family paper in full, release v1.0, 3 Oct 2026) — status U (unrefereed, AI-produced, Lean not rebuilt by us)
Source: github.com/Oliverds321/simple-zeros `papers/family/main.pdf` (46 pp.). Family F_Q = all primitive χ of
modulus 1 < q ≤ Q, unweighted, T = (log Q)^{r0+ε}, r0 ≥ 3; proportions of Σ_χ N_χ(T,2T).
- **Thm 1.1 (killed kernel)**: ≥ 0.7235 − c·loglog Q/log Q simple and on the line, no hypothesis (Lean
  `ZetaShell.LemmaK.theorem_one_prime_design`, three standard axioms). Variational supremum of this route 0.723795.
  Earlier preprint (ref [9], library ZetaQ): 0.7212, and 0.7098 for a dyadic family.
- **Thm 1.2 (Shell kernel)**: ≥ 0.9059137927 − c(log Q)^{−θ}, θ < 503/1994, assuming (J) Jutila's log-free hybrid
  zero-density estimate [Jutila, Thm 1] and (M) Montgomery's hybrid estimate (as in Bombieri, Thm 20). These are
  published theorems, so the claim is in effect **unconditional 0.9059**; in Lean they are displayed hypotheses.
  Route limit: 0.9061786 with (M); 0.9117 / 0.9226 with better bulk density exponents (not claimed); 0.9322826 as
  bandwidth → 2 (= Sono's GRH constant, per [9]).
- Not claimed there (working draft only): distinct zeros 0.95296 (F_Q), 0.95159 (dyadic), 0.8618 (killed kernel);
  parity subfamilies; bounded height (sketch "with a stated gap"); dyadic q ∈ (Q/2, Q] at the new constants.
- Corrections to §2c from this paper's literature review (their tag [V]): Conrey–Iwaniec–Soundararajan prove
  ≥ 14/25 **simple and on the line** on average over primitive χ with weight Ψ(q/Q)/φ(q), (log Q)^6 ≤ T ≤ (log Q)^A
  (unconditional, Levinson + asymptotic large sieve); Sono: ≥ 0.6044 (even characters, smooth dyadic weight,
  unconditional, Feng mollifier); under GRH Chandee–Lee–Liu–Radziwiłł / Sono 0.9323 for low-lying zeros.
- Consequence for §4 item 2: in the q ≤ Q Dirichlet family the unconditional frontier is already **0.7235 (clean) /
  0.9059 (using density theorems)**, not 0.6725; A–F's 0.811 (different, smooth weight) is superseded numerically
  by the Shell claim. Still unclaimed anywhere: bounded height / low-lying window; dyadic or prime-only moduli
  above bandwidth 1; real primitive characters (quadratic family, where the large sieve is Heath-Brown's);
  GL(2) families; a refereed or independently rebuilt proof of any of the above; closing 0.9059 → 0.9323
  (needs the density hypothesis in the family or a route avoiding density estimates).
