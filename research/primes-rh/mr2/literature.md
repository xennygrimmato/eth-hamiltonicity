# mr2 / literature: least strong-pseudoprime witness under GRH

Notation: n odd composite, w(n) = least a >= 2 such that n is NOT a strong probable prime to base a
(a "witness"). log = natural log. Tags: [K] known (citation), sources checked where stated.

## 1. Upper bounds under GRH

| who | statement | tag / how checked |
|---|---|---|
| Miller 1976 (JCSS 13) | ERH => w(n) = O(log^2 n) (via Ankeny 1952; constant often quoted as 70) | [K], secondary sources |
| Bach 1990, "Explicit bounds for primality testing and related problems", Math. Comp. 55 (191), 355-380 | ERH: any proper subgroup H of (Z/m)^* omits a positive integer < 2 log^2 m; with the extra requirement (x,m)=1, < 3 log^2 m. Consequence stated in the abstract: a composite m has a Miller / Solovay-Strassen witness <= 2 log^2 m. Bach also proves the asymptotic (1+o(1)) log^2 m for the least prime p not dividing m outside H. | [K]. Constants 2, 3 and the asymptotic (1+o(1)) are confirmed by the introduction of LLS (arXiv:1309.3595v3 p.1-2, read in full). AMS page itself returned 403. |
| Wedeniwski 2001 (thesis) | least quadratic non-residue mod q < (3/2) log^2 q - (44/5) log q + 13 | [K] as quoted in LLS p.2 |
| Lamzouri-Li-Soundararajan, "Conditional bounds for the least quadratic non-residue and related problems", Math. Comp. 84 (2015) 2391-2412; corrected arXiv:1309.3595v3 (Dec 2016) | **Thm 1.1** (GRH, q >= 3000, H proper subgroup of (Z/q)^*): least prime l not dividing q, l not in H, satisfies l <= (log q + B(q))^2, B(q) = max(0, 2 loglog q + 3 + 2 w(q)(loglog q)^2/log q - 2A(q)), A(q) = max(0, 2 loglog q - 8/5 - sum_{p|q} log p/(p-1)); and if q has no prime factor below log^2 q then l <= log^2 q. **Cor 1.1**: least quadratic non-residue mod prime q >= 5 is < log^2 q. **Thm 1.2** (asymptotic): l < (alpha(h)+o(1)) log^2 q, h = [G:H], alpha(2)=0.8 (0.794 in Sec. 6.3), alpha(3)=0.7, alpha(h)=0.66 for h>3. **Thm 1.3** (h large): l < (1/4+o(1)) (1-1/h)^2 (log 2h/(log 2h - 4))^2 log^2 q. **Sec. 6.1**: their Prop. 6.1 cannot give better than (1/4+o(1)) log^2 q. | [K], PDF read (v3). NOTE: v1/v2 and the journal version claimed smaller constants (0.42 type); these were withdrawn in v3 (error in Lemma 6.1 found by Carneiro-Milinovich). |
| LLS and Miller-Rabin | The paper **never mentions** Miller-Rabin / witnesses / pseudoprimes (grep of the full text: only the title of Bach's paper). | [K] checked |
| Immediate corollary (not stated in LLS; folklore) | GRH => w(n) <= log^2 n for n >= 3000: strong liars lie in a proper subgroup H of (Z/n)^*; a prime factor of n below log^2 n is itself a witness; otherwise LLS Thm 1.1(2). For n < 3000 by table (our leastwit run). Asymptotically w(n) <= (0.794+o(1)) log^2 n from Thm 1.2. | [K]+[N] trivial corollary |
| Later | I found no paper improving the *Miller-Rabin* constant below what LLS implies (two web searches Nov 2026; weak negative). Carneiro-Milinovich-Quesada-Herrera-Ramos (2021-22, "Exponential sums, twisted multiplicativity and moments" / Fourier optimisation papers on least quadratic non-residue / least character non-residue, arXiv:2001.xxxxx) refine the LLS framework by Fourier-optimisation; exact constants NOT verified here -> treat as "possibly sharper alpha(h) exists". | [K?] unverified |

## 2. Lower bounds / heuristics
- Alford-Granville-Pomerance, "On the difficulty of finding reliable witnesses", ANTS-I (LNCS 877, 1994): w(n) > (log n)^{1/(3 logloglog n)} for infinitely many n. [K]
- Bach-Huelsbergen 1993 heuristic: max w(n) ~ (log 2)^{-1} log n loglog n. [K, heuristic]; AGP conjecture the same order.
- Unconditional upper: Burthe 1997 (Acta Arith. 80), w(n) = O(n^{1/(8 sqrt e)+eps}) except for an explicit family; Balasubramanian-Nagaraj 1998: the exceptions are Carmichael n = pqr with v2(p-1)=v2(q-1)=v2(r-1). [K] (via arXiv:1608.07317 summary). NB: the same family is the extremal case in our Theorem A.
- Lenstra 1979 ("Miller's primality test", IPL 8): for p prime there is a < 4 log^2 p with a^{p-1} != 1 mod p^2 (unconditional; non-squarefree n need no GRH). [K]
- Konyagin-Pomerance 1997, Thm 2.1: Psi(x, log^c x) > x^{1-1/c} for x >= 4, 2 <= log^c x <= x. [K] (statement confirmed via arXiv:0707.4102).

## 3. Numerics
- psi_m = least strong pseudoprime to the first m prime bases: psi_1=2047, psi_2=1373653, psi_3=25326001,
  psi_4=3215031751, psi_5=2152302898747, psi_6=3474749660383, psi_7=psi_8=341550071728321 (Pomerance-Selfridge-Wagstaff 1980, Jaeschke 1993);
  psi_9=psi_10=psi_11=3825123056546413051 (Jiang-Deng 2014); psi_12=318665857834031151167461,
  psi_13=3317044064679887385961981 (Sorenson-Webster, Math. Comp. 86 (2017), arXiv:1509.00864). [K]
- Hence the record ratios w/ln^2 n at the psi's: 3/ln^2(2047)=0.0516, 5/..=0.0250, 7/..=0.0241, 11/..=0.0230,
  13/ln^2(psi_5)=0.0161, 17/ln^2(psi_6)=0.0204, 23/ln^2(psi_8)=0.0205, 37/ln^2(psi_11)=0.0206,
  41/ln^2(psi_12)=0.0143, 43/ln^2(psi_13)=0.0135. All far below any GRH bound; consistent with log n loglog n.
- Our own exhaustive run to 10^10 (leastwit.c) reproduces psi_1..psi_4 and the count 3291 of spsp(2) below 10^10. [N]

## 4. Fewer bases / faster GRH tests (for Task 3)
- Miller under GRH: O(log^2 n) bases x O~(log^2 n) per base = O~(log^4 n) bit operations. [K]
- AKS (Lenstra-Pomerance version) O~(log^6 n) unconditional; no GRH-conditional deterministic test faster than Miller's O~(log^4) is known to me (ECPP/APR-CL are not polynomial deterministic). [K]
- arXiv:2611.02280 (Shunia, Nov 2026) claims L^{6+o(1)} under GRH for a single-binomial test: not faster than Miller. [K, abstract only, unrefereed]
- Quadratic Frobenius (Grantham), Baillie-PSW: no composite known, but no GRH proof that one fixed test suffices. [K]
