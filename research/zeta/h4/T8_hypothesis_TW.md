# T8 — Hypothesis TW: zeta'-weighted pair sums as new arithmetic input beyond the bandwidth-one ceiling

Helper h4, 10 Nov 2026. Scripts: `h4/tw_model.py` (unmollified rows), `h4/tw_moll.py` (mollified rows), outputs `h4/out/`.
Tags as in TEAM.md. Notation: rho = beta + i gamma, gamma_rho := (rho - 1/2)/i, rho* := 1 - conj(rho), L = log(T/2pi), N = N(T,2T).

## 1. Statement, and what is known

### 1.1 The objects [R]
Let f(s) = zeta'(s)B(s), B(s) = sum_{k<=y} b(k) k^{-s} with real b(k), y = T^theta. For real u put
  A_B(u) := sum_{T<gamma<=2T} f(rho) e^{iu gamma_rho} = sum f(rho) x^{rho-1/2},  x = e^u   (multiple zeros contribute 0).
**Identity.** conj A_B(u) = sum_{rho'} f(1-rho') e^{-iu gamma_rho'}. (Proof: conj f(rho) = f(conj rho) = f(1 - rho*), conj(gamma_rho) = gamma_{rho*},
and rho -> rho* permutes the zeros of the window.) Hence, for every r >= 0,
  P_B(r) := sum_{rho,rho'} f(rho) f(1-rho') r^(gamma_rho - gamma_rho') = int r(u) abs(A_B(u))^2 du >= 0
is at once an analytic function of the zeros (computable by contour integrals, no RH) and a Hermitian square (no RH).
On RH it equals sum a_rho conj(a_rho') r^(gamma - gamma'), a weighted pair correlation whose weights vanish on multiple zeros.

**Hypothesis TW(lambda_-, lambda_+, theta).** There is an explicit function F_B on [-lambda_-, lambda_+] (plus an explicit atom at 0) with
  (1/(N L^2)) int r(alpha) abs(A_B(alpha L))^2 d alpha -> int r dF_B     for every continuous r supported in [-lambda_-, lambda_+],
"alpha > 0" meaning x = T^alpha > 1. The expected F_B is the random-matrix value (ratios conjecture); in the finite
model of §2 it is the CUE expectation.

### 1.2 Status of the inputs
| statistic | statement | status |
|---|---|---|
| sum zeta'(rho) (S1, B = 1) | = (T/4pi) log^2(T/2pi) + ..., error O(T e^{-c sqrt(log T)}) | [K] unconditional: Conrey–Ghosh–Gonek (Shanks' conjecture); Fujii 1994; Hughes–Pearce-Crump 2022 (as quoted in arXiv:2601.18025 Thm 3) |
| sum zeta'(rho) X^rho, fixed X | asymptotic formula | [K] Fujii, Proc. Steklov Inst. 276 (2012) (abstract only read) |
| sum X^rho, uniform | Landau–Gonek | [K] unconditional (Gonek 1985/1993) |
| sum chi(rho) X^rho, uniform in X >= 1 | three regimes X < T/2pi, ~T, > T, error O(T^{1/2} log^2 T + X^{1+o(1)} T^{-1/2} + ...) | [K] arXiv:2601.18025 Thm 5 (read in abstract/intro form only) |
| S1, S2 with BHB's mollifier, theta < 1/2 | asymptotics (19/24) N L, (57/64) N L^2 | [K] unconditional: Bui–Heath-Brown arXiv:1302.5018 Lemmas 1–2 ("all the analysis is unconditional"; RH only to read S2 as sum of squares) |
| sum zeta'(rho) X(rho) Y(1-rho), Dirichlet polynomials of length T^theta, theta < 1/2 | asymptotic | [K] N. Ng, arXiv:0706.1763 (hypotheses of the mean-value theorem itself not checked by me) |
| S2 with B = 1: sum zeta'(rho) zeta'(1-rho) ~ N L^3/12 | Gonek 1984 states the discrete moment under RH; the contour-integral computation is of the analytic sum | [C] believed unconditional (consistent with BHB's formula as theta -> 0); not verified in print |
| pointwise A_1(u), abs(u) <= (1-eps) L | approximate functional equation for zeta'(rho) + Landau–Gonek + the chi(rho)X^rho theorem: main terms are (T/2pi)(Lambda*log)(x) at integers x and prime exponential sums sum Lambda(k) e(xnk) | [C] plausible with errors O(T^{1-delta}); not in print |
| **L^2 form: int r abs(A_1)^2 for x >= 1 ("easy direction", alpha in [0, 1))** | mean square in x of the main terms; the cross terms nk != n'k' oscillate in x over ranges of length >= 1, so a Montgomery–Vaughan argument should give diagonal dominance | [C] **open, looks provable**; this is TW(0, 1, 0) |
| L^2 form for x < 1 ("hard direction") | cross terms with abs(nk - n'k') < 1/x do not oscillate: needs prime pairs in linear relations (Hardy–Littlewood type), on average over n, n' | [C] open; partial ranges via Bombieri–Vinogradov at best |
| mollified two-point (theta > 0) | twisted first moments with real twists; BHB's large-sieve treatment for rational twists | [C] open |
| fourth-moment objects (HS norm of the weighted matrix G_2 of T2 §1.3) | — | out of reach |

In model language (§2): zeta'(rho) x^{rho} with x in [1, T] corresponds to the frequencies abs(l) <= N/2 of
T(l) = sum_rho Z'(tau_rho) e(l tau_rho/N) (Z = Hardy's function: zeta'(rho) carries the phase e^{-i theta(gamma)}, i.e. frequency -N/2);
x < 1 corresponds to N/2 < abs(l) <= 3N/2.
