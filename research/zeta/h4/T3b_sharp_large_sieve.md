# T3b — the sharp weighted Farey large sieve for the family certificate (K = 1/S and K = 1.2688 instead of MV's 3/(2S) = 3.13)

Helper h4, 10 Nov 2026. Builds on h5/T3_families.md §3 (family certificate with F~(alpha) = alpha on [0,1], K alpha on (1, lambda]).
Scripts: `h4/t3b_density.py` (constants), `h4/t3b_check.py` (brute-force checks), `h4/t3b_constants.py` (proportions via
h5/family_opt.py). Tags as in TEAM.md.

## 0. Result
Family: primitive chi mod q, Q_0 < q <= Q, Q_0 = Q^{1-eps}, weight omega_chi = w(q/Q)/phi(q), w: [0,1] -> [0,1] of bounded variation.
S := prod_p (1 - p^{-2} - p^{-3}) = 0.4791453599 [N] (mean value of phi*(q)/phi(q), phi* = number of primitive characters) [R, Euler product].

**Theorem LS (sharp weighted large sieve) [R].** Let N <= Q^{2-7 eps} and c_n complex, M < n <= M+N. Then
  sum_{Q_0<q<=Q} (w(q/Q)/phi(q)) sum*_{chi mod q} abs(sum_n c_n chi(n))^2  <=  (C*_w + O(Q^{-eps/2})) Q sum abs(c_n)^2,
  C*_w := sup_{t>0} (1/t) sum_{1<=k<=t} (phi(k)/k) w(k/t).
The number of harmonics is sum_q w(q/Q) phi*(q)/phi(q) = (S int_0^1 w + o(1)) Q, so the large-sieve ratio is
  **K_w = C*_w / (S int w)**.
* w = 1 (sharp cut-off): C* = 1 (attained at t = 1: the spoke {1/q} at 1/Q), K = 1/S = **2.0870**  [R].
  (Prior art, per h2/priorart_T3.md: D'Souza's family paper §4.3–4.4 has the same local-density picture for the UNWEIGHTED family,
  where the shells around a/r are not removed by a weight and are handled with zero-density input; here the weight 1/phi(q), the
  cut q > Q^{1-eps} and, optionally, w(1) = 0 remove atoms and shells, so no density input is needed. I have not read his proof.)
* any non-increasing w: C*_w <= int w (right Riemann sums of a decreasing function, phi(k)/k <= 1), so K <= 1/S [R].
* w vanishing at 1: C*_w/((6/pi^2) int w) = 1.00000 for (1-u)^2 and (1-u)^3, 1.00008 for 1-u, 1.0004 for cos^2(pi u/2)
  (scan t <= 2 10^4) [N], i.e. **K = (6/pi^2)/S = 1.26877** up to 10^-4. This is, I believe, A–F's "1.263..." of Remark
  rem:Davg (their weight (1-q/Q)^2; the third digit differs, their normalisation is not stated).
MV's weighted inequality gives 3/(2S) = 3.1306, the classical one 2/S = 4.17 (h5). The constant C*_w is sharp for
Q^{1+eps} <= N: take c_n = e(n x) at the maximising x (the bound is the norm of a Toeplitz-type form, see Lemma 1).

**Consequence for the family certificate [N], given the rest of h5's §3 (not re-proved here):**
| weight | K | simple and on the line | distinct | lambda |
|---|---|---|---|---|
| MV (h5) | 3.1306 | 0.7534 | 0.8767 | 1.75 |
| w = 1 on (Q_0, Q] | 2.0870 | **0.7873** | **0.8937** | 1.75 |
| w = (1-u)^2 | 1.2688 | **0.8484** | **0.9242** | 1.99 |
(w = (1-u)^2 at lambda = 1.5: 0.8338 / 0.9169 — above A–F's stated 0.811 / 0.905.)  D'Souza's 0.9059 uses hybrid
zero-density theorems; these numbers use none.

## 1. Lemma 1 (Fejér-majorant duality) [R]
Let mu = sum_r mu_r delta_{x_r} be a finite positive measure on R/Z, H >= N an integer, and
F_H(x) := (1/H)(sin pi H x / sin pi x)^2 = sum_{abs(j)<H} (1 - abs(j)/H) e(jx) >= 0. Then for all c_n (M < n <= M+N)
  sum_r mu_r abs(S(x_r))^2 <= (1 - N/2H)^{-1} sup_x (mu * F_H)(x) sum abs(c_n)^2,     S(x) = sum c_n e(nx).
*Proof.* By duality it suffices to show sum_{n} abs(sum_r b_r mu_r^{1/2} e(n x_r))^2 <= Delta sum abs(b_r)^2. Put n_0 := M + ceil((N+1)/2) and
W(n) := (1 - N/2H)^{-1} (1 - abs(n - n_0)/H)_+; then W >= 1 on (M, M+N] and sum_n W(n) e(nx) = (1 - N/2H)^{-1} e(n_0 x) F_H(x). Hence
the left side is at most sum_{r,s} b_r conj(b_s) (mu_r mu_s)^{1/2} (1-N/2H)^{-1} e(n_0(x_r-x_s)) F_H(x_r - x_s), and by
abs(b_r b_s)(mu_r mu_s)^{1/2} <= (abs(b_r)^2 mu_s + abs(b_s)^2 mu_r)/2 and F_H even, >= 0, this is <= (1-N/2H)^{-1} sum_r abs(b_r)^2 (mu*F_H)(x_r). QED

## 2. Theorem 2 (local density of weighted Farey points) [R]
Let mu := sum_{Q_0<q<=Q} (w(q/Q)/q) sum*_{a mod q} delta_{a/q}. For every integer H <= Q^{2-6 eps},
  sup_x (mu * F_H)(x) <= C*_w Q + O_{w,eps}(Q^{1-2 eps+o(1)}).
*Proof.* Fix x. Put R := Q^{1-3 eps}; by Dirichlet there are coprime b, r with 1 <= r <= R, theta := x - b/r, abs(theta) <= 1/(rR).
WLOG theta >= 0. For a reduced a/q with q > Q_0 > R, a/q != b/r; lift a so that y := a/q - b/r lies in (-1/2, 1/2] and put
k := ar - bq, a non-zero integer with y = k/(qr), abs(k) <= Qr/2. Conversely, for fixed k the admissible q are those with
q == -k b^{-1} (mod r) (then a = (k + bq)/r), and (a,q) = 1.
(i) *Coprimality on a spoke.* gcd(a,q) divides k. For a prime p dividing k: if p does not divide r, then p | q forces p | a;
if p | r then p | q automatically and, writing q = q_k + rj, a = a_0 + bj, p | a iff j lies in one class mod p. So for
squarefree d | k the set {q == q_k (r), d | gcd(a,q)} is exactly one residue class mod rd, and
1_{(a,q)=1} = sum_{d | k} mu(d) 1_{d | (a,q)}. (Check: observed density phi(k)/k for seven (b, r, k), `t3b_check.py` (1) [N].)
(ii) *Riemann sums.* For h of bounded variation and compact support, abs(sum_{q == c (m)} h(q) - (1/m) int h) <= V(h)
(compare h(q) with its mean over [q, q+m)). Apply this to h_k(q) := (w(q/Q)/q) 1_{Q_0<q<=Q} 1_{q >= 2 abs(k)/r} F_H(theta - k/(qr)):
  spoke sum M_k := sum_{q on spoke k, (a,q)=1} h_k(q) = (phi(abs(k))/abs(k)) (1/r) int h_k + O(tau(k) V(h_k)).
(iii) *Main term.* Substituting y = k/(qr) (dq/q = -dy/y) and summing over k of each sign,
  sum_k (phi(k)/k)(1/r) int h_k = int_{-1/2}^{1/2} F_H(theta - y) rho(y) dy,
  rho(y) := (1/(abs(y) r)) sum_{abs(y) r Q_0 < k <= abs(y) r Q} (phi(k)/k) w(k/(abs(y) r Q)) <= Q Phi(abs(y) r Q) <= Q C*_w,
Phi(t) := (1/t) sum_{k<=t} (phi(k)/k) w(k/t). Since F_H >= 0 has integral 1 over a period, the main term is <= C*_w Q.
(iv) *Error term.* On (Q_0, Q], w(q/Q)/q <= 1/Q_0 with variation << (1 + V(w))/Q_0, and q -> k/(qr) is monotone onto
J_k = [k/(Qr), k/(Q_0 r)) (k > 0). With D_k := dist(theta, J_k): F_H(u) <= min(H, 1/(4 H u^2)) and the variation of F_H over
{abs(u) >= D} is << min(H, 1/D). Hence V(h_k) << (1/Q_0) min(H, 1/D_k). With t := theta r Q <= Q/R, t_0 := theta r Q_0:
D_k >= abs(k)/(Qr) for k < 0, D_k = (k - t)/(Qr) for k > t, D_k = (t_0 - k)/(Q_0 r) for 0 < k < t_0. So the number of k with
D_k <= 1/H is <= t + 3Qr/H + 3, and sum over the others of 1/D_k is << Qr log Q. With tau(k) << Q^{o(1)}:
  sum_k tau(k) V(h_k) << Q^{o(1)} Q_0^{-1} (H t + Qr + H + Qr log Q) << Q^{o(1)} (H Q^{eps}/R + Q^{eps} R + H Q^{eps-1}),
which is << Q^{1-2eps+o(1)} for R = Q^{1-3eps}, H <= Q^{2-6eps}. QED
*Proof of Theorem LS.* Gauss-sum step [K, Gallagher 1967; one-line proof]: for chi primitive mod q and every n,
chi(n) tau(conj chi) = sum_{a mod q} conj(chi)(a) e(an/q), so tau(conj chi) sum_n c_n chi(n) = sum*_a conj(chi)(a) S(a/q); summing the squares over ALL chi mod q
(orthogonality) and using abs(tau)^2 = q for the primitive ones gives q sum*_chi abs(sum c_n chi(n))^2 <= phi(q) sum*_a abs(S(a/q))^2. So the
left side of Theorem LS is <= sum_r mu_r abs(S(x_r))^2 with mu as in Theorem 2.
Apply Lemma 1 with H := ceil(N Q^{eps}) <= Q^{2-6eps} and Theorem 2. The harmonics count: sum_{q<=y} phi*(q)/phi(q) = S y + O(y^{1/2+o(1)})
and partial summation. QED

Numerical confirmation of Theorem 2 [N] (`t3b_check.py` (2), Q = 3000, Q_0 = 1500, H = 40Q, 2.05 10^6 points): the smoothed
density at x = t/Q and at x = 1/2 + t/(2Q) agrees with Q Phi(t) (truncated at k > t Q_0/Q) to 2–3 digits for
t = 1.1 … 9.7 (e.g. w = 1: 0.7652 / 0.7611 vs 0.7692 at t = 1.3; 0.2734 / 0.2736 vs 0.2732 at t = 4.27); at 150 random x
the maximum is 0.549 Q (w = 1; bound 1) and 0.068 Q (w = (1-u)^2; bound 0.2026).
Caveat seen in the first run: with H ~ Q Q_0 single atoms a/q, q ~ Q_0, of mass w/q are visible (height H w/(q)); the
hypothesis H <= Q^{2-6eps} with Q_0 = Q^{1-eps} is what removes them — small moduli must be excluded (or weighted by an
extra factor), exactly the N/q_min term in MV.

## 3. The other items of T3b
* MV73 constant [K]: Montgomery–Vaughan, "The large sieve", Mathematika 20 (1973), Theorem 1:
  sum_r abs(S(x_r))^2 (N + (3/2) delta_r^{-1})^{-1} <= sum abs(a_n)^2 — the 3/2 is correct (it is 1/pi times the 3 pi/2 of the
  weighted Hilbert inequality, which A–F use as Lemma 2.3; Preissmann 1984 improves 3/2 to about 1.3154). Quoted from memory
  and from h5's OCR; I did not re-open the source. It is no longer needed if Theorem LS is used.
* Farey gap [R]: for reduced a/q != a'/q' with q, q' <= Q, abs(a/q - a'/q') >= 1/(qq') >= 1/(qQ); restricting q to (Q_0, Q]
  only removes points, so delta_{a/q} >= 1/(qQ) still holds.
* Diagonal range e^y <= Q^{1-eps} [R, sketch]: sum*_chi chi(n) conj(chi(m)) = sum_{d | (q, n-m)} phi(d) mu(q/d) for (nm, q) = 1, so the
  off-diagonal part of sum_q phi(q)^{-1} sum*_chi abs(sum_{n<=N} c_n chi(n))^2 is << sum_{n != m} abs(c_n c_m) tau(n-m) log Q << N^{1+o(1)} sum abs(c_n)^2;
  for N <= Q^{1-eps} this is o(Q sum abs(c)^2): constant 1 (i.e. S Q), as h5 states. Note that no "localisation" is needed to
  apply the large sieve itself: it applies to c_n(y) = a_n I^(y - log n) for all n <= X at once; the split at Q^{1-eps} is
  only needed to get constant 1 for small scales, via abs(A+B)^2 <= (1+eta) abs(A)^2 + (1+1/eta) abs(B)^2 and the L^2 tail
  int_{abs(u)>delta} abs(I^(u))^2 du <= 8/delta against 2 pi T.
* NOT checked by me: (b) trace from the prime side (the bound sum_q phi(q)^{-1} abs(sum*_chi chi(n)) << tau(n-1) log Q and
  Titchmarsh's divisor bound sum_{n<=X} Lambda(n) tau(n-1) << X log X make it plausible for X <= Q^{2-eps}); the Gevrey tail
  for L(s,chi); the uniformity in q of the explicit formula; (d), (e) of h5's sketch. These remain [C].

## 4. Would-be theorem (for the lead)
**Theorem F (conditional on h5 §3 (a),(b),(d),(e) being written out).** Fix eps > 0, B large, T = (log Q)^B. For
primitive chi mod q, Q^{1-eps} < q <= Q, with weights (1 - q/Q)^2/phi(q),
  sum_chi omega_chi N_0^s(T, 2T; chi) >= (0.848 - o(1)) sum_chi omega_chi N(T, 2T; chi),   distinct: 0.924,
and with weights 1/phi(q): 0.787 and 0.893. No zero-density estimate, no GRH. The only number-theoretic inputs beyond
A–F are Theorem LS above and Titchmarsh's divisor bound.
