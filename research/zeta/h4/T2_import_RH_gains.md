# T2 — importing the RH-conditional gains (Cheer–Goldston, CGdL, CGG / Bui–Heath-Brown) through the rank–trace device

Helper h4, 10 Nov 2026. Tags: [R] proved here (complete, elementary), [K] known + citation, [N] numerical, [C] assessment.
Notation of Alpöge–Furman (A–F, `paper-v5-draft18.tex`): zeros rho = beta + i gamma, gamma_rho := (rho-1/2)/i (complex off the line),
rho* := 1 - conj(rho) (the partner; gamma_{rho*} = conj(gamma_rho)); s1, s2, p = numbers of simple on-line zeros, multiple on-line
points, off-line pairs; N = zeros with multiplicity; L = log(T/2pi); x_rho := gamma_rho L/2pi (normalised ordinate).

## 0. Verdict in one table

| RH-conditional result | where RH enters | does the device replace it? |
|---|---|---|
| Montgomery 2/3, Montgomery–Taylor 0.6725 | zero side read as a positive sum over real ordinates | yes — this is A–F Thm A [K] |
| CGG (1.2): N_d >= 5/6 via (m-1)(m-2)>=0 | same | yes — A–F Thm A(ii), §7.2(c) [K] |
| Cheer–Goldston 0.67275 (PAMS 118 (1993)) | zeros real, so (i) kernel r(u) >= 0 termwise and (ii) *consecutive* zeros have differences u, v, u+v that cannot all be zeros of the MT kernel | yes — "stability-enhanced rank–trace" (ainta repo 11 Aug 2026: 0.6730085; Knausgård arXiv:2610.08965: 0.673538; ceiling of this local scheme 0.67383) [K]. Nothing left to import. |
| Chirre–Gonçalves–de Laat 0.6792 (uses F(alpha) >= 0 for abs(alpha) > 1) | zero-side inequality  sum f(x_rho - x_rho') >= f(0) sum m^2  for f >= 0 that is NOT positive-definite | **no**: Prop. 2 below [R] — every f with f^ <= 0 (not identically 0) outside [-1,1] has f(iy) -> -infinity, and one off-line pair of depth y violates the zero-side inequality by an unbounded amount. Needs a "narrow box" hypothesis; the density hypothesis is not enough (§2.3). Also F >= 0 is automatic for every symmetric configuration, so it can never lift the bandwidth-one ceiling 0.68185. |
| CGG 1998 / Bui–Heath-Brown 19/27 (mollified discrete moments of zeta') | exactly one line: S2 = sum B zeta'(rho) B zeta'(1-rho) equals sum abs(B zeta'(rho))^2 only on RH (BHB p. 4: "this is the only place we need RH") | **no**: Prop. 1 [R] gives the exact defect E_off; the device needs a d ~ N dimensional family and a two-point second moment, and the natural matrix versions need a mollified *fourth* discrete moment with pair-correlation kernel (G_2) or give a worse constant even granting all missing inputs (G_1: about 0.57 [C]) (§1.3). |

So of the three RH-conditional improvements named in T2, one is already imported by others, and for the other two the
obstruction is precise and of the same nature: the RH proofs use a *non-analytic* or *non-positive-definite* zero-side
inequality, while the device can only handle zero-side quantities that are Hermitian squares in a Hilbert space realisation.

## 1. Conrey–Ghosh–Gonek / Bui–Heath-Brown

### 1.1 Where RH is used [K]
BHB (arXiv:1302.5018, BLMS 45 (2013)), §2. Let f(s) := zeta'(s)B(s), B(s) = sum_{k<=y} b(k)k^{-s}, b(k) = mu(k)P(log(y/k)/log y),
y = T^theta, theta < 1/2, P real. Lemma 1 + Lemma 2 + (5)–(7) there give, **unconditionally** ("Up to this point, all the
analysis is unconditional"; Lemma 2 removes GLH),
  S1 := sum_{0<gamma<=T} f(rho)          ~ (T L^2/2pi) (1/2 + theta int P),
  S2 := sum_{0<gamma<=T} f(rho) f(1-rho) ~ (T L^3/2pi) (1/3 + theta int P + theta^2 (int P)^2 + (1/12 theta) int P'^2),
(sums with multiplicity; multiple zeros contribute 0), and with P(x) = -theta x^2 + (1+theta)x, theta -> 1/2:
S1 ~ (19/24) N L, S2 ~ (57/64) N L^2. Then: "Assuming RH we have S2 = sum abs(B zeta'(rho))^2. Note that this is the only
place we need RH", and Cauchy–Schwarz N^s >= abs(S1)^2 / sum abs(f(rho))^2 gives 19/27.
CGG (Proc. LMS 76 (1998)) is the same argument with GLH for the error term M_{nu,3}; their (1.1)/(1.2) are the two
ways of passing to N_d ((m-2)(m-3) >= 0, resp. (m-1)(m-2) >= 0).

### 1.2 The exact unconditional statement and the defect [R]
**Proposition 1.** Let f be any function analytic near the zeros with real Dirichlet/Taylor coefficients (f(conj s) = conj f(s)),
S1 := sum f(rho), S2 := sum f(rho) f(1-rho) over the zeros with 0 < gamma <= T (with multiplicity). Put, over the off-line
pairs {rho, rho*} in the window, u := f(rho), v := f(rho*), and
  E_off := sum_{pairs} abs(f(rho) - f(rho*))^2,   D_off := sum_{pairs} (u + v),   C_off := sum_{pairs} 2 Re(u conj v).
Then (a) sum_rho abs(f(rho))^2 = S2 + E_off;   (b) S1 = sum_{on} f(rho) + D_off, S2 = sum_{on} abs(f(rho))^2 + C_off;
(c) for f = zeta' B:  N^s(T) >= S1^2/(S2 + E_off),   s1 >= abs(S1 - D_off)^2/(S2 - C_off);
(d) no inequality s1 >= Psi(S1,S2,N) or N^s >= Psi(S1,S2,N) with Psi > 4 can follow from this structure alone: every pair
(S1, S2) of real numbers is realised with s1 = 0 and two off-line pairs (N^s = 4).
*Proof.* The window is stable under rho -> rho*. For on-line rho, 1 - rho = conj(rho), so f(rho)f(1-rho) = abs(f(rho))^2. For
a pair, 1 - rho = conj(rho*), hence f(1-rho) = conj(v) and f(1-rho*) = conj(u); the pair contributes u conj(v) + v conj(u)
= 2Re(u conj v) to S2 and abs(u)^2 + abs(v)^2 = 2Re(u conj v) + abs(u-v)^2 to sum abs(f)^2. This is (a), (b). (c) is Cauchy–Schwarz
over the simple zeros (zeta'(rho) = 0 at multiple zeros), resp. over the simple on-line zeros. (d): write s_j := u_j + v_j, t_j := u_j - v_j, so that a pair contributes s_j to S1 and (abs(s_j)^2 - abs(t_j)^2)/2 to S2. Take
s_1 = S1/2 + R, t_1 = 0, s_2 = S1/2 - R, t_2 = tau (R, tau real): the sums are S1 and S1^2/4 + R^2 - tau^2/2, which takes every
real value. QED
With BHB's numbers (c) reads  N^s/N >= (19/27) / (1 + (64/57) E_off/(N L^2)) (1+o(1)), unconditionally.

**The obstruction, as a lemma someone could try to prove (Lemma O1).** *Show unconditionally
E_off = sum_{off-line pairs, 0<gamma<=T} abs(zeta'B(rho) - zeta'B(1 - conj rho))^2 <= (eps_0 + o(1)) N L^2.*
Then N^s/N >= (19/27)/(1 + 64 eps_0/57): any eps_0 < 0.0417 beats Knausgård's 0.678009 for simple zeros anywhere.
Remarks. (i) E_off is not an analytic function of the zeros, so no contour integral computes it; (ii) abs(u - v) <=
(2 beta - 1) max abs(f') on the horizontal segment, so E_off = o(N L^2) under "all zeros within o(1/L) of the line" given a
bound sum_rho sup abs(f'/L)^2 << N L^2 — a narrow-box theorem, consistent with BGSTB/Goldston–Suriajaya, not unconditional;
(iii) zero-density estimates do not help: they bound the number of deep zeros, not abs(f) on the shallow ones, and A–F only
tell us that at most 0.3264 N zeros are off the line. I see no route to O1.  [C]

### 1.3 Why the rank–trace device does not rescue it
The device needs: a Hilbert space with one vector per zero, a Hermitian form whose on-line part is PSD of rank <= (the count
wanted) and whose off-line part has positive index <= #pairs, the trace, and the Hilbert–Schmidt norm, with dimension d ~ N.
* (S1, S2) are one-point statistics: S2 is the *trace* of an indefinite form; a trace alone does not bound inertia — this is
  Prop. 1(d).
* The space of mollifiers has dimension y <= T^{1/2} << N (shifts B(s + i alpha) stay inside it), so the Hermitian form
  (B,B') -> sum zeta'(rho) zeta'(1-rho) B(rho) conj(B')(1-rho) compressed to mollifiers can certify at most T^{1/2} zeros.
* A d ~ N dimensional family needs the Gabor vectors v_rho of A–F. The two natural matrices are, with a_rho := f(rho)/L:
  G_2 := (aL^2)^{-1} sum_rho a_rho a~_rho v_rho v_rho^T (a~_rho := f(1-rho)/L): real symmetric, on-line part PSD of rank <= s1
  (multiple zeros vanish!), off-line pairs give (1,1) blocks, so n_+(G_2) <= s1 + p_1 and  [R]
      s1 + p_1 >= (tr G_2)^2/norm(G_2)_HS^2,   s1 >= 2 (tr G_2)^2/norm(G_2)_HS^2 - N.
  tr G_2 = S2/L^2 (1+o(1)) is BHB's S2, but norm(G_2)^2 = sum_{rho,rho'} a a~ a' a~' (v_rho . v_rho')^2 is a mollified *fourth*
  discrete moment of zeta' with a pair-correlation kernel — far beyond any known technique (even sum abs(zeta'(rho))^4 is open on RH).
  G_1 := (aL^2)^{-1} sum_rho a_rho v_rho v_rho^T: rank G_1 <= N^s, so N^s >= abs(tr G_1)^2/norm(G_1)_F^2 [R], where
      norm(G_1)_F^2 = (aL^2)^{-2} sum_{rho,rho'} f(rho) f(1-rho') (v_rho . v_rho')^2 / L^2
  is an *analytic* double sum (because conj f(rho') = f(1 - rho'*) and the zero set is *-symmetric), equal to
  int g(u) A(e^u) A~(e^{-u}) du with A(x) := sum_rho zeta'(rho) B(rho) x^{rho-1/2}. So the missing input is
  **Hypothesis TW(lambda, theta)**: an L^2(du) asymptotic for the twisted first moment A(x), 1 <= x <= T^lambda, real x.
  Integer x >= 1 against B = 1 is the easy (Gonek-lemma) direction; x < k (k <= y) needs BHB's character/large-sieve
  analysis for real twists. Even granting TW(1, 1/2): if a_rho has mean c = 19/24 and second moment c_2 = 57/64 and is
  uncorrelated with the local spacing, norm(G_1)^2 ~ (c_2 + c^2 (R-1)) N with R = 4/3, and the bound is
  c^2/(c_2 + c^2/3) = 0.570 < 2/3: the off-diagonal Gram interaction of a bandwidth-one family costs more than the
  mollifier gains.  [C] (heuristic, GUE pair correlation, independence assumption)
Conclusion: the BHB/CGG gain is not importable; the precise missing statement is Lemma O1, and the matrix reformulations
either need a 4th moment (G_2) or lose (G_1).

## 2. Chirre–Gonçalves–de Laat (positivity of F outside [-1,1]) and Cheer–Goldston

### 2.1 What is and is not unconditional [K]/[R]
Under RH, for f >= 0 on R, even, f(0) = 1: sum_{rho,rho'} f(x_rho - x_rho') >= sum m_rho^2 (drop the terms with gamma != gamma'),
and the left side is N int f^(alpha) F(alpha) d alpha <= N (f^(0) + int_{-1}^{1} f^(alpha) abs(alpha) d alpha) if f^ <= 0 outside [-1,1], since F >= 0.
Unconditionally: (i) F(alpha) on abs(alpha) <= 1 is the same (Aryan; BGSTB arXiv:2306.04799); (ii) F >= 0 holds for *every* finite
multiset Z symmetric under conjugation, since sum_{z,z'} e^{2 pi i alpha (z - z')} = abs(sum_z e^{2 pi i alpha z})^2 (relabel z' -> conj z') [R].
Consequence [R]: "F >= 0 beyond 1" is not information about zeta; any law of symmetric configurations with the correct F on
[-1,1] satisfies it, in particular the A–F / Knausgård ceiling law. Hence **no unconditional argument using F on [-1,1]
plus positivity of F elsewhere can exceed 0.68185** (simple on line) / 0.84093 (distinct).
What fails unconditionally is only the zero-side inequality.

### 2.2 The zero-side inequality in configuration form
For a finite multiset Z of normalised ordinates, symmetric under conjugation, define
  I(f):  sum_{z,z' in Z} f(z - z') >= 4 abs(Z) - 3 s1 - 4 s2 - 4 p.
A–F Lemma 3.2 + Prop. 4.1 (in the untruncated space L^2(psi), where the Gram kernel of the vectors e_z(t) = e^{2 pi i z t}
is k(z - conj z'), k = psi^/psi^(0)) say: **I(k^2) holds whenever psi >= 0** (k positive-definite) [K]; numerically
confirmed on random configurations, `check_config_ineq.py` (a) [N]. Since I(f) is linear in f, it holds on the convex
hull of {k^2 : k positive-definite, k(0) = 1}; all such f have f^ = mixture of psi*psi >= 0.

**Proposition 2 (no-go) [R].** Let f be entire, real and even on R, f(0) = 1, f(z) = int f^(alpha) e^{2 pi i alpha z} d alpha with
int abs(f^(alpha)) e^{c abs(alpha)} d alpha finite for all c. (a) If f(iy_0) < 1 for some real y_0, then I(f) fails for
Z = {i y_0/2, -i y_0/2}; more generally a certificate "sum f >= a abs(Z) - b s1 for all symmetric Z" forces f(iy) >= a - 1 for all y.
(b) If f^ <= 0 on abs(alpha) > 1 and f^ is not a.e. zero there, then f(iy) -> -infinity as y -> infinity; so no (a, b) works.
*Proof.* (a) For the single pair, abs(Z) = 2, s1 = s2 = 0, p = 1, sum f = 2 f(0) + 2 f(i y_0) (differences 0, 0, +- i y_0, f even).
(b) f(iy) = int f^(alpha) cosh(2 pi y alpha) d alpha <= cosh(2 pi y) int_{-1}^{1} abs(f^) - int_{abs(alpha) > 1+delta} abs(f^) cosh(2 pi y (1+delta)),
and the second integral is positive for some delta > 0. QED
Example (`check_config_ineq.py` (b)) [N]: f(x) = (1 + x^2/(1 - 1/2pi)) e^{-pi x^2} >= 0, f^ proportional to (1 - alpha^2) e^{-pi alpha^2};
a single pair at depth eta has f(2 i eta) = 1.77, -4.4, -6359 for eta = 0.3, 0.5, 0.8.
In matrix language: f = abs(k)^2 with k^ = psi signed means replacing the Hilbert space L^2(psi) by the Krein space
(L^2(abs(psi)), J = sign psi); the CGdL quantity is tr(GJGJ) = norm(G_{++})^2 + norm(G_{--})^2 - 2 norm(G_{+-})^2, and the rank–trace lemma is
false for tr(GJGJ): Q = t(aa* - bb*) with a, b J-null and a*Jb = 1 has n_+(Q) = 1, tr(QJ) = 0, tr(QJQJ) = -2t^2. [R]

### 2.3 What hypothesis would repair it [C]
With eta = (beta - 1/2) L/2pi the self-term of a pair is about -c T^{2 lambda' (beta - 1/2)} where f^ < 0 near abs(alpha) = lambda' > 1. For the
certificate to survive one needs sum_{beta > 1/2} T^{2 lambda'(beta-1/2)} = o(T log T). Under the density hypothesis
N(sigma,T) << T^{2(1-sigma)+eps} the sum is T^{1 + (2 lambda' - 2)(sigma - 1/2) + eps}, still too large for every lambda' > 1; one needs
essentially all zeros within O(1/log T) of the line (Goldston–Suriajaya box hypotheses). So CGdL's 0.6792 is importable
exactly under a narrow-box hypothesis and not otherwise by this route. The structural reason (h1's remark, sharpened):
removing RH costs the freedom to use non-positive-definite k; with k positive-definite, f^ = psi*psi >= 0, and the sign
condition f^ <= 0 outside [-1,1] collapses to supp f^ in [-1,1], where Montgomery–Taylor is optimal (CCLM17 Cor. 14).

### 2.4 Cheer–Goldston [K]
Their gain over MT comes from keeping part of the discarded sum over gamma != gamma': with r = the MT kernel, three consecutive
ordinates have differences u, v, u+v, not all zeros of r. RH is used only to order the zeros on a line and for r >= 0
termwise. The unconditional substitute is the defect term tr Psi(V^T V), Psi(t) = (t-1)^2 on [0,2], 2t-3 beyond, in
  norm(P+Q)_F^2 >= 4 tr(P+Q) - 3r - 4b + tr Psi(V*V)        (ainta, Lemma 1; I re-checked the proof: correct)
evaluated on blocks of consecutive simple on-line zeros. This line is fully exploited (record 0.6736389, ceiling 0.67383
for local-interaction schemes per Knausgård Prop. 7.3 — see h2/novelty.md). Not worth more effort.

## 3. What would be worth doing next (for the board)
1. Lemma O1 (bound E_off) is the single statement that would import 19/27; I rate it out of reach.
2. Hypothesis TW (L^2 Landau–Gonek formula for sum zeta'(rho) B(rho) x^rho, real x) is a concrete, probably provable
   unconditional statement giving *new two-point data that vanishes on multiple zeros* (zeta'-weighted form factors
   F_1 = sum zeta'(rho) x^{i(gamma - gamma')}, F_2 = abs(sum zeta'(rho) x^{i gamma})^2). It is the only genuinely new arithmetic input I found
   in T2; whether any certificate can use it to pass 0.6819 is open (the naive rank bound gives 0.57).
3. Anything inside bandwidth one is capped at 0.68185 regardless of positivity tricks (§2.1).

## 4. Addenda (after reading the board, 02:05)

### 4.1 Shape of the BHB defect for shallow pairs — why E_off and C_off cannot be assumed small [R]/[C]
Let {rho, rho*} be an off-line pair of simple zeros, delta := 2 beta - 1, and write zeta(s) = (s - rho)(s - rho*) E(s) near it.
Then zeta'(rho) = delta E(rho), zeta'(rho*) = -delta E(rho*) exactly [R]. So with f = zeta' B,
u = delta (EB)(rho), v = -delta (EB)(rho*): **u and v are anti-aligned** whenever EB varies little over the distance delta, and then
  u + v = O(delta^2 (EB)'),   2 Re(u conj v) ~ -2 delta^2 abs(EB)^2 < 0,   abs(u - v)^2 ~ 4 delta^2 abs(EB)^2.
Hence every shallow pair contributes ~0 to S1 and a *negative* amount to S2: unconditionally
S2 = sum_{on} abs(f(rho))^2 - abs(C_off), so BHB's S2 *under*-counts the on-line second moment and
s1 >= S1^2/(S2 + abs(C_off)) with abs(C_off) ~ 2 sum_{pairs} delta^2 abs(EB(rho))^2. A double zero is the limit delta -> 0 (contribution 0).
Complementarity with the device [C]: the Hilbert–Schmidt budget of A–F penalises a pair of normalised depth eta by
2 kappa(eta)^2 - 2, kappa(eta) = int psi~ cosh(4 pi eta t) dt (flat window: sinh(2 pi eta)/(2 pi eta); the pair block has
eigenvalues 1 + kappa and -(kappa - 1), HS^2 = 2 + 2 kappa^2 against the flat charge 4) [R for an isolated pair], i.e. it is blind to
shallow pairs and strong against deep ones, while the zeta'-weights are tiny on shallow pairs (order eta) and uncontrolled on
deep ones. A hybrid would need an unconditional bound for sum over off-line zeros of delta^2 abs(EB(rho))^2, i.e. a discrete
second moment at off-line points: this is Lemma O1 again in sharper form. Not available.

### 4.2 Aryan's imaginary-part identity (arXiv:2610.12853) carries no data beyond F on [-1,1] [R]
Thm 1 there: Im Z(1/2+it) = sum_rho A(L(gamma_rho - t)) + O(1/L), A(z) = 2 int_0^1 (1-u) sin(uz) du, the sum being analytic
in the zeros and real by the *-symmetry. This is a *linear* statistic with a test function of Fourier support [-1,1]
(in units of L). Every quadratic average of it — int abs(Im Z)^2 dt, sum_gamma Im Z(gamma + shift), mixed products with the
Fejér statistic — is of the form sum_{rho,rho'} K(gamma_rho - gamma_rho') with K^ supported in [-1,1], i.e. N int K^(alpha) F(alpha) d alpha
with F the (even) form factor on [-1,1]; the odd part of K integrates to zero against F. So at the two-point level the
"phase channel" is already contained in the A–F data and is subject to the 0.68185 ceiling. It could matter only through
third or higher mixed moments, where the admissible bandwidth drops to 2/3 (rank ceiling lambda N). (Answers h2 Hunch 2,
first candidate, negatively.)

### 4.3 No unconditional O(1) bound for F on (1, 1+eps) is in sight (for h3's remark "any bound F <= B beats 0.6725") [K]/[C]
By the Goldston–Montgomery correspondence F(alpha), alpha > 1, measures the variance of psi(x+h) - psi(x) - h for h = x^{1 - 1/alpha}.
F = O(1) on average means variance << h log x, i.e. RH-quality cancellation in intervals of length x^{eps'}; the trivial
(Brun–Titchmarsh) bound is F << T^{alpha - 1}/log T, and unconditional variance bounds exist only for h >= x^{1/6+eps} (alpha > 6/5)
and save only powers of log. A single zero with beta > 1/2 + 1/(2 alpha) makes F(alpha) genuinely large. So an averaged upper
bound for F just beyond 1 is equivalent to near-RH zero-density information and cannot be an input.

### 4.4 Independent check of h1's Prop. 1.5 [R]
The identity rank P1 = 2 tr P1 + 4 tr Q' - 4 b_+ - norm(G)^2 + D with
D = norm(P1 - Q_- - Pi)^2 + norm(Q_+ - 2 Pi_+)^2 + 2 tr(P1 Q_+) + 4 tr Q_- - 2 tr(Pi Q_-) is correct: expand the two squares using
Q_+ Q_- = 0, tr(P1 Pi) = tr P1, tr Pi = r, tr Pi_+ = b_+, tr(Q_+ Pi_+) = tr Q_+; all terms cancel except norm(G)^2 - 2 tr P1 + r - 4 tr Q' + 4 b_+.
The lower bound D >= sum phi(p_i - 1) is the same statement as ainta's Lemma 1 (Psi(t) = phi(t - 1)), 11 Aug 2026 — prior art.

### 4.5 An observation worth keeping: the certificate is exact once the simple-zero pair energy is known [C]
With D_s := sum_{i != j, simple on-line} k(x_i - x_j)^2 (and no Gram eigenvalue above 2), A–F + stability give
s1 >= (2 - R) N + D_s. If all zeros are simple and on the line, D_s = (R - 1) N and the right side is N: the inequality
loses nothing. So "100%" is equivalent, inside this method, to a lower bound for the off-diagonal pair energy *restricted to
simple zeros*; the total energy R N = sum m^2 + (off-diagonal) is all that primes <= T give. The zeta'-weighted pair sums of
Hypothesis TW, sum_{rho,rho'} f(rho) f(1-rho') k(gamma_rho - gamma_rho')^2 = sum_{i,j simple} a_i conj(a_j) k_ij^2, are exactly weighted versions of
D_s (the weights vanish on multiple zeros and are O(depth) on shallow pairs). Turning a weighted energy into a lower bound
for D_s needs control of the fluctuation of a_i (a fourth moment), so I do not have a theorem; but this is the only
mechanism I see by which data from primes <= T could exceed the bandwidth-one ceiling for zeta itself.
