# Exact certificates for the bucket game (notes.md §2.2–2.3)

## Claim

For B = 2, 4, 8, 16, 32 the bucket game with corner rank bounds satisfies **n\*(B) ≤ c_B**, with

| B | c_B (exact rational in the file) | exact max load found | rate ≥ 1/c_B | file |
|---|---|---|---|---|
| 2 | 1202907609/10⁹ = 1.202907609 | 1.2029076087 | 0.8313190 | `cert_B2.json` |
| 4 | 1.201875498 | 1.2018754976 | 0.8320329 | `cert_B4.json` |
| 8 | 1.198602702 | 1.1986027016 | 0.8343048 | `cert_B8.json` |
| 16 | 1.196431439 | 1.1964314382 | 0.8358189 | `cert_B16.json` |
| 32 | 1.195153569 | 1.1951535682 | 0.8367126 | `cert_B32.json.gz` |

All c_B are < 4/3 (routing). **So the protocol family of notes §2.3 has rate ≥ 1/c_B > 3/4.** The best is
rate ≥ 0.83671 at B = 32. The B = 2 bound is also checked in Lean (`../../lean/PortsLean/ProtocolCert.lean`),
with rounder data and c = 30073/25000 = 1.20292.

What this certifies: only the finite game, i.e. the arithmetic step "for every type there is a mixture
with all six edge loads ≤ c_B" (step 3 of §2.3). The tensor side (crossing identity [AN] B.2, Lemma A.3,
time-sharing, the cover with its shared index, asymptotics of the class sizes) is not covered here. The
referee's report reviews that part.

Lower bound (B = 2, `verify_dual_B2.py`): an exact rational edge price gives
**1.2029076080 ≤ n\*(2) ≤ 1.2029076090**. So c_2 is tight to 10⁻⁹. The exact value is
n\*(2) = 29/27 + 11√10/270 = 1.20290760838 (root of 270x² − 580x + 307). The upper half of this is exact:
the mixture below with α = 7/18 − √10/90 and γ = 5/9 − 13√10/90 makes all three distinct loads equal to this
number, checked symbolically. The matching lower bound holds only to 4·10⁻¹⁰ (the rational price).

## The game, exactly as certified

Units: Q = log D₂ = 1, P = log D₁ = 1/3 (the ratio 1 : 3 of §2.1), A = P + Q = 4/3. The parties are
u₁, u₂, v₁, v₂, v₃, and there are six supply edges u_k v_i. Pairs: {v₁v₂}, {v₂v₃}, {v₁v₃}. For the pair
(v_i, v_j), i < j, set (a, c, b, d) = (u₁, u₂, v_i, v_j).

- **Buckets.** x = N/n₀ ∈ [0, T], T = 2(P² + Q²) = 20/9, cut into B equal intervals [x_k, x_{k+1}]. Bucket k has
  r ≤ min(√(T − x_k), A) on the cut {a,b}|{c,d}, from [AN] B.2(c) with N′ = Θ − N, and
  r′ ≤ min(√(x_{k+1}), A) on the cut {a,d}|{b,c}, from B.2(b). These are the corner bounds of `buckets.py`.
- **Options** for one pair: (kind, o, o′) with hubs o, o′ any of the five parties. Kind 0 ("c") has wires
  a–o: P, b–o: Q, c–o′: P, d–o′: Q, o–o′: r. Kind 1 ("b") has wires a–o: P, d–o: Q, b–o′: Q, c–o′: P, o–o′: r′.
  A wire with equal ends costs nothing. The four options of §2.1 are special cases, and so is plain
  routing (o = o′).
- **Routing.**
  - A wire on a supply edge uses that edge.
  - u₁u₂ goes along u₁–v_l–u₂, split by rational fractions.
  - v_iv_j goes along v_i–u_k–v_j, split by rational fractions.
- **Value.** For each type (k₁₂, k₂₃, k₁₃) ∈ [B]³, take the minimum over mixtures and splits of the largest
  edge load. n\*(B) is the maximum of this over all types.

**Both implementations agree.** `level1_lp.py` (notes) routes as above. The referee's `mylp.py` also allows
every simple path of K₂,₃, which is more freedom, so its value can only be lower. On every type for
B = 2, 4, 8, the two values differ by at most 4·10⁻¹⁰. That is the size of the √-rounding, so in fact
longer paths never help. The certificates use the more restricted model, the notes' one, which is the
conservative choice. Both use all 25 ordered hub pairs and both pairings.

## Rounding (why it is sound)

The only irrational coefficients are the corner rank bounds √(jT/B). Each one is replaced by
up(s) = ⌈10⁹·√s⌉/10⁹. `verify.py` computes this with `math.isqrt` and asserts up(s) ≥ 0 and up(s)² ≥ s,
then caps the result at A. These are the only places rounding happens; P, Q, A, T and x_k are exact rationals.

Why rounding up is safe:
- Every edge load is Σ (nonnegative weight × nonnegative routing fraction × wire length).
- Every wire length is P, Q, r or r′.
- So each load is a nondecreasing function of (r, r′). A mixture whose loads are ≤ c with r̂ ≥ r therefore
  has loads ≤ c with the true r.

On the protocol side, a hub wire of log-dimension r̂ is at least as large as the rank. A term of rank ρ is a
restriction of the hub network with ⟨ρ⟩, and ⟨ρ⟩ is a restriction of ⟨ρ̂⟩ when ρ ≤ ρ̂ (padding). The cap
r ≤ A is the trivial rank bound rank ≤ D₁D₂. The dual lower bound rounds the other way, using ⌊10⁹√s⌋/10⁹.

The o(1) corrections of §2.3, step 1 (class sizes, O(log Θ) bucket sums) are handled as in the notes. The
loads are linear in (r, r′) with coefficients ≤ 1, so the same mixtures give max load ≤ c_B + o(1) at the
actual ranks, and the rate tends to ≥ 1/c_B.

## Files

| file | content |
|---|---|
| `verify.py` | Standalone verifier, standard library only (`fractions`, `json`, `math`, `gzip`). Run `python3 verify.py cert_B2.json cert_B4.json cert_B8.json cert_B16.json cert_B32.json.gz` (≈ 6 s). It rebuilds the bucket bounds and every option's wires from (kind, o, o′), then checks four things for every type: the weights are ≥ 0 and sum to 1 per pair, each option is well formed, the routing fractions are ≥ 0 and sum to 1, and the exact max of the six loads is ≤ c. It also checks that every type in [B]³ is present and that c < 4/3. |
| `cert_B*.json` | Data: `B`, `c`, then for each type `mix[e] = [[kind, o, o′, "p/q"], …]`, `route_u1u2` (fractions via v₁, v₂, v₃) and `route_vv[p]` (fractions via u₁, u₂). |
| `verify_dual_B2.py` | Exact lower bound for B = 2: a price y on the edges (sum 1) and the y-shortest-path cost of the cheapest option per pair, taken over all paths (so it bounds both models). |
| `make_certs.py` | Generator for B ≥ 4. It solves a float LP per type (HiGHS), rationalises (denominators ≤ 10⁷), renormalises exactly and sets c_B just above the exact max. Run `python3 make_certs.py 4 8 16 32`. Do not pass 2: that would overwrite the clean B = 2 file. |
| `make_cert_B2.py` | Clean B = 2 certificate. Two orbits under the order-12 symmetry group (S₃ on the v's × u₁↔u₂); the other types are transported by relabelling parties. |
| `gen_lean.py` | Writes `../../lean/PortsLean/ProtocolCert.lean` after checking the same data in Python. |
| `game_values_sym.py` | Float n\*(B) over orbit representatives, for B = 64 and 128. |

The B = 2 mixture. Acyclic type (1,1,1): all pairs in the bucket "r ≤ √10/3, r′ trivial".
- Pair v₁v₂: "c via u₁" (o = u₁, o′ = v₂) with weight α, "c via u₂" (o = v₁, o′ = u₂) with weight 1−α.
- Pair v₂v₃: the same two options with weights 1−α and α.
- Pair v₁v₃: plain routing through u₁ and through u₂ with weight γ each, "c via u₁" / "c via u₂" with
  weight ½−γ each.
- The u₁u₂ wires go through v₂.

This gives three edge loads:
- L₁ = 1 + 2α/3 − γ/3 on u₁v₁ and u₂v₃;
- L₂ = 1 + α(ρ − 2/3) + 2γ/3 on u₁v₂ and u₂v₂;
- L₃ = 3ρ/2 − (α+γ)ρ + γ on u₁v₃ and u₂v₁.

Cyclic type (1,1,0): every pair ½ via u₁ and ½ via u₂, and every edge carries (A + ρ)/2 = 1.19372. The
remaining six types are relabellings.

Lean (`PortsLean/ProtocolCert.lean`, imported from `PortsLean.lean`; `lake build` passes):
- Data: ρ̂ = 10541/10000, α = 283/800, γ = 4939/50000.
- `rhoHat_bound : √(10/9) ≤ ρ̂`.
- `cert_wellFormed` and `cert_loads`, proved by `decide +kernel`, which is kernel evaluation of ℚ
  arithmetic, not `native_decide`.
- `n_star_two_le`: for every τ ∈ {0,1}³ there is a well-formed entry with all six loads ≤ 30073/25000,
  this number is < 4/3, and ρ̂ ≥ √10/3.
- Axioms: propext, Classical.choice, Quot.sound.

## n\*(B) for larger B (floating point, task 3)

| B | n\*(B) | n\*(B) − (4+√10)/6 | worst type |
|---|---|---|---|
| 2 | 1.2029076 | 9.19e-3 | (1,1,1) |
| 4 | 1.2018755 | 8.16e-3 | (1,1,1) |
| 8 | 1.1986027 | 4.89e-3 | (3,3,3) |
| 16 | 1.1964314 | 2.72e-3 | (7,7,7) |
| 32 | 1.1951536 | 1.44e-3 | (15,15,15) |
| 64 | 1.1944556 | 7.43e-4 | (31,31,31) |
| 128 | 1.1940901 | 3.77e-4 | (63,63,63) |

(4+√10)/6 = 1.1937129. From B = 8 on, the gap halves with each doubling (ratios 1.80, 1.89, 1.94, 1.97),
so it is ≈ 0.048/B. Richardson extrapolation gives 2n\*(128) − n\*(64) = 1.193725, which is 1.2·10⁻⁵ above
(4+√10)/6 and consistent with that limit.

The worst type is always (B/2−1)³, equivalently (B/2)³ under u₁↔u₂. This is the bucket next to the middle,
in all three pairs, with the orientation that makes the type acyclic. Its corner (√(T/2 + T/B), √10/3)
touches the all-middle point. The type (B/2−1, B/2−1, B/2) is the cyclic version of the same buckets. Its
value is exactly (4+√10)/6 for every B tested, and it comes second.
