# MC222 in Lean: the multiplicative complexity of 2×2 matrix multiplication over F₂ is 7

Status: STATUS_LINE

Toolchain `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0`. The toolchain, lakefile and manifest
were copied from `research/ports/lean`, and the Mathlib cache came from `lake exe cache get`.
Build everything with `lake build` (Mathlib is never built here).

## The statement (`MC222/Statement.lean`, about 50 lines, imports Mathlib)

```lean
abbrev Pt := Fin 8 → ZMod 2                 -- points of F₂⁸
abbrev Fn := Pt → ZMod 2                    -- Boolean functions, pointwise algebra
def x (k : Fin 8) : Fn := fun p => p k      -- a11 a12 a21 a22 b11 b12 b21 b22
def a (i k : Fin 2) : Fn := x ⟨2 * i + k, _⟩
def b (k j : Fin 2) : Fn := x ⟨4 + 2 * k + j, _⟩
def c (i j : Fin 2) : Fn := a i 0 * b 0 j + a i 1 * b 1 j
def S (g : Fin k → Fn) (j : ℕ) : Submodule (ZMod 2) Fn :=
  span (insert 1 (Set.range x ∪ {f | ∃ i : Fin k, i.val < j ∧ g i = f}))
def IsCircuit (g : Fin k → Fn) : Prop := ∀ i, ∃ u ∈ S g i, ∃ v ∈ S g i, g i = u * v
def Computes (g : Fin k → Fn) : Prop := ∀ i j, c i j ∈ S g k
def HasCircuit (k : ℕ) : Prop := ∃ g : Fin k → Fn, IsCircuit g ∧ Computes g
noncomputable def MC : ℕ := sInf {k | HasCircuit k}
```

This is Definition 2.1 of the paper. Each gate is a product of two elements of
span{1, inputs, earlier gates}. Intermediate degrees are not restricted, and `x² = x` holds
because the values lie in ZMod 2.

Theorems (`MC222/Main.lean`):

* `hasCircuit_seven : HasCircuit 7`: Strassen's algorithm (`MC222/Upper.lean`).
* `not_hasCircuit_six : ¬ HasCircuit 6`.
* `not_hasCircuit_le_six : ∀ k ≤ 6, ¬ HasCircuit k`, by padding (`HasCircuit.mono`).
* `mc_eq_seven : MC = 7`.

## How the proof goes

| file | content |
|---|---|
| `Cube.lean` | The cube propositions, over `BitVec 256` truth tables. It imports only `Std`. |
| `Cubes/Rxx.lean` | 72 files, each with 5 theorems `cube_r_h : Cube a b 0 h`, each proved by `bv_decide`. |
| `AllCubes.lean` | Collects the 360 cube theorems into `all_cubes`. |
| `TT.lean` | `tt : Fn → BitVec 256`. It is injective, sends `+` to `^^^` and `*` to `&&&`, and sends `x k` and `c i j` to the literals. |
| `Comb.lean` | XOR-combinations with 16-bit coefficient vectors on both sides of `tt`; span membership gives a coefficient vector. |
| `Circuit.lean` | Basic lemmas about `S`. `update_circuit` is the replacement lemma: if a gate is replaced by a product `y` with `g m ∈ S g m + span{y}`, the result is again a circuit and every space can only grow. Also padding. |
| `Normal.lean` | Lemma 4.1: each gate can be replaced by `combF l G * combF r G` with no constants and with `(l, r)` a reduced echelon pair. The existence of the echelon basis is a `bv_decide` lemma. |
| `Orbit.lean`, `OrbitData.lean` | Lemma 4.3 and Prop. 4.4. Composition with a linear map `sig s` preserves circuits. `checkT_all` (native_decide) checks that each of the 432 maps sends T into span(T∘σ). `covers_all` (native_decide) checks that every echelon pair of 8-bit masks is mapped onto a basis of one of the 72 representative planes. The 432 maps are only a certificate: the group property is never used. |
| `Reduce.lean` | `orbit_step`: the first gate becomes `lin a * lin b` for a representative. `normalize_upto`: gates 1..5 are put in normal form. |
| `BVLemmas.lean` | `AT_indep`: 1, x, c are independent (`bv_decide`). `first_helper` (Lemma 4.5): `ℓ_a ℓ_b ∉ A + T` for independent masks (one symbolic `bv_decide`). |
| `Helpers.lean` | The helper set, replacing Lemmas 4.2 and 4.6. Put `U i = S i + T`. A gate is a helper if `g i ∉ U i`. Then 13 ≤ dim U₀ and dim U₆ ≤ 15, and each helper raises the dimension. Gate 0 is a helper, so all helpers lie in `{0, h}`, and every other gate lies in `W_i = A + T + span{g_j : j ∈ {0,h}, j < i}`. |
| `Final.lean` | `lower_of_cubes : (∀ r ∈ reps, ∀ h, 1 ≤ h → h ≤ 5 → Cube r.1 r.2 0 h) → ¬ HasCircuit 6`. |
| `Main.lean` | The main theorems. |

Differences from the paper's route:

* The helper lemma is proved without "shortest circuits", reducers or deleting gates. The
  dimension count is applied to *any* 6-gate circuit, and normalisation uses only the
  replacement lemma. This made the Lean proof much shorter.
* The paper's 15 helper sets are not all needed. Lemma 4.5 is one `bv_decide` lemma, so only
  `H = {0, h}` is used: 72 × 5 = 360 cubes. The 720 cubes with 0 ∉ H are not used.
* The first gate is set to `ℓ_a ℓ_b` with the raw representative masks `(a, b)` from
  `plane_orbits.txt`. These need not be in echelon form, and gate 0 needs no echelon condition.

### The cube proposition (`MC222/Cube.lean`)

`Cube α β h₁ h₂` says that no assignment of the following variables satisfies `CubeOK`:

* `G0..G5 : BitVec 256`, the gate truth tables;
* `l_i, r_i : BitVec 16` for i = 1..5, the coefficients of the factors over (x₀..x₇, g₀..g_{i−1});
* `o_t : BitVec 16`, the output coefficients over (1, x, g);
* `w_i : BitVec 16`, the helper witnesses over (1, x, c, g_{h₁}, g_{h₂}).

The conditions in `CubeOK` are:

* `G0 = comb α X &&& comb β X`;
* for i ≥ 1, `G_i = comb l_i (gens) &&& comb r_i (gens)`, with `Ech l_i r_i` and coefficients only
  at positions below 8 + i;
* `comb o_t (outGens) = C t`;
* for i ∉ {h₁, h₂}, `G_i = comb w_i (witGens …)`.

Here `comb c v = ⊕_j (v_j &&& signExtend 256 (c[j]))`. The proof of each cube is
`simp only [defs] at h; bv_decide`. Its correctness is not trusted: `lower_of_cubes` proves in
Lean that a 6-gate circuit would give a satisfying assignment.

## Axioms

```
MC222.hasCircuit_seven : [propext, Classical.choice, Quot.sound]
MC222.lower_of_cubes   : [propext, Classical.choice, Quot.sound,
   MC222.AT_indep._native.bv_decide.ax_1_24, MC222.checkT_all._native.native_decide.ax_1_1,
   MC222.covers_all._native.native_decide.ax_1_1, MC222.ech_exists._native.bv_decide.ax_1_5,
   MC222.first_helper._native.bv_decide.ax_1_25]
AXIOMS_MAIN
```

In Lean 4.36, `bv_decide` and `native_decide` no longer go through `Lean.ofReduceBool`.
Instead, each call adds its own auxiliary axiom, named `<decl>._native.<tactic>.ax_…`. That
axiom says that a particular compiled Boolean computation evaluated to `true`: for
`bv_decide`, the verified LRAT checker run on the certificate; for `native_decide`, the check
itself. So the trust base is the standard axioms plus the Lean compiler and runtime, used for
365 such evaluations: 360 cubes, 3 `bv_decide` lemmas and 2 `native_decide` checks. No Python
encoder, external SAT checker or hand-proved lemma is trusted. CaDiCaL is not trusted either:
only its LRAT certificate is used, and Lean's verified checker checks it.

**A fully kernel-checked proof is not realistic.** Each cube's LRAT proof would have to be
replayed by the kernel's evaluator instead of compiled code. bv_decide's certificates are
roughly 10–50 MB per hard cube, and kernel reduction is orders of magnitude slower than native
code; even the 2 native_decide checks would need restructuring. `checkT_all` could probably be
done with `decide`. `covers_all` takes 3 minutes of native search and would need a per-plane
certificate. The cubes are the obstacle.

## Measurements

* A single cube run alone: root 0, H={0,3}: 11 s in total (CaDiCaL 4.6 s, LRAT parse,
  trim and check < 2 s, kernel 0.8 s). Root 0, H={0,1}: 20 s (SAT 11.3 s). Root 9, H={0,1},
  the hardest cube in the external run: 22 s (SAT 12.2 s). Each Lean process uses about
  0.9–1.0 GB RSS, and each CaDiCaL about 160 MB.
* No options were needed except a larger `timeout`. The default is 10 s; 7200 s was set.
  Neither `+acNf` nor splitting was needed.
* A control instance (6 gates computing only c11, c12, c21, with first gate Strassen's m1)
  is satisfiable: bv_decide returns a counterexample, so the encoding is not vacuous. In any
  case, `lower_of_cubes` is a Lean proof.
* All 360 cubes: CUBE_TIMING
* `covers_all` (native_decide): about 3 min of elaboration on the loaded machine. Most of it is
  the compiled search over 10795 planes × up to 432 maps × 72 representatives. A certificate
  table would make it take seconds.
* Lean source: about 1400 lines, excluding generated data and cubes. Work time: one agent
  session.

## Alternative: a verified exact search run by native_decide

The Rust search, 3.5M states, could be written in Lean as a decision procedure over spaces of
truth tables. Its soundness would have to be proved: canonical keys, the memo of failed
states, the reducer successors (which use the bilinearity/Gray-code argument), and the
pruning rule rem > b. All of this would then run under `native_decide`. The trust base is the
same (Lean compiler plus the standard axioms), but there are 2 axioms instead of 365. The
proof effort is clearly larger: the correctness of the search is a real verified-algorithms
project, with Gaussian elimination, invariants of the DFS and the hash memo, perhaps 3–6×
the Lean code here. The runtime would also be larger: Lean native code over BitVec 256 is
likely several times slower than the Rust, so roughly 1 h. The bv_decide route needs no
reasoning about a search algorithm, only about the model, and it is done.

## Not done

* The small validation theorems (F₄ multiplication MC = 3, degree-1 polynomial product
  MC = 3) were not formalized. The development is specialised to 8 inputs and 4 targets, and
  generalising it would be mostly mechanical, perhaps half a day. They matter less here than
  in the paper, because the cube encoding is not trusted: its meaning is proved in Lean.
* Lint warnings (deprecated names, unused simp arguments) were not cleaned up.

## Files

* `scripts/gen_cubes.py` writes `MC222/Cubes/R*.lean` and `MC222/AllCubes.lean` from
  `scripts/plane_orbits.txt`, a copy of `tools/mc222/plane_orbits.txt`.
* `scripts/gen_orbit_data.py` writes `MC222/OrbitData.lean`: 432 maps and 72 representatives.
  This is untrusted certificate data, checked in `Orbit.lean`.
* `scratch/` holds experiments. It is not part of the library.
