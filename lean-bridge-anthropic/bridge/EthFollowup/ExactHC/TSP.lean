/-
# TSP (weighted exact #HC via Kronecker substitution) at Turing-machine level

The weighted analogue of `Assembly.lean` / `Package.lean`: from a `TSPPackage g c₀`
(`WeightedPackage.lean`) for every `g ≥ 1`, a Turing machine of Mathlib with finite alphabets that,
on the word `tspCode G W w` (`code G`, then `W` in unary, then the `n²` weights `w s(u,v)` in
row-major order as blocks of `W + 1` bits), writes the **Kronecker integer**
`kronNum G w = n · Σ_{H ∈ HC(G)} 2^{bK n · w(H)}` (`bK n = n² + n`) in binary, within
`⌊C · 2^{δn} · (W + 2)^C⌋` steps for every graph with `|E| ≤ D·n` and all weights `≤ W`.

* **The machine** `TSPAsm.tspM`: read the word (`readT`); for every branch `y < nBr` of Lemma 6.1
  (the graph part is branched exactly as in `Assembly.lean`, the weights are passed through:
  `brWordT_code : brWordT g (cOf G W w, y) = tspCode (brGraph G g y) W w`), if the branch graph is
  bad answer `0`, else run Lemma 1 on the weighted network of the branch; add up (`sum_branches_w`:
  the Hamiltonian cycles of the branches partition those of `G`, so the Kronecker integers add up),
  write the bits. No division by `n`: the output is `n · Σ_H 2^{b·w(H)}` itself, the integer whose
  base-`2^b` digits `Hamiltonian.kronecker_decode` reads.
* `bodyT_runs`, `tspM_runs`: the branch and the machine, with time `A (W+2)^A 2^{(δ/2) n}` and
  states of size `A (n + W + 2)^A`.
* **`theoremTSP_of_package`**, **`theoremTSP`** (unconditional, from `exists_tspPackage`).
* **Decoding**: `kronNum_digit` (digit `j` of `kronNum` in base `2^{bK n}` is `n · c_j`, the number of
  tours of weight `j` times `n`), `kronNum_digit_ne_zero_iff`, `kronNum_digit_div`,
  `kronNum_min_iff` (the minimum tour weight is the position of the lowest non-zero digit, and the
  number of optimal tours is that digit divided by `n`), and `theoremTSP_decode` combining them
  with the machine.

The time bound is pseudo-polynomial in the weights, as it must be: the output has about `b·n·W`
bits. Standard axioms only.
-/
import EthFollowup.ExactHC.WeightedPackage
import CountKSat.Host

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Groundwork Groundwork.Prog GraphProblems Asm Finset EthFollowup.Hamiltonian
  Eight.SecNetworks Printed

/-! ## The Kronecker integer -/

/-- **The Kronecker integer** `n · Σ_{H ∈ HC(G)} 2^{bK n · w(H)}`, the output of the TSP machine. -/
def kronNum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℕ) : ℕ :=
  n * ∑ H ∈ hamCycles G, 2 ^ (bK n * wt w H)

/-- The exponent bounding the Kronecker integers: `n · Σ_H 2^{b·w(H)} < 2^{n + n² + b·n·W}`. -/
def eK (n W : ℕ) : ℕ := n + n * n + bK n * (n * W)

theorem kron_le {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] {W : ℕ} {w : Sym2 (Fin n) → ℕ}
    (hw : ∀ e, w e ≤ W) :
    n * ∑ X ∈ hamCycles H, 2 ^ (bK n * wt w X) ≤ n * 2 ^ (n * n) * 2 ^ (bK n * (n * W)) := by
  have h1 : ∑ X ∈ hamCycles H, 2 ^ (bK n * wt w X) ≤ (hamCycles H).card • 2 ^ (bK n * (n * W)) :=
    sum_le_card_nsmul _ _ _ fun X hX =>
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (wt_le_of_mem_hamCycles H hw hX))
  rw [smul_eq_mul] at h1
  rw [mul_assoc]
  exact Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_right _ (card_hamCycles_le H)))

theorem kron_lt {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] {W : ℕ} {w : Sym2 (Fin n) → ℕ}
    (hw : ∀ e, w e ≤ W) : n * ∑ X ∈ hamCycles H, 2 ^ (bK n * wt w X) < 2 ^ eK n W := by
  refine (kron_le H hw).trans_lt ?_
  unfold eK
  rw [pow_add, pow_add]
  exact Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (by positivity))
    (by positivity)

/-! ## The branches of Lemma 6.1, weighted -/

/-- **Lemma 6.1, weighted**: the Hamiltonian cycles of the branches partition those of `G`, so any
sum over tours adds up over the branches. -/
theorem sum_branches_w {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (g : ℕ)
    (f : Finset (Sym2 (Fin n)) → ℕ) :
    ∑ y ∈ range (nBr g (aOf G)), ∑ H ∈ hamCycles (brGraph G g y), f H = ∑ H ∈ hamCycles G, f H := by
  rw [← sum_fiberwise_of_maps_to (s := hamCycles G) (t := range (nBr g (aOf G))) (g := yOf G g)
    (fun X _ => mem_range.2 (yOf_lt G g X)) f]
  exact sum_congr rfl fun y hy => by rw [hamCycles_brGraph G g (mem_range.1 hy)]

namespace TSPAsm

/-- The branch word: the code of the branch graph, then the weight part of the input unchanged. -/
def brWordT (g : ℕ) (p : TIn × ℕ) : List Bool :=
  brWord g (p.1.1, p.2) ++ ((p.1.2.1.map fun _ => true) ++ [false]) ++ p.1.2.2

/-- The branch graph is bad (`n ≤ 2` or a vertex of degree `< 2`). -/
def badT (g : ℕ) (p : TIn × ℕ) : Bool := badW g (p.1.1, p.2)

theorem brWordT_polyT (g : ℕ) : PolyT (brWordT g) := by
  have h1 : PolyT fun p : TIn × ℕ => brWord g (p.1.1, p.2) :=
    PolyT.comp (brWord_polyT g) (g := fun p : TIn × ℕ => (p.1.1, p.2)) (by fun_prop)
  unfold brWordT
  fun_prop

theorem badT_polyT (g : ℕ) : PolyT (badT g) :=
  PolyT.comp (badW_polyT g) (g := fun p : TIn × ℕ => (p.1.1, p.2)) (by fun_prop)

theorem nBrT_polyT (g : ℕ) : PolyT fun c : TIn => nBr g c.1 :=
  PolyT.comp (nBr_polyT g) (g := fun c : TIn => c.1) (by fun_prop)

/-- **The branch word of `(G, W, w)` and `y` is the input word of `(G_y, W, w)`.** -/
theorem brWordT_code {n : ℕ} (G : SimpleGraph (Fin n)) (W : ℕ) (w : Sym2 (Fin n) → ℕ) (g y : ℕ) :
    brWordT g (cOf G W w, y) = tspCode (brGraph G g y) W w := by
  unfold brWordT cOf
  simp only
  rw [← read1_code, brWord_code, tspCode, List.append_assoc]
  congr 2
  simp [GraphProblems.unary]

/-! ### The machine -/

variable {g c₀ : ℕ}

/-- One branch: `0` if the branch graph is bad; otherwise Lemma 1 (the machine `NM`) on the
weighted network of the branch. -/
def bodyT (g : ℕ) (NM : NetMachine) (pk : TSPPackage g c₀) : Stepped (TIn × ℕ) ℤ :=
  Stepped.ite (badT g) (Stepped.const 0)
    (Stepped.mapIn (fun p => pk.prep (brWordT g p))
      (networkOnSteps g NM (labelProcs pk.lay pk.par pk.Tp)))

/-- The sum over the branches: the Kronecker integer. -/
def mainT (g : ℕ) (NM : NetMachine) (pk : TSPPackage g c₀) : Stepped (List Bool) ℤ :=
  Stepped.mapIn readT (Stepped.sumRange (fun c : TIn => nBr g c.1) (bodyT g NM pk))

/-- The binary digits of the result. -/
def finT (p : List Bool × ℤ) : List Bool := Nat.bits p.2.toNat

/-- **The TSP machine.** -/
def tspM (g : ℕ) (NM : NetMachine) (pk : TSPPackage g c₀) : Stepped (List Bool) (List Bool) :=
  Stepped.bind (mainT g NM pk) (Stepped.ofFun finT)

theorem finT_polyT : PolyT finT := by
  unfold finT
  exact PolyT.bits (PolyT.toNat PolyT.id'.snd)

theorem tspM_poly (NM : NetMachine) (pk : TSPPackage g c₀) (hN : NM.PolyTimeSteps) :
    Nonempty (IsPolyT (tspM g NM pk)) := by
  obtain ⟨i1⟩ := networkOnSteps_poly g NM (labelProcs pk.lay pk.par pk.Tp) hN
    (labelProcs_keeps pk.lay_poly pk.par_poly pk.Tp_poly) (Lay.P_unary pk.lay_poly)
    (Lay.B_unary pk.lay_poly)
  have : IsPolyT (Stepped.mapIn (fun p => pk.prep (brWordT g p))
      (networkOnSteps g NM (labelProcs pk.lay pk.par pk.Tp))) :=
    IsPolyT.mapIn (PolyT.comp pk.prep_poly (brWordT_polyT g))
  have : IsPolyT (Stepped.const (0 : ℤ) : Stepped (TIn × ℕ) ℤ) := IsPolyT.const 0
  have : IsPolyT (bodyT g NM pk) := IsPolyT.ite (badT_polyT g)
  have : IsPolyT (Stepped.sumRange (fun c : TIn => nBr g c.1) (bodyT g NM pk)) :=
    IsPolyT.sumRange (nBrT_polyT g)
  have : IsPolyT (mainT g NM pk) := IsPolyT.mapIn readT_polyT
  have : IsPolyT (Stepped.ofFun finT) := IsPolyT.ofFun finT_polyT
  exact ⟨IsPolyT.bind⟩

/-! ### Polynomial bounds in `N = n + W` -/

/-- The bound on `P + B` of a branch (`N = n + W`). -/
def pbT (c₀ q D n N : ℕ) : ℕ := c₀ * ((2 * D + 1) * n + 2) + q + q * (N + 2) ^ q

/-- The state bound of a branch. -/
def smT (g c₀ q D C₁ n W : ℕ) : ℕ :=
  (Pkg.szC n W + ((n + 2) ^ (4 * D * g) + 1) + 3) +
    (q * (n + W + 2) ^ q + C₁ * pbT c₀ q D n (n + W) ^ C₁ + 5)

/-- The step bound of a branch, without the factor `2^{(δ/4) n}`. -/
def wT (g c₀ q D C₁ n W : ℕ) : ℕ :=
  3 * C₁ * 2 ^ (q + 3 * (2 * c₀ * g + g * q) + 2 * c₀) * pbT c₀ q D n (n + W) ^ C₁ *
    (q * (n + W + 2) ^ q) + 1

theorem n_pol (n W : ℕ) : Pol 1 (n + W) n := Pol.le Pol.id (Nat.le_add_right n W)

theorem W_pol (n W : ℕ) : Pol 1 (n + W) W := Pol.le Pol.id (Nat.le_add_left W n)

theorem pol_szC : ∃ A, ∀ n W, Pol A (n + W) (Pkg.szC n W) :=
  ⟨_, fun n W => (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 2) (n_pol n W)) (Pol.const 1))
    (Pol.add (Pol.mul (Pol.const 2) (Pol.mul (n_pol n W) (n_pol n W))) (Pol.const 1)))
    (Pol.add (Pol.mul (Pol.const 2) (W_pol n W)) (Pol.const 1)))
    (Pol.add (Pol.mul (Pol.const 2) (Pol.mul (Pol.mul (n_pol n W) (n_pol n W))
      (Pol.add (W_pol n W) (Pol.const 1)))) (Pol.const 1)) : Pol _ (n + W) _)⟩

theorem pol_pow_n_le (k n W : ℕ) : Pol (k + 1) (n + W) ((n + 2) ^ k) :=
  (Pol.pow_n k).le (Nat.pow_le_pow_left (by omega) _)

theorem pol_pbT (c₀ q D : ℕ) : ∃ A, ∀ n W, Pol A (n + W) (pbT c₀ q D n (n + W)) :=
  ⟨_, fun n W => (Pol.add (Pol.add (Pol.mul (Pol.const c₀)
    (Pol.add (Pol.mul (Pol.const (2 * D + 1)) (n_pol n W)) (Pol.const 2))) (Pol.const q))
    (Pol.mul (Pol.const q) (Pol.pow_n q)) : Pol _ (n + W) _)⟩

theorem pol_smT (g c₀ q D C₁ : ℕ) : ∃ A, ∀ n W, Pol A (n + W) (smT g c₀ q D C₁ n W) := by
  obtain ⟨A, hA⟩ := pol_pbT c₀ q D
  obtain ⟨As, hs⟩ := pol_szC
  exact ⟨_, fun n W => (Pol.add
    (Pol.add (Pol.add (hs n W) (Pol.add (pol_pow_n_le (4 * D * g) n W) (Pol.const 1))) (Pol.const 3))
    (Pol.add (Pol.add (Pol.mul (Pol.const q) (Pol.pow_n q))
      (Pol.mul (Pol.const C₁) (Pol.pow (hA n W) C₁))) (Pol.const 5)) : Pol _ (n + W) _)⟩

theorem pol_wT (g c₀ q D C₁ : ℕ) : ∃ A, ∀ n W, Pol A (n + W) (wT g c₀ q D C₁ n W) := by
  obtain ⟨A, hA⟩ := pol_pbT c₀ q D
  exact ⟨_, fun n W => (Pol.add (Pol.mul (Pol.mul (Pol.const _) (Pol.pow (hA n W) C₁))
    (Pol.mul (Pol.const q) (Pol.pow_n q))) (Pol.const 1) : Pol _ (n + W) _)⟩

/-- `(n + W + 2)^k ≤ (n + 2)^k · (W + 2)^k`. -/
theorem pow_add_le_mul (n W k : ℕ) : (n + W + 2) ^ k ≤ (n + 2) ^ k * (W + 2) ^ k := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by nlinarith) k

/-! ### One branch -/

section Runs

variable {NM : NetMachine} {C₁ K : ℕ} {e δ : ℝ}

theorem bodyT_runs (pk : TSPPackage g c₀) (hNM : ComputesNetworks NM C₁ g K e)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK1 : 1 ≤ K) (hKg : K ≤ g) {D : ℕ}
    (he : e * c₀ * (D + 1) ≤ δ / 8) (hKδ : 4 * (c₀ : ℝ) * (2 * D + 1) ≤ δ / 8 * K)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hm : G.edgeFinset.card ≤ D * n)
    {W : ℕ} {w : Sym2 (Fin n) → ℕ} (hw : ∀ e, w e ≤ W) {y : ℕ} (hy : y < nBr g (aOf G)) :
    ∃ t : ℕ, (bodyT g NM pk).Runs (cOf G W w, y) t (smT g c₀ pk.q D C₁ n W)
        ((n * ∑ H ∈ hamCycles (brGraph G g y), 2 ^ (bK n * wt w H) : ℕ) : ℤ) ∧
      (t : ℝ) ≤ wT g c₀ pk.q D C₁ n W * (2 : ℝ) ^ (δ / 4 * n) := by
  have hg1 : 1 ≤ g := hK1.trans hKg
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 4 * n) := by
    have : (0 : ℝ) ≤ δ / 4 * n := by
      have : 0 ≤ δ := by
        have h0 : (0 : ℝ) ≤ 4 * (c₀ : ℝ) * (2 * D + 1) := by positivity
        have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
        nlinarith
      positivity
    exact Real.one_le_rpow one_le_two this
  have hsy : size y ≤ (n + 2) ^ (4 * D * g) + 1 := by
    have := nBr_le G hg1 hm
    have := size_nat_le' y
    omega
  have hsa := Pkg.size_cOf G hw
  by_cases hb : badW g (aOf G, y) = true
  · -- the branch has no Hamiltonian cycle
    have h0 := hamCycles_eq_empty ((badW_iff G g y).1 hb)
    refine ⟨1, ?_, ?_⟩
    · rw [h0, sum_empty, mul_zero, Nat.cast_zero]
      have hb' : badT g (cOf G W w, y) = true := hb
      refine (Stepped.ite_runs_true hb' (Stepped.const_runs (0 : ℤ) (cOf G W w, y))).mono le_rfl ?_
      have : size (0 : ℤ) = 1 := rfl
      simp only [size_prod] at *
      unfold smT
      omega
    · have : (1 : ℝ) ≤ wT g c₀ pk.q D C₁ n W := by
        have : 1 ≤ wT g c₀ pk.q D C₁ n W := by unfold wT; omega
        exact_mod_cast this
      nlinarith
  · -- the weighted network of the branch
    have hb' : badT g (cOf G W w, y) = false := by
      show badW g (aOf G, y) = false
      simpa using hb
    set H := brGraph G g y with hH
    have hgood : ¬ (n ≤ 2 ∨ ∃ v, H.degree v < 2) := fun h => hb ((badW_iff G g y).2 h)
    have h3 : 3 ≤ n := by omega
    have hdeg : ∀ v, 2 ≤ H.degree v := fun v => by
      by_contra h; exact hgood (Or.inr ⟨v, by omega⟩)
    have hG : Good H W w := ⟨h3, hdeg, hw⟩
    have hcode : brWordT g (cOf G W w, y) = tspCode H W w := brWordT_code G W w g y
    have hgiven : Given.IsGivenNetwork (Given.ofProcs (labelProcs pk.lay pk.par pk.Tp)) Given.noTable
        (pk.prep (tspCode H W w)) ((pk.X H W w).net (pk.C H)) (pk.P H) (pk.B H W w) (pk.τ H)
        (pk.S H W w + size (pk.prep (tspCode H W w)) + 2 * g + 4 * pk.P H + 8) :=
      labelProcs_given (pk.X H W w) (pk.C H) pk.lay_poly pk.par_poly pk.Tp_poly
        ((pk.X H W w).net_is (pk.C H) (pk.P_pos H W w hG) (pk.B_pos H W w hG) (pk.hP H W w hG)
          (pk.hT H W w hG))
        (pk.describes H W w hG) (pk.parSpec H W w hG) (pk.tSpec H W w hG) (pk.τ_pos H W w hG)
    obtain ⟨T, hrun, hT⟩ := (Given.onSteps hNM hgiven).2
    rw [LabelSystem.value_net, pk.value H W w hG] at hrun
    have hmH : H.edgeFinset.card ≤ D * n := (card_edge_brGraph_le G g y).trans hm
    have hmu := pk.mu_le H W w hG (n / g + 2) (degree_brGraph_le G g y)
    have hU : ((pk.X H W w).net (pk.C H)).U ≤ c₀ * (H.edgeFinset.card + n) + pk.q := by
      rw [LabelSystem.U_eq]; exact pk.U_le H W w hG
    have hP := pk.P_le H W w hG
    have hB := pk.B_le H W w hG
    have hτ := pk.τ_le H W w hG
    have hS := pk.S_le H W w hG
    -- μ ≤ (2D+1) n + 2, P + B ≤ pbT
    have hmu' : pk.mu H ≤ (2 * D + 1) * n + 2 := by
      have : g * (n / g) ≤ n := Nat.mul_div_le n g
      have h2 : g * pk.mu H ≤ g * ((2 * D + 1) * n + 2) := by nlinarith
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    have hPB : pk.P H + pk.B H W w ≤ pbT c₀ pk.q D n (n + W) := by
      unfold pbT
      have : c₀ * pk.mu H ≤ c₀ * ((2 * D + 1) * n + 2) := Nat.mul_le_mul_left _ hmu'
      omega
    refine ⟨T, ?_, ?_⟩
    · have hr := Stepped.ite_runs_false (M := Stepped.const (0 : ℤ)) hb'
        (Stepped.mapIn_runs (f := fun p => pk.prep (brWordT g p)) (a := (cOf G W w, y))
          (by rw [hcode]; exact hrun))
      refine hr.mono le_rfl ?_
      have : C₁ * (pk.P H + pk.B H W w) ^ C₁ ≤ C₁ * pbT c₀ pk.q D n (n + W) ^ C₁ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hPB _)
      unfold smT
      omega
    · -- the exponent
      have hX := exponent_le (q := pk.q) (U := ((pk.X H W w).net (pk.C H)).U) (P := pk.P H)
        (mu := pk.mu H) he0 he1 hK1 hKg hmH hmu hU hP he hKδ
      set E₀ : ℕ := pk.q + 3 * (2 * c₀ * g + g * pk.q) + 2 * c₀ with hE₀
      set X : ℝ := e * (((pk.X H W w).net (pk.C H)).U + (g : ℝ) * (pk.P H) / K) +
        2 * ((g : ℝ) * (pk.P H)) / K with hXd
      have hτR : (pk.τ H : ℝ) ≤ (2 : ℝ) ^ ((c₀ * pk.mu H : ℕ) : ℝ) *
          ((pk.q * (n + W + 2) ^ pk.q : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; exact_mod_cast hτ
      have hPBR : ((pk.P H : ℝ) + pk.B H W w) ^ C₁ ≤ (pbT c₀ pk.q D n (n + W) : ℝ) ^ C₁ := by
        gcongr; exact_mod_cast hPB
      have h2 : (2 : ℝ) ^ X * (2 : ℝ) ^ ((c₀ * pk.mu H : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (E₀ : ℝ) * (2 : ℝ) ^ (δ / 4 * n) := by
        rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
        exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      rw [show (2 : ℝ) ^ (E₀ : ℝ) = (2 : ℝ) ^ E₀ from Real.rpow_natCast 2 E₀] at h2
      calc (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ X * ((pk.P H : ℝ) + pk.B H W w) ^ C₁) * (pk.τ H) := hT
        _ ≤ 3 * (C₁ * (2 : ℝ) ^ X * (pbT c₀ pk.q D n (n + W) : ℝ) ^ C₁) *
              ((2 : ℝ) ^ ((c₀ * pk.mu H : ℕ) : ℝ) * ((pk.q * (n + W + 2) ^ pk.q : ℕ) : ℝ)) := by
            gcongr
        _ = 3 * C₁ * (pbT c₀ pk.q D n (n + W) : ℝ) ^ C₁ * ((pk.q * (n + W + 2) ^ pk.q : ℕ) : ℝ) *
              ((2 : ℝ) ^ X * (2 : ℝ) ^ ((c₀ * pk.mu H : ℕ) : ℝ)) := by ring
        _ ≤ 3 * C₁ * (pbT c₀ pk.q D n (n + W) : ℝ) ^ C₁ * ((pk.q * (n + W + 2) ^ pk.q : ℕ) : ℝ) *
              ((2 : ℝ) ^ E₀ * (2 : ℝ) ^ (δ / 4 * n)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ (wT g c₀ pk.q D C₁ n W : ℝ) * (2 : ℝ) ^ (δ / 4 * n) := by
            unfold wT
            rw [← hE₀]
            push_cast
            have : (0 : ℝ) ≤ (2 : ℝ) ^ (δ / 4 * n) := by positivity
            nlinarith

/-! ### The machine on every instance -/

/-- **The machine, on every graph with at most `Dn` edges and weights `≤ W`**: the Kronecker integer
in binary, within `A · (W+2)^A · 2^{(δ/2) n}` steps on states of size at most `A (n + W + 2)^A`. -/
theorem tspM_runs (pk : TSPPackage g c₀) (hNM : ComputesNetworks NM C₁ g K e)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK1 : 1 ≤ K) (hKg : K ≤ g) (hδ : 0 < δ) {D : ℕ}
    (he : e * c₀ * (D + 1) ≤ δ / 8) (hKδ : 4 * (c₀ : ℝ) * (2 * D + 1) ≤ δ / 8 * K) :
    ∃ A : ℕ, ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (w : Sym2 (Fin n) → ℕ),
      G.edgeFinset.card ≤ D * n → (∀ e, w e ≤ W) →
      ∃ T : ℕ, (tspM g NM pk).Runs (tspCode G W w) T (A * (n + W + 2) ^ A) (Nat.bits (kronNum G w)) ∧
        (T : ℝ) ≤ A * ((W : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * n) := by
  have hg1 : 1 ≤ g := hK1.trans hKg
  set q := pk.q
  obtain ⟨As, hAs⟩ := pol_smT g c₀ q D C₁
  obtain ⟨Aw, hAw⟩ := pol_wT g c₀ q D C₁
  obtain ⟨Ac, hAc⟩ := pol_szC
  -- the step bound, without the exponential factor
  have hZ : ∃ A, ∀ n W, Pol A (n + W) ((n + 2) ^ (4 * D * g) * (wT g c₀ q D C₁ n W + 1) + 2) :=
    ⟨_, fun n W => Pol.add (Pol.mul (pol_pow_n_le (4 * D * g) n W) (Pol.add (hAw n W) (Pol.const 1)))
      (Pol.const 2)⟩
  obtain ⟨Az, hAz⟩ := hZ
  obtain ⟨Cp, hCp⟩ := exists_pow_le Az (show (0 : ℝ) < δ / 4 by positivity)
  -- the state bound
  have hSt : ∃ A, ∀ n W, Pol A (n + W) ((2 * (n + 1 + n * n + (W + 1 + n * n * (W + 1))) + 1) +
      Pkg.szC n W + ((n + 2) ^ (4 * D * g) + 1) + ((n + 2) * (4 * D * g) + eK n W + 1) +
      smT g c₀ q D C₁ n W + (eK n W + 1) + (2 * eK n W + 1) + 4) := by
    have hbK : ∀ n W, Pol 4 (n + W) (bK n) := fun n W =>
      (Pol.add (Pol.mul (n_pol n W) (n_pol n W)) (n_pol n W) : Pol _ (n + W) (n * n + n))
    have heK : ∀ n W, Pol _ (n + W) (eK n W) := fun n W =>
      (Pol.add (Pol.add (n_pol n W) (Pol.mul (n_pol n W) (n_pol n W)))
        (Pol.mul (hbK n W) (Pol.mul (n_pol n W) (W_pol n W))) : Pol _ (n + W) (n + n * n + bK n * (n * W)))
    exact ⟨_, fun n W => Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.add (Pol.add (n_pol n W) (Pol.const 1))
        (Pol.mul (n_pol n W) (n_pol n W))) (Pol.add (Pol.add (W_pol n W) (Pol.const 1))
        (Pol.mul (Pol.mul (n_pol n W) (n_pol n W)) (Pol.add (W_pol n W) (Pol.const 1))))))
        (Pol.const 1))
      (hAc n W))
      (Pol.add (pol_pow_n_le (4 * D * g) n W) (Pol.const 1)))
      (Pol.add (Pol.add (Pol.mul (Pol.add (n_pol n W) (Pol.const 2)) (Pol.const (4 * D * g)))
        (heK n W)) (Pol.const 1)))
      (hAs n W))
      (Pol.add (heK n W) (Pol.const 1)))
      (Pol.add (Pol.mul (Pol.const 2) (heK n W)) (Pol.const 1)))
      (Pol.const 4)⟩
  obtain ⟨Ast, hAst⟩ := hSt
  refine ⟨Ast + Az * Cp + Az, fun {n} G _ W w hm hw => ?_⟩
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 4 * n) := Real.one_le_rpow one_le_two (by positivity)
  -- the branches
  choose! t ht using fun y (hy : y < nBr g (aOf G)) =>
    bodyT_runs pk hNM he0 he1 hK1 hKg he hKδ G hm hw hy
  set N := nBr g (aOf G) with hN
  have hNle := nBr_le G hg1 hm
  set v : ℕ → ℤ := fun y => ((n * ∑ H ∈ hamCycles (brGraph G g y), 2 ^ (bK n * wt w H) : ℕ) : ℤ)
    with hv
  set V : ℕ := n * 2 ^ (n * n) * 2 ^ (bK n * (n * W)) with hV
  have hVb : ∀ y < N, (v y).natAbs ≤ V := fun y _ => by
    simp only [hv, Int.natAbs_natCast]
    exact kron_le (brGraph G g y) hw
  have hsum := Stepped.sumRange_runs (M := bodyT g NM pk) (N := fun c : TIn => nBr g c.1)
    (a := cOf G W w) t v V (smT g c₀ q D C₁ n W) (fun y hy => (ht y hy).1) hVb
  have hval : ∑ y ∈ range N, v y = ((kronNum G w : ℕ) : ℤ) := by
    simp only [hv]
    rw [← Nat.cast_sum, ← mul_sum, sum_branches_w G g]
    rfl
  have hNc : nBr g (cOf G W w).1 = N := rfl
  simp only [hNc] at hsum
  rw [hval] at hsum
  have hmain : (mainT g NM pk).Runs (tspCode G W w) _ _ ((kronNum G w : ℕ) : ℤ) :=
    Stepped.mapIn_runs (f := readT) (by rw [readT_code]; exact hsum)
  have hfin := Stepped.ofFun_runs finT (tspCode G W w, ((kronNum G w : ℕ) : ℤ))
  have hout : finT (tspCode G W w, ((kronNum G w : ℕ) : ℤ)) = Nat.bits (kronNum G w) := by
    unfold finT
    simp only [Int.toNat_natCast]
  rw [hout] at hfin
  have hrun := Stepped.bind_runs hmain hfin
  have hkron : kronNum G w < 2 ^ eK n W := kron_lt G hw
  have hVlt : V < 2 ^ eK n W := by
    rw [hV, eK, pow_add, pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (by positivity))
      (by positivity)
  refine ⟨_, hrun.mono le_rfl ?_, ?_⟩
  · -- the state bound
    refine le_trans ?_ ((hAst n W).mono (by omega))
    have h1 : size (tspCode G W w) = 2 * (n + 1 + n * n + (W + 1 + n * n * (W + 1))) + 1 := by
      rw [LabelSystem.size_word, length_tspCode G hw]
    have h2 := Pkg.size_cOf G hw
    have h3 : size N ≤ (n + 2) ^ (4 * D * g) + 1 :=
      (size_nat_le' _).trans (by omega)
    have h4 : size (N * V) ≤ (n + 2) * (4 * D * g) + eK n W + 1 := by
      apply size_nat_of_lt
      have e1 : (n + 2) ^ (4 * D * g) ≤ 2 ^ ((n + 2) * (4 * D * g)) :=
        calc (n + 2) ^ (4 * D * g) ≤ (2 ^ (n + 2)) ^ (4 * D * g) :=
              Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
          _ = 2 ^ ((n + 2) * (4 * D * g)) := (pow_mul _ _ _).symm
      calc N * V ≤ 2 ^ ((n + 2) * (4 * D * g)) * V :=
            Nat.mul_le_mul_right _ (hNle.trans e1)
        _ < 2 ^ ((n + 2) * (4 * D * g)) * 2 ^ eK n W :=
            Nat.mul_lt_mul_of_pos_left hVlt (by positivity)
        _ = _ := by rw [← pow_add]
    have h5 : size ((kronNum G w : ℕ) : ℤ) ≤ eK n W + 1 := by
      apply size_int_of_lt
      rw [Int.natAbs_natCast]
      exact hkron
    have h6 : size (Nat.bits (kronNum G w)) ≤ 2 * eK n W + 1 := by
      rw [LabelSystem.size_word, Nat.size_eq_bits_len]
      have := Nat.size_le.2 hkron
      omega
    rw [show size (tspCode G W w, ((kronNum G w : ℕ) : ℤ)) =
      size (tspCode G W w) + size ((kronNum G w : ℕ) : ℤ) from rfl]
    simp only [max_def]
    split_ifs <;> omega
  · -- the step bound
    have hT1 : ∀ y ∈ range N, ((t y + 1 : ℕ) : ℝ) ≤
        (wT g c₀ q D C₁ n W + 1 : ℕ) * (2 : ℝ) ^ (δ / 4 * n) := fun y hy => by
      have := (ht y (mem_range.1 hy)).2
      push_cast
      nlinarith
    have hsumT : ((∑ y ∈ range N, (t y + 1) : ℕ) : ℝ) ≤
        N * ((wT g c₀ q D C₁ n W + 1 : ℕ) * (2 : ℝ) ^ (δ / 4 * n)) := by
      push_cast
      have := Finset.sum_le_sum hT1
      simp only [sum_const, card_range, nsmul_eq_mul] at this
      push_cast at this
      linarith
    have hNR : (N : ℝ) ≤ ((n + 2) ^ (4 * D * g) : ℕ) := by exact_mod_cast hNle
    have hZn : ((((n + 2) ^ (4 * D * g) * (wT g c₀ q D C₁ n W + 1) + 2 : ℕ)) : ℝ) ≤
        Az * (((n : ℝ) + 2) ^ Az * ((W : ℝ) + 2) ^ Az) := by
      have h0 := hAz n W
      unfold Pol at h0
      have h1 := h0.trans (Nat.mul_le_mul_left Az (pow_add_le_mul n W Az))
      exact_mod_cast h1
    have hCpn := hCp n
    have e2 : (2 : ℝ) ^ (δ / 2 * n) = (2 : ℝ) ^ (δ / 4 * n) * (2 : ℝ) ^ (δ / 4 * n) := by
      rw [← Real.rpow_add two_pos]; congr 1; ring
    have hW0 : (0 : ℝ) ≤ ((W : ℝ) + 2) ^ Az := by positivity
    have hW1 : ((W : ℝ) + 2) ^ Az ≤ ((W : ℝ) + 2) ^ (Ast + Az * Cp + Az) :=
      pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg W : (0 : ℝ) ≤ W)]) (by omega)
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := by positivity
    calc (((∑ y ∈ range N, (t y + 1)) + 1 + 1 : ℕ) : ℝ)
        ≤ N * ((wT g c₀ q D C₁ n W + 1 : ℕ) * (2 : ℝ) ^ (δ / 4 * n)) + 2 := by
          push_cast at hsumT ⊢; linarith
      _ ≤ ((n + 2) ^ (4 * D * g) : ℕ) * ((wT g c₀ q D C₁ n W + 1 : ℕ) * (2 : ℝ) ^ (δ / 4 * n)) +
            2 * (2 : ℝ) ^ (δ / 4 * n) := by gcongr; linarith
      _ = ((((n + 2) ^ (4 * D * g) * (wT g c₀ q D C₁ n W + 1) + 2 : ℕ)) : ℝ) *
            (2 : ℝ) ^ (δ / 4 * n) := by push_cast; ring
      _ ≤ (Az * (((n : ℝ) + 2) ^ Az * ((W : ℝ) + 2) ^ Az)) * (2 : ℝ) ^ (δ / 4 * n) := by gcongr
      _ ≤ (Az * ((Cp * (2 : ℝ) ^ (δ / 4 * n)) * ((W : ℝ) + 2) ^ Az)) * (2 : ℝ) ^ (δ / 4 * n) := by
          gcongr
      _ = ((Az * Cp : ℕ) : ℝ) * ((W : ℝ) + 2) ^ Az * (2 : ℝ) ^ (δ / 2 * n) := by
          rw [e2]; push_cast; ring
      _ ≤ ((Ast + Az * Cp + Az : ℕ) : ℝ) * ((W : ℝ) + 2) ^ (Ast + Az * Cp + Az) *
            (2 : ℝ) ^ (δ / 2 * n) := by
          gcongr
          · exact_mod_cast (by omega : Az * Cp ≤ Ast + Az * Cp + Az)

end Runs

end TSPAsm

/-! ## The theorem -/

open TSPAsm in
/-- **TSP (the Kronecker integer of a weighted graph) at Turing-machine level, from TSP packages.**
For every `δ > 0` and `D` there are a Turing machine of Mathlib with finite alphabets and a constant
`C` such that, on the word `tspCode G W w` of any graph `G` on `n` vertices with at most `D·n` edges
and edge weights `w ≤ W`, the machine halts within `⌊C · 2^{δn} · (W+2)^C⌋` steps with the Kronecker
integer `kronNum G w = n · Σ_{H ∈ HC(G)} 2^{bK n · w(H)}` in binary (lowest bit first). -/
theorem theoremTSP_of_package (hpkg : ∃ c₀ : ℕ, ∀ g : ℕ, 1 ≤ g → Nonempty (TSPPackage g c₀))
    (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (w : Sym2 (Fin n) → ℕ),
        G.edgeFinset.card ≤ D * n → (∀ e, w e ≤ W) →
        GraphProblems.Outputs M (tspCode G W w) (Nat.bits (kronNum G w))
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n) * ((W : ℝ) + 2) ^ C⌋₊ := by
  obtain ⟨c₀, hpk⟩ := hpkg
  set η : ℝ := min 1 (δ / (8 * (c₀ + 1) * (D + 1))) with hηd
  have hη : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨K, hK0, hach⟩ := Given.stEveryEta η hη (⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ + 2)
  obtain ⟨NM, C₁, hpoly, hNM⟩ := Printed.groupingLemma K η hach
  have hK1 : 1 ≤ K := by omega
  have hKg : K ≤ 3 * K ^ 8 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 8 := Nat.pow_le_pow_right hK1 (by norm_num)
      _ ≤ 3 * K ^ 8 := Nat.le_mul_of_pos_left _ (by norm_num)
  obtain ⟨pk⟩ := hpk (3 * K ^ 8) (hK1.trans hKg)
  have he : η * c₀ * (D + 1) ≤ δ / 8 := by
    have h1 : η ≤ δ / (8 * (c₀ + 1) * (D + 1)) := min_le_right _ _
    have h2 : η * c₀ * (D + 1) ≤ η * (c₀ + 1) * (D + 1) := by gcongr; linarith
    have h3 : η * (c₀ + 1) * (D + 1) ≤ δ / (8 * (c₀ + 1) * (D + 1)) * (c₀ + 1) * (D + 1) := by
      gcongr
    have h4 : δ / (8 * (c₀ + 1) * (D + 1)) * (c₀ + 1) * (D + 1) = δ / 8 := by
      field_simp
    linarith
  have hKδ : 4 * (c₀ : ℝ) * (2 * D + 1) ≤ δ / 8 * K := by
    have h1 : 32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ ≤ K := by
      have := Nat.le_ceil (32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ)
      have h2 : ((⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ : ℕ) : ℝ) ≤ K := by
        exact_mod_cast (by omega : ⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ ≤ K)
      linarith
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  obtain ⟨A, hA⟩ := tspM_runs pk hNM hη.le (min_le_left _ _) hK1 hKg hδ he hKδ
  obtain ⟨inst⟩ := tspM_poly NM pk hpoly
  obtain ⟨M, q, hfin, hM⟩ := CountKSat.stHostW (tspM (3 * K ^ 8) NM pk)
  have hδ2 : (0 : ℝ) < δ / 2 := by positivity
  obtain ⟨Cp, hCp⟩ := exists_pow_le ((A + 3) * q) hδ2
  refine ⟨M, q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q, hfin, fun n G inst W w hm hw => ?_⟩
  obtain ⟨T, hr, hT⟩ := hA G W w hm hw
  obtain ⟨ev⟩ := hM (tspCode G W w) T _ _ hr
  set S := A * (n + W + 2) ^ A with hS
  set L := (tspCode G W w).length with hL
  have hLv : L = n + 1 + n * n + (W + 1 + n * n * (W + 1)) := length_tspCode G hw
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := Real.one_le_rpow one_le_two (by positivity)
  -- L + S + 1 ≤ (4 + A) (n + W + 2)^(A + 3)
  have hLS : L + S + 1 ≤ (4 + A) * (n + W + 2) ^ (A + 3) := by
    have hL1 : L + 1 ≤ 4 * (n + W + 2) ^ 3 := by
      rw [hLv]
      set N := n + W with hN
      have h1 : n ≤ N := by omega
      have h2 : W ≤ N := by omega
      have e3 : (N + 2) ^ 3 = N * N * N + 6 * (N * N) + 12 * N + 8 := by ring
      have a1 : n * n ≤ N * N := Nat.mul_le_mul h1 h1
      have a2 : n * n * (W + 1) ≤ N * N * (N + 1) := Nat.mul_le_mul a1 (by omega)
      have a3 : N * N * (N + 1) = N * N * N + N * N := by ring
      rw [e3]
      omega
    have hp3 : (n + W + 2) ^ 3 ≤ (n + W + 2) ^ (A + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    have hpA : (n + W + 2) ^ A ≤ (n + W + 2) ^ (A + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 := Nat.mul_le_mul_left 4 hp3
    have h5 := Nat.mul_le_mul_left A hpA
    rw [add_mul]
    omega
  have hle : q * (T + 1) * (L + S + 1) ^ q ≤
      ⌊((q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n) *
        ((W : ℝ) + 2) ^ (q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q)⌋₊ := by
    refine Nat.le_floor ?_
    have hW0 : (0 : ℝ) ≤ (W : ℝ) + 2 := by positivity
    have hW1 : (1 : ℝ) ≤ (W : ℝ) + 2 := by linarith [(Nat.cast_nonneg W : (0 : ℝ) ≤ W)]
    -- T + 1 ≤ (A + 1) (W+2)^A 2^{(δ/2) n}
    have h1 : ((T : ℝ) + 1) ≤ ((A : ℝ) + 1) * ((W : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * n) := by
      have : (1 : ℝ) ≤ ((W : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * n) :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1) hE1
      nlinarith
    -- (L + S + 1)^q ≤ (4 + A)^q (n+2)^{(A+3) q} (W+2)^{(A+3) q}
    have h2 : (((L + S + 1 : ℕ) : ℝ)) ^ q ≤
        ((4 : ℝ) + A) ^ q * ((((n : ℝ) + 2) ^ ((A + 3) * q)) * ((W : ℝ) + 2) ^ ((A + 3) * q)) := by
      have h6 : (((L + S + 1 : ℕ) : ℝ)) ≤ ((4 : ℝ) + A) * (((n : ℝ) + 2) ^ (A + 3) * ((W : ℝ) + 2) ^ (A + 3)) := by
        have := hLS.trans (Nat.mul_le_mul_left (4 + A) (pow_add_le_mul n W (A + 3)))
        exact_mod_cast this
      calc (((L + S + 1 : ℕ) : ℝ)) ^ q ≤
            (((4 : ℝ) + A) * (((n : ℝ) + 2) ^ (A + 3) * ((W : ℝ) + 2) ^ (A + 3))) ^ q := by
              gcongr
        _ = ((4 : ℝ) + A) ^ q * ((((n : ℝ) + 2) ^ ((A + 3) * q)) * ((W : ℝ) + 2) ^ ((A + 3) * q)) := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    have h3 : ((n : ℝ) + 2) ^ ((A + 3) * q) ≤ Cp * (2 : ℝ) ^ (δ / 2 * n) := hCp n
    have h7 : (2 : ℝ) ^ (δ * n) = (2 : ℝ) ^ (δ / 2 * n) * (2 : ℝ) ^ (δ / 2 * n) := by
      rw [← Real.rpow_add two_pos]; congr 1; ring
    have hWexp : ((W : ℝ) + 2) ^ A * ((W : ℝ) + 2) ^ ((A + 3) * q) ≤
        ((W : ℝ) + 2) ^ (q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hW1 (by omega)
    have hpos1 : (0 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := by positivity
    have hpos2 : (0 : ℝ) ≤ ((4 : ℝ) + A) ^ q := by positivity
    have hpos3 : (0 : ℝ) ≤ ((W : ℝ) + 2) ^ ((A + 3) * q) := by positivity
    have hpos4 : (0 : ℝ) ≤ ((W : ℝ) + 2) ^ A := by positivity
    have h2' : (((L + S + 1 : ℕ) : ℝ)) ^ q ≤
        ((4 : ℝ) + A) ^ q * ((Cp * (2 : ℝ) ^ (δ / 2 * n)) * ((W : ℝ) + 2) ^ ((A + 3) * q)) :=
      h2.trans (by gcongr)
    rw [h7]
    calc ((q * (T + 1) * (L + S + 1) ^ q : ℕ) : ℝ)
        = (q : ℝ) * ((T : ℝ) + 1) * (((L + S + 1 : ℕ) : ℝ)) ^ q := by push_cast; ring
      _ ≤ (q : ℝ) * (((A : ℝ) + 1) * ((W : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * n)) *
            (((4 : ℝ) + A) ^ q * ((Cp * (2 : ℝ) ^ (δ / 2 * n)) * ((W : ℝ) + 2) ^ ((A + 3) * q))) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2' (by positivity)
            (by positivity)
      _ = ((q : ℝ) * ((A : ℝ) + 1) * ((4 : ℝ) + A) ^ q * Cp) *
            ((2 : ℝ) ^ (δ / 2 * n) * (2 : ℝ) ^ (δ / 2 * n)) *
            (((W : ℝ) + 2) ^ A * ((W : ℝ) + 2) ^ ((A + 3) * q)) := by ring
      _ ≤ ((q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q : ℕ) : ℝ) *
            ((2 : ℝ) ^ (δ / 2 * n) * (2 : ℝ) ^ (δ / 2 * n)) *
            ((W : ℝ) + 2) ^ (q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q) := by
          gcongr
          · push_cast
            have : (0 : ℝ) ≤ ((A : ℝ) + 3) * q := by positivity
            have : (0 : ℝ) ≤ (A : ℝ) := by positivity
            linarith
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩

/-- **TSP at Turing-machine level, unconditional.** For every `δ > 0` and every `D` there are a
Turing machine of Mathlib with finite alphabets and a constant `C` such that, on the word
`tspCode G W w` (`n` in unary, the adjacency matrix, `W` in unary, the `n²` edge weights
`w s(u,v) ≤ W` as blocks of `W+1` bits in row-major order) of any graph `G` on `n` vertices with at
most `D·n` edges, the machine halts within `⌊C · 2^{δn} · (W+2)^C⌋` steps with the Kronecker integer
`kronNum G w = n · Σ_{H ∈ HC(G)} 2^{bK n · w(H)}` (`bK n = n² + n`) in binary. -/
theorem theoremTSP (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (w : Sym2 (Fin n) → ℕ),
        G.edgeFinset.card ≤ D * n → (∀ e, w e ≤ W) →
        GraphProblems.Outputs M (tspCode G W w) (Nat.bits (kronNum G w))
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n) * ((W : ℝ) + 2) ^ C⌋₊ :=
  theoremTSP_of_package exists_tspPackage δ hδ D

/-! ## Decoding the output -/

section Decode

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {W : ℕ} {w : Sym2 (Fin n) → ℕ}

/-- The digit `j` of the Kronecker integer in base `2^{bK n}`. -/
def kronDigit (w : Sym2 (Fin n) → ℕ) (j : ℕ) : ℕ := kronNum G w / 2 ^ (bK n * j) % 2 ^ bK n

/-- **Digit `j` of the output is `n · c_j`**, `c_j` the number of tours of weight `j`, for every
`j ≤ n·W` (every tour has weight `≤ n·W`). -/
theorem kronNum_digit (hw : ∀ e, w e ≤ W) {j : ℕ} (hj : j ≤ n * W) :
    kronDigit G w j = n * tourCount G w j :=
  kronecker_decode G w (bK n) (n_mul_tourCount_lt G w (bK_spec G))
    (fun H hH => wt_le_of_mem_hamCycles G hw hH) hj

/-- Digit `j` is non-zero iff some tour has weight `j`. -/
theorem kronNum_digit_ne_zero_iff (hn : 0 < n) (hw : ∀ e, w e ≤ W) {j : ℕ} (hj : j ≤ n * W) :
    kronDigit G w j ≠ 0 ↔ ∃ H ∈ hamCycles G, wt w H = j := by
  rw [kronNum_digit G hw hj, tourCount, Nat.mul_ne_zero_iff, Finset.card_ne_zero,
    filter_nonempty_iff]
  exact ⟨fun h => h.2, fun h => ⟨hn.ne', h⟩⟩

/-- **The number of tours of weight `j`** is digit `j` divided by `n`. -/
theorem kronNum_digit_div (hn : 0 < n) (hw : ∀ e, w e ≤ W) {j : ℕ} (hj : j ≤ n * W) :
    kronDigit G w j / n = tourCount G w j := by
  rw [kronNum_digit G hw hj, Nat.mul_div_cancel_left _ hn]

/-- `k` is the minimum tour weight (some tour has weight `k`, none has a smaller one). -/
def IsMinTourWt (w : Sym2 (Fin n) → ℕ) (k : ℕ) : Prop :=
  (∃ H ∈ hamCycles G, wt w H = k) ∧ ∀ H ∈ hamCycles G, k ≤ wt w H

/-- **The minimum tour weight is the position of the lowest non-zero digit** of the output (in base
`2^{bK n}`), and **the number of optimal tours is that digit divided by `n`**
(`kronNum_digit_div`). -/
theorem kronNum_min_iff (hn : 0 < n) (hw : ∀ e, w e ≤ W) {k : ℕ} (hk : k ≤ n * W) :
    IsMinTourWt G w k ↔ kronDigit G w k ≠ 0 ∧ ∀ j < k, kronDigit G w j = 0 := by
  rw [IsMinTourWt, kronNum_digit_ne_zero_iff G hn hw hk]
  refine and_congr Iff.rfl ⟨fun h j hj => ?_, fun h H hH => ?_⟩
  · by_contra hne
    obtain ⟨H, hH, rfl⟩ := (kronNum_digit_ne_zero_iff G hn hw (by omega)).1 hne
    exact absurd (h H hH) (by omega)
  · by_contra hlt
    have := h (wt w H) (by omega)
    exact (kronNum_digit_ne_zero_iff G hn hw ((wt_le_of_mem_hamCycles G hw hH))).2 ⟨H, hH, rfl⟩ this

end Decode

/-- **TSP at Turing-machine level, with the decoding.** The machine of `theoremTSP`, and: for every
`j ≤ n·W`, digit `j` of its output (in base `2^{bK n}`) is `n` times the number of tours of weight
`j`; the minimum tour weight is the position of the lowest non-zero digit; and the number of
optimal tours is that digit divided by `n`. -/
theorem theoremTSP_decode (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (w : Sym2 (Fin n) → ℕ),
        G.edgeFinset.card ≤ D * n → (∀ e, w e ≤ W) →
        GraphProblems.Outputs M (tspCode G W w) (Nat.bits (kronNum G w))
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n) * ((W : ℝ) + 2) ^ C⌋₊ ∧
        (∀ j ≤ n * W, kronDigit G w j = n * tourCount G w j) ∧
        (0 < n → ∀ k ≤ n * W, IsMinTourWt G w k ↔
          kronDigit G w k ≠ 0 ∧ ∀ j < k, kronDigit G w j = 0) ∧
        (0 < n → ∀ j ≤ n * W, kronDigit G w j / n = tourCount G w j) := by
  obtain ⟨M, C, hfin, hM⟩ := theoremTSP δ hδ D
  refine ⟨M, C, hfin, fun n G _ W w hm hw => ⟨hM n G W w hm hw, fun j hj => kronNum_digit G hw hj,
    fun hn k hk => kronNum_min_iff G hn hw hk, fun hn j hj => kronNum_digit_div G hn hw hj⟩⟩

end EthFollowup.ExactHC
