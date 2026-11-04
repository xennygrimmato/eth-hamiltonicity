/-
# Tree verifiers of an iterated product: the Huffman/Kraft lower bound

A *tree verifier* multiplies the factors d_1,…,d_k along a binary tree T whose leaves carry the factor
sizes ℓ_i (bits).  Each internal node v multiplies its two children; by the cut-rank lemma
(research/iterated-product.md §2.1(a)) the multiplication at v needs at least wt(v) := Σ_{leaves below v} ℓ_i
crossing bits.  So U ≥ cost(T) := Σ_{internal v} wt(v) = Σ_i ℓ_i · depth(i).

Theorem `cost_ge_entropy`:  cost(T) + Σ_i ℓ_i log₂ ℓ_i ≥ L log₂ L  (L = Σ ℓ_i),
i.e. cost(T) ≥ Σ_i ℓ_i log₂(L/ℓ_i), for every tree shape (balanced or not).
Corollary `cost_ge_equal`: k equal leaves of size w give cost ≥ k·w·log₂ k = n log₂ k.
So unbalanced product trees cannot beat n log k; the first idea of the brief is dead in the tree model.
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.unusedSectionVars false

namespace EthFollowup.IterProd

open Real

/-- Binary tree with natural-number leaf weights (factor sizes in bits). -/
inductive BTree
  | leaf (w : ℕ)
  | node (l r : BTree)

namespace BTree

/-- total weight (bits) below a node -/
def wt : BTree → ℕ
  | leaf w => w
  | node l r => wt l + wt r

/-- cost = Σ over internal nodes of the weight below it (= Σ leaves ℓ_i · depth_i) -/
def cost : BTree → ℕ
  | leaf _ => 0
  | node l r => (wt l + wt r) + cost l + cost r

/-- Σ_leaves ℓ log₂ ℓ -/
noncomputable def ent : BTree → ℝ
  | leaf w => (w : ℝ) * logb 2 w
  | node l r => ent l + ent r

/-- all leaf weights positive -/
def pos : BTree → Prop
  | leaf w => 0 < w
  | node l r => pos l ∧ pos r

theorem wt_pos : ∀ T : BTree, pos T → 0 < wt T
  | leaf _, h => h
  | node l r, ⟨hl, _⟩ => by simp only [wt]; have := wt_pos l hl; omega

/-- The one analytic input: `A log₂(L/A) + B log₂(L/B) ≤ L` for `A + B = L`, i.e. binary entropy ≤ 1. -/
theorem entropy_step (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (A + B) * logb 2 (A + B) - A * logb 2 A - B * logb 2 B ≤ A + B := by
  set L := A + B with hL
  have hLpos : 0 < L := by positivity
  set p := A / L with hp
  have hp0 : 0 < p := div_pos hA hLpos
  have hp1 : p < 1 := by rw [hp, div_lt_one hLpos]; linarith
  have hB' : B = L * (1 - p) := by rw [hp]; field_simp; ring
  have hA' : A = L * p := by rw [hp]; field_simp
  have key : L * logb 2 L - A * logb 2 A - B * logb 2 B = L * (binEntropy p / log 2) := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog]
    rw [hA', hB']
    have h1 : logb 2 (L * p) = logb 2 L + logb 2 p := logb_mul hLpos.ne' hp0.ne'
    have h2 : logb 2 (L * (1 - p)) = logb 2 L + logb 2 (1 - p) :=
      logb_mul hLpos.ne' (by linarith)
    rw [h1, h2]
    simp only [logb]
    field_simp
    ring
  rw [key]
  have hbe : binEntropy p ≤ log 2 := binEntropy_le_log_two
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  calc L * (binEntropy p / log 2) ≤ L * (log 2 / log 2) := by
        apply mul_le_mul_of_nonneg_left _ hLpos.le
        exact div_le_div_of_nonneg_right hbe hlog2.le
    _ = L := by rw [div_self hlog2.ne', mul_one]

/-- **Tree bound.** `cost T + Σ ℓ_i log₂ ℓ_i ≥ L log₂ L`. -/
theorem cost_ge_entropy : ∀ T : BTree, pos T →
    (wt T : ℝ) * logb 2 (wt T) ≤ (cost T : ℝ) + ent T
  | leaf w, _ => by simp [wt, cost, ent]
  | node l r, ⟨hl, hr⟩ => by
    have ihl := cost_ge_entropy l hl
    have ihr := cost_ge_entropy r hr
    have hA : (0 : ℝ) < wt l := by exact_mod_cast wt_pos l hl
    have hB : (0 : ℝ) < wt r := by exact_mod_cast wt_pos r hr
    have step := entropy_step (wt l) (wt r) hA hB
    simp only [wt, cost, ent, Nat.cast_add]
    linarith


/-- number of leaves -/
def leaves : BTree → ℕ
  | leaf _ => 1
  | node l r => leaves l + leaves r

/-- all leaves have weight `w` -/
def allLeaves (w : ℕ) : BTree → Prop
  | leaf v => v = w
  | node l r => allLeaves w l ∧ allLeaves w r

theorem wt_of_allLeaves (w : ℕ) : ∀ T : BTree, allLeaves w T → wt T = leaves T * w
  | leaf v, h => by simp only [allLeaves] at h; subst h; simp [wt, leaves]
  | node l r, ⟨hl, hr⟩ => by
    simp only [wt, leaves, wt_of_allLeaves w l hl, wt_of_allLeaves w r hr]; ring

theorem ent_of_allLeaves (w : ℕ) : ∀ T : BTree, allLeaves w T →
    ent T = (leaves T : ℝ) * ((w : ℝ) * logb 2 w)
  | leaf v, h => by simp only [allLeaves] at h; subst h; simp [ent, leaves]
  | node l r, ⟨hl, hr⟩ => by
    simp only [ent, leaves, ent_of_allLeaves w l hl, ent_of_allLeaves w r hr, Nat.cast_add]; ring

theorem pos_of_allLeaves (w : ℕ) (hw : 0 < w) : ∀ T : BTree, allLeaves w T → pos T
  | leaf v, h => by simp only [allLeaves] at h; subst h; exact hw
  | node l r, ⟨hl, hr⟩ => ⟨pos_of_allLeaves w hw l hl, pos_of_allLeaves w hw r hr⟩

/-- **Equal sizes.** A product tree on `k` factors of `w` bits each has `cost ≥ k·w·log₂ k`
(`= n log₂ k` with `n = k w`). -/
theorem cost_ge_equal (T : BTree) (w : ℕ) (hw : 0 < w) (hT : allLeaves w T) :
    (leaves T : ℝ) * w * logb 2 (leaves T) ≤ cost T := by
  have h := cost_ge_entropy T (pos_of_allLeaves w hw T hT)
  rw [wt_of_allLeaves w T hT, ent_of_allLeaves w T hT] at h
  have hk : (0 : ℝ) < leaves T := by
    have := wt_pos T (pos_of_allLeaves w hw T hT)
    rw [wt_of_allLeaves w T hT] at this
    exact_mod_cast Nat.pos_of_mul_pos_right this
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hlog : logb 2 ((leaves T : ℝ) * w) = logb 2 (leaves T) + logb 2 w :=
    logb_mul hk.ne' hw'.ne'
  push_cast at h
  rw [hlog] at h
  nlinarith [h]

end BTree
end EthFollowup.IterProd

#print axioms EthFollowup.IterProd.BTree.cost_ge_entropy
#print axioms EthFollowup.IterProd.BTree.cost_ge_equal
