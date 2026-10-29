/-
# Theorem Q1, bridge part 7: the context in polynomial time

`PolyT` of every word-level function that builds the context `qCtx` from the scan state: the
partition lists, the factor descriptors (with the residue matrices), the layout.
-/
import EthFollowup.Quantum.QScan

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Groundwork Groundwork.Prog

namespace QP

variable {γ : Type} [Enc γ]

theorem rangeL_polyT {α : Type} [Enc α] {l : γ → List α} (hl : PolyT l) : PolyT fun x => List.range (l x).length :=
  PolyT.range (Unary.of_length hl)

@[fun_prop] theorem blkAt_polyT {st : γ → SS} {t : γ → ℕ} (hs : PolyT st) (ht : PolyT t) :
    PolyT fun x => blkAt (st x) (t x) := by unfold blkAt dBlk; fun_prop

@[fun_prop] theorem srcOf_polyT {b : γ → Blk} {i : γ → Bool} (hb : PolyT b) (hi : PolyT i) :
    PolyT fun x => srcOf (b x) (i x) := by unfold srcOf; fun_prop

@[fun_prop] theorem readsB_polyT {b : γ → Blk} {v : γ → ℕ × Bool} (hb : PolyT b) (hv : PolyT v) :
    PolyT fun x => readsB (b x) (v x) := by unfold readsB; fun_prop

@[fun_prop] theorem reader_polyT {st : γ → SS} {v : γ → ℕ × Bool} (hs : PolyT st) (hv : PolyT v) :
    PolyT fun x => reader (st x) (v x) := by
  have := rangeL_polyT (l := fun x => (st x).1) (by fun_prop)
  unfold reader; fun_prop

@[fun_prop] theorem rgN_polyT {st : γ → SS} {g : γ → ℕ} {v : γ → ℕ × Bool} (hs : PolyT st) (hg : PolyT g)
    (hv : PolyT v) : PolyT fun x => rgN (st x) (g x) (v x) := by unfold rgN; fun_prop

@[fun_prop] theorem crossN_polyT {st : γ → SS} {g : γ → ℕ} {v : γ → ℕ × Bool} (hs : PolyT st) (hg : PolyT g)
    (hv : PolyT v) : PolyT fun x => crossN (st x) (g x) (v x) := by unfold crossN; fun_prop

@[fun_prop] theorem allN_polyT {st : γ → SS} (hs : PolyT st) : PolyT fun x => allN (st x).1.length := by
  have := rangeL_polyT (l := fun x => (st x).1) (by fun_prop)
  unfold allN; fun_prop

@[fun_prop] theorem clN_polyT {st : γ → SS} {g : γ → ℕ} (hs : PolyT st) (hg : PolyT g) :
    PolyT fun x => clN (st x) (g x) := by unfold clN; fun_prop

@[fun_prop] theorem ilN_polyT {st : γ → SS} {g a : γ → ℕ} (hs : PolyT st) (hg : PolyT g) (ha : PolyT a) :
    PolyT fun x => ilN (st x) (g x) (a x) := by unfold ilN; fun_prop

@[fun_prop] theorem itemV_polyT {st : γ → SS} {g k : γ → ℕ} (hs : PolyT st) (hg : PolyT g) (hk : PolyT k) :
    PolyT fun x => itemV (st x) (g x) (k x) := by unfold itemV; fun_prop

@[fun_prop] theorem loN_polyT {st : γ → SS} {g k : γ → ℕ} (hs : PolyT st) (hg : PolyT g) (hk : PolyT k) :
    PolyT fun x => loN (st x) (g x) (k x) := by unfold loN; fun_prop

@[fun_prop] theorem hiN_polyT {st : γ → SS} {g k : γ → ℕ} (hs : PolyT st) (hg : PolyT g) (hk : PolyT k) :
    PolyT fun x => hiN (st x) (g x) (k x) := by unfold hiN; fun_prop

@[fun_prop] theorem incN_polyT {st : γ → SS} {g a : γ → ℕ} (hs : PolyT st) (hg : PolyT g) (ha : PolyT a) :
    PolyT fun x => incN (st x) (g x) (a x) := by
  have hr := rangeL_polyT (l := fun x => clN (st x) (g x)) (clN_polyT hs hg)
  have hlo : PolyT fun p : γ × ℕ => loN (st p.1) (g p.1) p.2 :=
    loN_polyT (hs.comp PolyT.id'.fst) (hg.comp PolyT.id'.fst) PolyT.id'.snd
  have hhi : PolyT fun p : γ × ℕ => hiN (st p.1) (g p.1) p.2 :=
    hiN_polyT (hs.comp PolyT.id'.fst) (hg.comp PolyT.id'.fst) PolyT.id'.snd
  have hpred : PolyT fun p : γ × ℕ => decide (loN (st p.1) (g p.1) p.2 = a p.1 ∨ hiN (st p.1) (g p.1) p.2 = a p.1) :=
    PolyT.decide_or (PolyT.decide_eq hlo (ha.comp PolyT.id'.fst)) (PolyT.decide_eq hhi (ha.comp PolyT.id'.fst))
  exact PolyT.filter (f := fun x k => decide (loN (st x) (g x) k = a x ∨ hiN (st x) (g x) k = a x)) hpred hr

@[fun_prop] theorem refN_polyT {st : γ → SS} {g a : γ → ℕ} {v : γ → ℕ × Bool} (hs : PolyT st) (hg : PolyT g)
    (ha : PolyT a) (hv : PolyT v) : PolyT fun x => refN (st x) (g x) (a x) (v x) := by
  unfold refN; fun_prop

@[fun_prop] theorem srcRefN_polyT {st : γ → SS} {g a q : γ → ℕ} {xs : γ → List Bool} {s : γ → Src}
    (hs : PolyT st) (hg : PolyT g) (ha : PolyT a) (hx : PolyT xs) (hq : PolyT q) (hs' : PolyT s) :
    PolyT fun x => srcRefN (st x) (g x) (a x) (xs x) (q x) (s x) := by
  unfold srcRefN; fun_prop

@[fun_prop] theorem tailGrpN_polyT {st : γ → SS} {g q : γ → ℕ} (hs : PolyT st) (hg : PolyT g) (hq : PolyT q) :
    PolyT fun x => tailGrpN (st x) (g x) (q x) := by unfold tailGrpN; fun_prop

/-! ### Residue matrices -/

/-- Division and remainder as atoms for `fun_prop`. -/
def dv (a b : ℕ) : ℕ := a / b
def md (a b : ℕ) : ℕ := a % b

@[fun_prop] theorem dv_polyT {a b : γ → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => dv (a x) (b x) :=
  PolyT.div ha hb
@[fun_prop] theorem md_polyT {a b : γ → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => md (a x) (b x) :=
  PolyT.mod ha hb

theorem m2mul_eq (M : ℕ) (A B : List ℕ) : m2mul M A B = (List.range 4).map fun e =>
    md (A.getD (2 * dv e 2) 0 * B.getD (md e 2) 0 + A.getD (2 * dv e 2 + 1) 0 * B.getD (2 + md e 2) 0) M := rfl

theorem m4mul_eq (M : ℕ) (A B : List ℕ) : m4mul M A B = (List.range 16).map fun e =>
    md ((List.range 4).map fun j => A.getD (4 * dv e 4 + j) 0 * B.getD (4 * j + md e 4) 0).sum M := rfl

theorem k22N_eq (M : ℕ) (A B : List ℕ) : k22N M A B = (List.range 16).map fun e =>
    md (A.getD (2 * dv e 8 + dv (md e 4) 2) 0 * B.getD (2 * md (dv e 4) 2 + md e 2) 0) M := rfl

@[fun_prop] theorem m2mul_polyT {M : γ → ℕ} {A B : γ → List ℕ} (hM : PolyT M) (hA : PolyT A) (hB : PolyT B) :
    PolyT fun x => m2mul (M x) (A x) (B x) := by
  have h4 : PolyT fun _ : γ => List.range 4 := PolyT.const _
  have h : PolyT fun x => (List.range 4).map fun e =>
      md ((A x).getD (2 * dv e 2) 0 * (B x).getD (md e 2) 0 + (A x).getD (2 * dv e 2 + 1) 0 *
        (B x).getD (2 + md e 2) 0) (M x) := by fun_prop
  exact h.congr fun x => (m2mul_eq _ _ _).symm

/-- One entry of a product of `4 × 4` matrices. -/
def m4e (M : ℕ) (A B : List ℕ) (e : ℕ) : ℕ :=
  md ((List.range 4).map fun j => A.getD (4 * dv e 4 + j) 0 * B.getD (4 * j + md e 4) 0).sum M

@[fun_prop] theorem m4e_polyT {M e : γ → ℕ} {A B : γ → List ℕ} (hM : PolyT M) (hA : PolyT A) (hB : PolyT B)
    (he : PolyT e) : PolyT fun x => m4e (M x) (A x) (B x) (e x) := by
  have h4 : PolyT fun _ : γ => List.range 4 := PolyT.const _
  have hj : PolyT fun q : γ × ℕ =>
      (A q.1).getD (4 * dv (e q.1) 4 + q.2) 0 * (B q.1).getD (4 * q.2 + md (e q.1) 4) 0 := by fun_prop
  have hm : PolyT fun x => (List.range 4).map fun j =>
      (A x).getD (4 * dv (e x) 4 + j) 0 * (B x).getD (4 * j + md (e x) 4) 0 := by fun_prop
  exact md_polyT (PolyT.sum hm) hM

@[fun_prop] theorem m4mul_polyT {M : γ → ℕ} {A B : γ → List ℕ} (hM : PolyT M) (hA : PolyT A) (hB : PolyT B) :
    PolyT fun x => m4mul (M x) (A x) (B x) := by
  have h16 : PolyT fun _ : γ => List.range 16 := PolyT.const _
  have h : PolyT fun x => (List.range 16).map (m4e (M x) (A x) (B x)) := by fun_prop
  exact h.congr fun x => rfl

@[fun_prop] theorem k22N_polyT {M : γ → ℕ} {A B : γ → List ℕ} (hM : PolyT M) (hA : PolyT A) (hB : PolyT B) :
    PolyT fun x => k22N (M x) (A x) (B x) := by
  have h16 : PolyT fun _ : γ => List.range 16 := @PolyT.const γ (List ℕ) _ _ (List.range 16)
  have h : PolyT fun x => (List.range 16).map fun e =>
      md ((A x).getD (2 * dv e 8 + dv (md e 4) 2) 0 * (B x).getD (2 * md (dv e 4) 2 + md e 2) 0) (M x) := by
    fun_prop
  exact h.congr fun x => (k22N_eq _ _ _).symm

@[fun_prop] theorem negN_polyT {M a : γ → ℕ} (hM : PolyT M) (ha : PolyT a) : PolyT fun x => negN (M x) (a x) := by
  unfold negN; fun_prop

@[fun_prop] theorem g1N_polyT {M z₁ z₂ z₃ u : γ → ℕ} (hM : PolyT M) (h1 : PolyT z₁) (h2 : PolyT z₂) (h3 : PolyT z₃)
    (hu : PolyT u) : PolyT fun x => g1N (M x) (z₁ x) (z₂ x) (z₃ x) (u x) := by unfold g1N; fun_prop

@[fun_prop] theorem g2N_polyT {M z₁ z₂ z₃ u : γ → ℕ} (hM : PolyT M) (h1 : PolyT z₁) (h2 : PolyT z₂) (h3 : PolyT z₃)
    (hu : PolyT u) : PolyT fun x => g2N (M x) (z₁ x) (z₂ x) (z₃ x) (u x) := by unfold g2N diag4; fun_prop

theorem len_list_le {l : List ℕ} {M : ℕ} (h : ∀ e ∈ l, e ≤ M) : len l ≤ l.length * (len M + 2) + 2 := by
  induction l with
  | nil => rw [len_nil]; omega
  | cons e l ih =>
    rw [len_cons, List.length_cons]
    have h1 := len_nat_mono (h e List.mem_cons_self)
    have h2 := ih fun e' he => h e' (List.mem_cons_of_mem _ he)
    rw [Nat.succ_mul]; omega

theorem len_m2mul_le {M : ℕ} (hM : 0 < M) (A B : List ℕ) : len (m2mul M A B) ≤ 4 * len M + 10 := by
  have h := len_list_le (l := m2mul M A B) (M := M) fun e he => by
    unfold m2mul at he
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
    exact (Nat.mod_lt _ hM).le
  have hl : (m2mul M A B).length = 4 := by simp [m2mul]
  rw [hl] at h; omega

/-- Runs of single-qubit gates, for a modulus `M x > 0`. -/
theorem prodLN_polyT {M z₁ z₂ z₃ : γ → ℕ} {r : γ → List ℕ} (hM : PolyT M) (h1 : PolyT z₁) (h2 : PolyT z₂)
    (h3 : PolyT z₃) (hr : PolyT r) (hpos : ∀ x, 0 < M x) :
    PolyT fun x => prodLN (M x) (z₁ x) (z₂ x) (z₃ x) (r x) := by
  unfold prodLN
  obtain ⟨-, t, ht, -, -, hlen⟩ := hM.elim
  refine PolyT.foldl_add (l := r) (a := fun _ => [1, 0, 0, 1])
    (g := fun x A u => m2mul (M x) (g1N (M x) (z₁ x) (z₂ x) (z₃ x) u) A) hr (by fun_prop) (by fun_prop)
    ⟨fun m => 4 * t m + 10, ((PB.const 4).mul ht).add (PB.const 10), fun x c e _ => ?_⟩
  have := len_m2mul_le (hpos x) (g1N (M x) (z₁ x) (z₂ x) (z₃ x) e) c
  have := hlen x
  dsimp only
  omega

theorem blkEntN_polyT {M z₁ z₂ z₃ : γ → ℕ} {b : γ → Blk} (hM : PolyT M) (h1 : PolyT z₁) (h2 : PolyT z₂)
    (h3 : PolyT z₃) (hb : PolyT b) (hpos : ∀ x, 0 < M x) :
    PolyT fun x => blkEntN (M x) (z₁ x) (z₂ x) (z₃ x) (b x) := by
  have p1 := prodLN_polyT (r := fun x => (b x).2.2.2.1) hM h1 h2 h3 (by fun_prop) hpos
  have p2 := prodLN_polyT (r := fun x => (b x).2.2.2.2) hM h1 h2 h3 (by fun_prop) hpos
  unfold blkEntN; fun_prop

/-! ### The descriptors, the layout, the context -/

section Ctx

variable {st : γ → SS} {g n M z₁ z₂ z₃ : γ → ℕ} {xs ys : γ → List Bool}

theorem blockDesc_polyT (hs : PolyT st) (hg : PolyT g) (hM : PolyT M) (h1 : PolyT z₁) (h2 : PolyT z₂)
    (h3 : PolyT z₃) (hx : PolyT xs) (hpos : ∀ x, 0 < M x) :
    PolyT fun p : γ × ℕ × ℕ => blockDesc (st p.1) (g p.1) (M p.1) (z₁ p.1) (z₂ p.1) (z₃ p.1) (xs p.1) p.2.1 p.2.2 := by
  have hb := blkEntN_polyT (γ := γ × ℕ × ℕ) (M := fun p => M p.1) (z₁ := fun p => z₁ p.1) (z₂ := fun p => z₂ p.1)
    (z₃ := fun p => z₃ p.1) (b := fun p => blkAt (st p.1) p.2.2) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) fun p => hpos p.1
  unfold blockDesc; fun_prop

theorem tailDesc_polyT (hs : PolyT st) (hg : PolyT g) (hM : PolyT M) (h1 : PolyT z₁) (h2 : PolyT z₂)
    (h3 : PolyT z₃) (hx : PolyT xs) (hy : PolyT ys) (hpos : ∀ x, 0 < M x) :
    PolyT fun p : γ × ℕ × ℕ =>
      tailDesc (st p.1) (g p.1) (M p.1) (z₁ p.1) (z₂ p.1) (z₃ p.1) (xs p.1) (ys p.1) p.2.1 p.2.2 := by
  have hb := prodLN_polyT (γ := γ × ℕ × ℕ) (M := fun p => M p.1) (z₁ := fun p => z₁ p.1) (z₂ := fun p => z₂ p.1)
    (z₃ := fun p => z₃ p.1) (r := fun p => (st p.1).2.1.getD p.2.2 []) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) fun p => hpos p.1
  unfold tailDesc; fun_prop

theorem descN_polyT (hs : PolyT st) (hg : PolyT g) (hn : Unary n) (hM : PolyT M) (h1 : PolyT z₁)
    (h2 : PolyT z₂) (h3 : PolyT z₃) (hx : PolyT xs) (hy : PolyT ys) (hpos : ∀ x, 0 < M x) :
    PolyT fun p : γ × ℕ => descN (st p.1) (g p.1) (n p.1) (M p.1) (z₁ p.1) (z₂ p.1) (z₃ p.1) (xs p.1) (ys p.1) p.2 := by
  have hb := blockDesc_polyT hs hg hM h1 h2 h3 hx hpos
  have ht := tailDesc_polyT hs hg hM h1 h2 h3 hx hy hpos
  have hb' : PolyT fun q : (γ × ℕ) × ℕ =>
      blockDesc (st q.1.1) (g q.1.1) (M q.1.1) (z₁ q.1.1) (z₂ q.1.1) (z₃ q.1.1) (xs q.1.1) q.1.2 q.2 :=
    PolyT.comp (g := fun q : (γ × ℕ) × ℕ => (q.1.1, q.1.2, q.2)) hb (by fun_prop)
  have ht' : PolyT fun q : (γ × ℕ) × ℕ =>
      tailDesc (st q.1.1) (g q.1.1) (M q.1.1) (z₁ q.1.1) (z₂ q.1.1) (z₃ q.1.1) (xs q.1.1) (ys q.1.1) q.1.2 q.2 :=
    PolyT.comp (g := fun q : (γ × ℕ) × ℕ => (q.1.1, q.1.2, q.2)) ht (by fun_prop)
  have hr1 := rangeL_polyT (γ := γ × ℕ) (l := fun p => (st p.1).1) (by fun_prop)
  have hr2 : PolyT fun p : γ × ℕ => List.range (n p.1) := PolyT.range (hn.comp (by fun_prop))
  unfold descN; fun_prop

@[fun_prop] theorem onPairN_polyT {a b k : γ → ℕ} (hs : PolyT st) (hg : PolyT g) (ha : PolyT a) (hb : PolyT b)
    (hk : PolyT k) : PolyT fun x => onPairN (st x) (g x) (a x) (b x) (k x) := by
  have hlo := loN_polyT hs hg hk
  have hhi := hiN_polyT hs hg hk
  unfold onPairN
  exact PolyT.decide_or (PolyT.decide_and (PolyT.decide_eq hlo ha) (PolyT.decide_eq hhi hb))
    (PolyT.decide_and (PolyT.decide_eq hlo hb) (PolyT.decide_eq hhi ha))

@[fun_prop] theorem pairN_polyT {a b : γ → ℕ} (hs : PolyT st) (hg : PolyT g) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => pairN (st x) (g x) (a x) (b x) := by
  have := rangeL_polyT (l := fun x => clN (st x) (g x)) (by fun_prop)
  unfold pairN; fun_prop

theorem layQ_polyT {P B : γ → ℕ} (hs : PolyT st) (hg : Unary g) (hP : Unary P) (hB : Unary B) :
    PolyT fun x => layQ (st x) (g x) (P x) (B x) := by
  have hr : PolyT fun x => List.range (g x) := PolyT.range hg
  have hg' : PolyT g := hg.poly
  have hi : PolyT fun p : γ × ℕ => List.replicate (incN (st p.1) (g p.1) p.2).length () :=
    Unary.of_length (by fun_prop)
  unfold layQ; fun_prop

/-- **The context in polynomial time.** -/
theorem qCtx_polyT {P B : γ → ℕ} (hs : PolyT st) (hg : Unary g) (hn : Unary n) (hM : PolyT M) (h1 : PolyT z₁)
    (h2 : PolyT z₂) (h3 : PolyT z₃) (hx : PolyT xs) (hy : PolyT ys) (hP : Unary P) (hB : Unary B)
    (hpos : ∀ x, 0 < M x) :
    PolyT fun x => qCtx (st x) (g x) (n x) (M x) (z₁ x) (z₂ x) (z₃ x) (xs x) (ys x) (P x) (B x) := by
  have hl := layQ_polyT hs hg hP hB
  have hd := descN_polyT hs hg.poly hn hM h1 h2 h3 hx hy hpos
  have hr : PolyT fun x => List.range (g x) := PolyT.range hg
  have hg' : PolyT g := hg.poly
  have hi : PolyT fun p : γ × ℕ => List.replicate (ilN (st p.1) (g p.1) p.2).length () :=
    Unary.of_length (by fun_prop)
  unfold qCtx; fun_prop

end Ctx

end QP

end EthFollowup.Quantum
