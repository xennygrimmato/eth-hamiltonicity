/-
# Factoring, module F4: the reader, the procedures, the multiplication-network package

`scratchpad/plans/factoring-plan.md` §3–§4 (row F4); interface `facM-interface.md` (F3/F4).

* `prmOf_polyT`: the parameters of `n` in polynomial time from `n` in unary (`ν` by `Nat.log2`,
  every exponent unary by `Unary.of_le`, the ranges by `PolyT.range`);
* `prepM : List Unit × (List Bool × List Bool) → MCtx`, `(unary g, (w, π)) ↦` the context of
  `n = |w|`, `g`, `N = ofWord w`, the pattern `pat n π`, `P = PM n g` (`prepM_polyT`, uniform in `g`);
* `mulNp := labelProcsW layF parF mulTp` (complete code: membership is the length test);
* `netM g w π`: the network `mulSys` for `g ≥ 2` (an empty network otherwise);
* `SzLen` (size `≤` length of the word), so `size (prepM y) ≤ c(len y + 1)^c` from `prepM_polyT`;
* **`mulPackage_nonempty : ∃ c₀, Nonempty (MulPackage c₀)`** (with `c₀ = 2^16`), and
  `mulPackage : Nonempty (MulPackage (2 ^ 16))`.

Standard axioms only.
-/
import EthFollowup.Factoring.MulCtxPoly

set_option linter.unusedSectionVars false

namespace EthFollowup.Factoring

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks MP MPoly

/-! ## Sizes are at most word lengths -/

/-- The size of a value is at most the length of its word. -/
class SzLen (α : Type) [Enc α] [HasSize α] : Prop where
  le : ∀ x : α, size x ≤ len x

instance : SzLen Unit := ⟨fun u => by rw [len_unit, size_unit] <;> omega⟩
instance : SzLen Bool := ⟨fun b => by rw [len_bool, size_bool] <;> omega⟩
instance : SzLen ℕ := ⟨fun n => by rw [len_nat, size_nat] <;> omega⟩
instance {α β : Type} [Enc α] [Enc β] [HasSize α] [HasSize β] [SzLen α] [SzLen β] : SzLen (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    have := SzLen.le a
    have := SzLen.le b
    rw [len_pair, size_prod]; dsimp only; omega⟩
instance {α : Type} [Enc α] [HasSize α] [SzLen α] : SzLen (Option α) :=
  ⟨fun o => by
    rcases o with _ | a
    · rw [len_none, size_none]; omega
    · have := SzLen.le a; rw [len_some, size_some]; omega⟩
instance {α : Type} [Enc α] [HasSize α] [SzLen α] : SzLen (List α) :=
  ⟨fun l => by
    induction l with
    | nil => rw [len_nil]; simp
    | cons a l ih =>
      have := SzLen.le a
      rw [size_list] at ih
      rw [len_cons, size_list, List.map_cons, List.sum_cons]; omega⟩

/-! ## Parameter bounds -/

theorem ν_le (k : ℕ) : ν k ≤ k + 2 := by
  have h1 := two_pow_ν_le k
  have h2 : ν k < 2 ^ ν k := Nat.lt_two_pow_self
  omega

theorem L1_le (k : ℕ) : L1 k ≤ 2 * (k + 2) := by
  have h := two_pow_ν_le k
  unfold L1 m
  calc 2 ^ (ν k / 4 + 1) ≤ 2 ^ (ν k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 * 2 ^ ν k := by ring
    _ ≤ 2 * (k + 2) := by omega

theorem ℓ1_le_L1 (k : ℕ) : ℓ1 k ≤ L1 k := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)

theorem J_le (k : ℕ) : J k ≤ 128 * (k + 2) := by
  have h := two_pow_ν_le k
  unfold J
  calc 2 ^ (ν k / 2 + 7) ≤ 2 ^ (ν k + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 128 * 2 ^ ν k := by ring
    _ ≤ 128 * (k + 2) := by omega

theorem dg_le (k : ℕ) : dg k ≤ 2048 * (k + 2) := by
  have h := two_pow_ν_le k
  unfold dg
  calc 2 ^ (3 * ν k / 4 + 11) ≤ 2 ^ (ν k + 11) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2048 * 2 ^ ν k := by ring
    _ ≤ 2048 * (k + 2) := Nat.mul_le_mul_left _ h

theorem PM_le (k g : ℕ) : PM k g ≤ 268435456 * (k + 2) := by
  have h1 := dg_le k
  have h2 : (k + 2) / g ≤ k + 2 := Nat.div_le_self _ _
  have e : PM k g = 65536 * ((k + 2) / g + dg k) := by unfold PM; norm_num
  rw [e]
  omega

/-! ## The parameters in polynomial time -/

section Par
variable {α : Type} [Enc α] {n : α → ℕ} (hn : Unary n)
include hn

theorem ν_polyT : PolyT fun x => ν (n x) := by
  have : PolyT fun x => Nat.log2 (n x + 2) := PolyT.log2' (PolyT.add hn.poly (PolyT.const 2))
  exact this.congr fun x => Nat.log2_eq_log_two

theorem m_unary : Unary fun x => m (n x) :=
  Unary.of_le (hn.add (Unary.const 2)) (PolyT.add (PolyT.div (ν_polyT hn) (PolyT.const 4)) (PolyT.const 1))
    fun x => by have := ν_le (n x); unfold m; omega

theorem L1_unary : Unary fun x => L1 (n x) :=
  Unary.of_le (Unary.mul (Unary.const 2) (hn.add (Unary.const 2))) (PolyT.two_pow (m_unary hn))
    fun x => L1_le _

theorem ℓ1_unary : Unary fun x => ℓ1 (n x) :=
  Unary.of_le (L1_unary hn)
    (PolyT.two_pow (Unary.of_le (m_unary hn) (PolyT.sub (m_unary hn).poly (PolyT.const 1))
      fun _ => Nat.sub_le _ _)) fun x => ℓ1_le_L1 _

theorem ℓ_unary : Unary fun x => ℓ (n x) := Unary.mul (ℓ1_unary hn) (ℓ1_unary hn)

theorem b_unary : Unary fun x => b (n x) :=
  Unary.of_le (hn.add (Unary.const 1)) (PolyT.add (PolyT.div hn.poly (ℓ_unary hn).poly) (PolyT.const 1))
    fun x => by have := Nat.div_le_self (n x) (ℓ (n x)); unfold b; omega

theorem J_unary : Unary fun x => J (n x) :=
  Unary.of_le (Unary.mul (Unary.const 128) (hn.add (Unary.const 2)))
    (PolyT.two_pow (Unary.of_le (hn.add (Unary.const 9))
      (PolyT.add (PolyT.div (ν_polyT hn) (PolyT.const 2)) (PolyT.const 7))
      fun x => by have := ν_le (n x); omega)) fun x => J_le _

theorem W_unary : Unary fun x => W (n x) := (J_unary hn).add (Unary.const 2)

theorem dg_unary : Unary fun x => dg (n x) :=
  Unary.of_le (Unary.mul (Unary.const 2048) (hn.add (Unary.const 2)))
    (PolyT.two_pow (Unary.of_le (hn.add (Unary.const 13))
      (PolyT.add (PolyT.div (PolyT.mul (PolyT.const 3) (ν_polyT hn)) (PolyT.const 4)) (PolyT.const 11))
      fun x => by have := ν_le (n x); omega)) fun x => dg_le _

theorem numWires_unary : Unary fun x => numWires (n x) := by
  have h1 := (ℓ1_unary hn).poly
  have h2 := (L1_unary hn).poly
  have h3 := (ℓ_unary hn).poly
  have hp : PolyT fun x => numWires (n x) := by
    have e : ∀ x, numWires (n x) = 2 * ℓ (n x) + 2 * (L1 (n x) * ℓ1 (n x)) + 5 * (L1 (n x) * L1 (n x)) +
        (L1 (n x) + ℓ1 (n x) * L1 (n x) - 1) := fun x => rfl
    refine PolyT.congr ?_ fun x => (e x).symm
    exact PolyT.add (PolyT.add (PolyT.add (PolyT.mul (PolyT.const 2) h3) (PolyT.mul (PolyT.const 2)
      (PolyT.mul h2 h1))) (PolyT.mul (PolyT.const 5) (PolyT.mul h2 h2)))
      (PolyT.sub (PolyT.add h2 (PolyT.mul h1 h2)) (PolyT.const 1))
  exact Unary.of_le (Unary.mul (Unary.const 30) (ℓ_unary hn)) hp fun x => numWires_le_ℓ _

theorem numVerts_unary : Unary fun x => numVerts (n x) := by
  have h1 := (ℓ1_unary hn).poly
  have h2 := (L1_unary hn).poly
  have h3 := (ℓ_unary hn).poly
  have hp : PolyT fun x => numVerts (n x) := by
    have e : ∀ x, numVerts (n x) = 2 * ℓ (n x) + 2 * ℓ1 (n x) + 3 * L1 (n x) + L1 (n x) * L1 (n x) +
        L1 (n x) + (L1 (n x) + ℓ1 (n x) * L1 (n x)) := fun x => rfl
    refine PolyT.congr ?_ fun x => (e x).symm
    exact PolyT.add (PolyT.add (PolyT.add (PolyT.add (PolyT.add (PolyT.mul (PolyT.const 2) h3)
      (PolyT.mul (PolyT.const 2) h1)) (PolyT.mul (PolyT.const 3) h2)) (PolyT.mul h2 h2)) h2)
      (PolyT.add h2 (PolyT.mul h1 h2))
  exact Unary.of_le (Unary.mul (Unary.const 24) (ℓ_unary hn)) hp fun x => numVerts_le _

theorem wTab_polyT : PolyT fun x => wTab (n x) := by
  have hJ := J_unary hn
  have hL := L1_unary hn
  have hfst : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hsnd : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hJq : PolyT fun q : α × ℕ => J (n q.1) := PolyT.comp (f := fun x => J (n x)) hJ.poly hfst
  have hLq : PolyT fun q : α × ℕ => L1 (n q.1) := PolyT.comp (f := fun x => L1 (n x)) hL.poly hfst
  have hwE : Unary fun q : α × ℕ => wE (n q.1) q.2 :=
    Unary.of_le (Unary.comp (f := fun x => 2 * J (n x)) (Unary.mul (Unary.const 2) hJ) hfst)
      (PolyT.mul (PolyT.div (PolyT.mul (PolyT.const 2) hJq) hLq) (PolyT.mod hsnd hLq))
      fun q => (wE_lt _ _).le
  exact PolyT.map (f := fun x e => wP (n x) e) (PolyT.two_pow hwE) (PolyT.range hL)

/-- **The parameters of `n`, in polynomial time from `n` in unary.** -/
theorem prmOf_polyT : PolyT fun x => prmOf (n x) := by
  have hl1 := ℓ1_unary hn
  have hL1 := L1_unary hn
  have hb := b_unary hn
  have hJ := J_unary hn
  have hW : PolyT fun x => List.replicate (W (n x)) () := W_unary hn
  have hm := m_unary hn
  have hiL : PolyT fun x => iL (n x) :=
    PolyT.two_pow (Unary.of_le (Unary.mul (Unary.const 2) hJ)
      (PolyT.sub (PolyT.mul (PolyT.const 2) hJ.poly) hm.poly) fun _ => Nat.sub_le _ _)
  have hM : PolyT fun x => M (n x) := PolyT.add (PolyT.two_pow hJ) (PolyT.const 1)
  have hpb : PolyT fun x => 2 ^ b (n x) := PolyT.two_pow hb
  have hwT := wTab_polyT hn
  have r1 : PolyT fun x => List.range (ℓ1 (n x)) := PolyT.range hl1
  have r2 : PolyT fun x => List.range (L1 (n x)) := PolyT.range hL1
  have r3 : PolyT fun x => List.range (b (n x)) := PolyT.range hb
  have r4 : PolyT fun x => List.range (numWires (n x)) := PolyT.range (numWires_unary hn)
  have r5 : PolyT fun x => List.range (numVerts (n x)) := PolyT.range (numVerts_unary hn)
  unfold prmOf
  exact PolyT.prodMk (PolyT.prodMk (PolyT.prodMk hl1.poly hl1.poly) (PolyT.prodMk hL1.poly hL1.poly))
    (PolyT.prodMk (PolyT.prodMk (PolyT.prodMk hb.poly hpb) (PolyT.prodMk hM hiL))
      (PolyT.prodMk (PolyT.prodMk hW hwT)
        (PolyT.prodMk (PolyT.prodMk (PolyT.prodMk r1 r1) (PolyT.prodMk r2 r2))
          (PolyT.prodMk r3 (PolyT.prodMk r4 r5)))))

theorem pat_polyT {π : α → List Bool} (hπ : PolyT π) : PolyT fun x => pat (n x) (π x) := by
  have hnB : Unary fun x => nB (n x) := Unary.mul (ℓ_unary hn) (b_unary hn)
  have hfst : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hnq : PolyT fun q : α × ℕ => n q.1 := PolyT.comp (f := n) hn.poly hfst
  have hπq : PolyT fun q : α × ℕ => π q.1 := PolyT.comp (f := π) hπ hfst
  have hs : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hbody : PolyT fun q : α × ℕ => patBit (n q.1) (π q.1) q.2 := by
    unfold patBit
    exact PolyT.ite' (PolyT.decide_le hnq hs) (PolyT.const (some false))
      (PolyT.ite' (PolyT.decide_le (PolyT.sub hnq (PolyT.length hπq)) hs)
        (PolyT.some' (PolyT.getD (PolyT.reverse hπq) (PolyT.sub hs (PolyT.sub hnq (PolyT.length hπq)))
          (PolyT.const false))) (PolyT.const none))
  exact PolyT.map (f := fun x j => patBit (n x) (π x) j) hbody (PolyT.range hnB)

theorem PM_unary {g : α → ℕ} (hg : Unary g) : Unary fun x => PM (n x) (g x) := by
  unfold PM
  refine Unary.mul (Unary.const _) (Unary.add ?_ (dg_unary hn))
  exact Unary.of_le (hn.add (Unary.const 2)) (PolyT.div (hn.add (Unary.const 2)).poly hg.poly)
    fun x => Nat.div_le_self _ _

end Par

/-! ## The reader -/

/-- **The reader**: `(g in unary, (w, π)) ↦` the context of `n = |w|`, `g`, `N = ofWord w`, the
pattern of `π`, `P = PM n g`. -/
def prepM (q : List Unit × (List Bool × List Bool)) : MCtx :=
  mctxOf (prmOf q.2.1.length) q.1.length (ofWord q.2.1) (pat q.2.1.length q.2.2) (PM q.2.1.length q.1.length)

theorem prepM_unary (g : ℕ) (w π : List Bool) :
    prepM (Printed.unary g, (w, π)) = mctxOf (prmOf w.length) g (ofWord w) (pat w.length π) (PM w.length g) := by
  simp only [prepM, Printed.unary, List.length_replicate]

/-- **The reader is polynomial-time** (uniformly in `g`). -/
theorem prepM_polyT : PolyT prepM := by
  have hw : PolyT fun q : List Unit × (List Bool × List Bool) => q.2.1 := PolyT.fst (PolyT.snd PolyT.id')
  have hπ : PolyT fun q : List Unit × (List Bool × List Bool) => q.2.2 := PolyT.snd (PolyT.snd PolyT.id')
  have hn : Unary fun q : List Unit × (List Bool × List Bool) => q.2.1.length := Unary.of_length hw
  have hg : Unary fun q : List Unit × (List Bool × List Bool) => q.1.length :=
    Unary.of_length (PolyT.fst PolyT.id')
  exact mctxOf_polyT (prmOf_polyT hn) hg (PolyT.ofWord' hw) (pat_polyT hn hπ) (PM_unary hn hg)

/-! ## The procedures and the networks -/

/-- The layout of a context. -/
def layF (c : MCtx) : Lay := c.1
/-- No copy bits. -/
def parF (_ : MCtx × (ℕ × List Bool)) : Bool := false

theorem layF_polyT : PolyT layF := PolyT.fst PolyT.id'
theorem parF_polyT : PolyT parF := PolyT.const false

/-- **The procedures of the multiplication networks.** -/
def mulNp : Procs MCtx := labelProcsW layF parF mulTp

theorem mulNp_keeps : mulNp.Keeps := labelProcsW_keeps layF_polyT parF_polyT mulTp_poly

/-- An empty network (for `g < 2`, never used). -/
def emptyNet (g : ℕ) : Net g :=
  ⟨fun _ => 0, fun _ => ∅, fun _ _ => 0, fun _ _ _ _ => 0, fun _ _ => 0, fun _ _ _ _ => 0⟩

/-- **The multiplication network** of `(g, w, π)`: `mulSys` for `n = |w|`, `N = ofWord w`, the
pattern of `π`, if `g ≥ 2`. -/
def netM (g : ℕ) (w π : List Bool) : Net g :=
  if h : 2 ≤ g then (mulSys w.length (ofWord w) (pat w.length π) g h).net (labCode w.length) else emptyNet g

/-- The state bound. -/
def SB (g : ℕ) (w π : List Bool) : ℕ :=
  SM (prepM (Printed.unary g, (w, π))) g (PM w.length g) + size (prepM (Printed.unary g, (w, π))) +
    2 * g + 4 * PM w.length g + 8

theorem netM_isNet {g : ℕ} {w π : List Bool} (hg : 2 ≤ g) :
    IsNetwork mulNp (prepM (Printed.unary g, (w, π))) (netM g w π) (PM w.length g) 1 1 (SB g w π) := by
  have hN := mulSys_is (N := ofWord w) (pt := pat w.length π) (n := w.length) hg
  have h := LabelSystem.labelProcsW_isNet (lay := layF) (par := parF)
    (mulSys w.length (ofWord w) (pat w.length π) g hg) (labCode w.length) (labCode_complete _) mulTp
    (c := mctxOf (prmOf w.length) g (ofWord w) (pat w.length π) (PM w.length g)) (cs := codesM w.length)
    hN (layM_describes hg _) (fun j => j.elim) (mulSys_tspec hg _ fun a => hN.len_le a) le_rfl
  rw [netM, dif_pos hg]
  unfold SB
  rw [prepM_unary]
  exact h

/-! ## The package -/

/-- **The multiplication-network package** (`c₀ = 2^16`). -/
theorem mulPackage : Nonempty (MulPackage (2 ^ 16)) := by
  obtain ⟨-, c', -, hc⟩ := prepM_polyT
  have hX : ∀ (g : ℕ) (w : List Bool) (q : ℕ), 1 ≤ q → 1 ≤ q * (w.length + g + 2) ^ q := fun g w q hq =>
    Nat.mul_le_mul hq (Nat.one_le_pow _ _ (by omega))
  refine ⟨{
    Ctx := MCtx
    Np := mulNp
    keeps := mulNp_keeps
    P_unary := labelProcsW_P layF_polyT
    B_unary := labelProcsW_B layF_polyT
    prep := prepM
    prep_poly := prepM_polyT
    q := 3 * (c' * 6 ^ c') + 2147483648 + c' + 1
    net := netM
    P := fun g w _ => PM w.length g
    B := fun _ _ _ => 1
    τ := fun _ _ _ => 1
    S := SB
    isNet := fun g w π hg _ _ => netM_isNet hg
    value := fun g w π hg _ hπ => by
      rw [netM, dif_pos hg]
      exact mulNet_value hg (ofWord_lt w) hπ
    U_le := fun g w π hg _ _ => by
      rw [netM, dif_pos hg]
      have := mulSys_U_le (N := ofWord w) (pt := pat w.length π) (n := w.length) hg
      exact this.trans (Nat.mul_le_mul_right _ (by norm_num))
    P_le := fun g w π _ _ _ => le_of_eq rfl
    B_le := fun g w π _ _ _ => hX g w _ (by omega)
    τ_le := fun g w π _ _ _ => hX g w _ (by omega)
    S_le := fun g w π _ _ hπ => by
      set y := (Printed.unary g, (w, π)) with hy
      set c := prepM y
      have h1 : size c ≤ len c := SzLen.le c
      have h2 : len c ≤ c' * (len y + 1) ^ c' := hc y
      have hly : len y ≤ 4 * g + 6 * w.length + 10 := by
        rw [hy, len_pair, len_pair, len_units, len_bools, len_bools]
        simp only [Printed.unary, List.length_replicate]
        omega
      set X := w.length + g + 2 with hXd
      have hX1 : 1 ≤ X := by omega
      have h3 : len y + 1 ≤ 6 * X := by omega
      have h4 : c' * (len y + 1) ^ c' ≤ c' * 6 ^ c' * X ^ c' := by
        calc c' * (len y + 1) ^ c' ≤ c' * (6 * X) ^ c' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)
          _ = c' * 6 ^ c' * X ^ c' := by rw [mul_pow]; ring
      set q := 3 * (c' * 6 ^ c') + 2147483648 + c' + 1 with hq
      have h5 : X ^ c' ≤ X ^ q := Nat.pow_le_pow_right hX1 (by omega)
      have h6 : X ≤ X ^ q := by
        calc X = X ^ 1 := (pow_one X).symm
          _ ≤ X ^ q := Nat.pow_le_pow_right hX1 (by omega)
      have h7 : c' * 6 ^ c' * X ^ c' ≤ c' * 6 ^ c' * X ^ q := Nat.mul_le_mul_left _ h5
      have hP := PM_le w.length g
      have e' : ∀ Y : ℕ, q * Y = 3 * (c' * 6 ^ c' * Y) + 2147483648 * Y + (c' + 1) * Y := fun Y => by
        rw [hq]; ring
      have e := e' (X ^ q)
      show SM c g (PM w.length g) + size c + 2 * g + 4 * PM w.length g + 8 + size c ≤ q * X ^ q
      unfold SM
      rw [e]
      generalize c' * 6 ^ c' * X ^ q = Z at *
      generalize X ^ q = Y at *
      generalize c' * 6 ^ c' * X ^ c' = Z' at *
      generalize (c' + 1) * Y = Y' at *
      generalize c' * (len y + 1) ^ c' = T at *
      omega }⟩

/-- **The multiplication-network package exists** (the hypothesis of `minFac_TM_of_pkg`). -/
theorem mulPackage_nonempty : ∃ c₀ : ℕ, Nonempty (MulPackage c₀) := ⟨2 ^ 16, mulPackage⟩

end EthFollowup.Factoring
