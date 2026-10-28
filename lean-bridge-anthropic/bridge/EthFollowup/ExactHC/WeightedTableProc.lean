/-
# The weighted node tables as a step machine (TSP, Kronecker substitution)

The weighted analogue of `TableProc.lean` (C1c). The node table of the weighted network
(`WeightedNetwork.lean`) is `σ_a(ℓ) · χ_a(ℓ, y) · I^w_a(ℓ)` with
`I^w_a(ℓ) = z^{w_ℓ(a)} · Σ_{x ⊆ E_int(a)} [deg = 2] · z^{w(x)} · [ω_a](F_a(x) Γ_a(ℓ))` at the Kronecker
point `z = 2^b`. The term number `i` of the stream of `TableProc.lean` (mask `m = i mod 2^p`, choice
`j = i / 2^p`) gets the extra factor `2^{b · (w(x_m) + w_ℓ(a))}`, a shift that depends on the mask only.

* **Data** `TDW = TD × (b in unary, (weights of E_int(a) in unary, weights of δ(a) in unary))`; the
  weights are in unary so that the shift `2^{b·(…)}` is a polynomial-time function (`PolyT.two_pow`).
  `TDescW` says what the data must hold (`TDescW.toTDesc`).
* `tableStreamW_eq`: the streamed sum is `σ_a χ_a(y) I^w_a` (`z = 2^b`).
* `tableMachineW = Stepped.sumRange tdNW (Stepped.ofFun termWR)`, `tableMachineW_poly`;
  `tableMachineW_runs`: under `TDescW` with all weights `≤ W` and `μ_a ≤ μ`,
  `Runs d (2 · 8^μ) (2 · size d + 9μ + 2bWμ + 9) (σ_a χ_a I^w_a)`.
* `tableProcW rd = Stepped.mapIn rd tableMachineW`, `tableProcW_poly`, `tableProcW_runs`.
-/
import EthFollowup.ExactHC.TableProc
import EthFollowup.ExactHC.Weighted

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset

/-! ### The weighted data and the weighted term -/

/-- The weighted data: `(d, (b in unary, (weights of the internal edges, weights of the crossing
edges at `a`)))`, all weights in unary and in the order of the lists of `d`. -/
abbrev TDW : Type := TD × (List Unit × (List (List Unit) × List (List Unit)))

/-- The total weight of the internal edges selected by the mask `m`. -/
def wsel (wes : List (List Unit)) (m : ℕ) : ℕ := (selR wes m).flatten.length

/-- The weight of the crossing edges at `a` with low end in `a` and label `≠ N` (`Crossing.wtL`). -/
def wLow (cl : List CE) (wcl : List (List Unit)) : ℕ :=
  (((cl.zip wcl).filter fun p => p.1.1.2 && decide (p.1.2.2.2 ≠ 0)).map fun p => p.2).flatten.length

/-- The exponent of the shift for the mask `m`: `b · (w(x_m) + w_ℓ(a))`. -/
def expW (dw : TDW) (m : ℕ) : ℕ := dw.2.1.length * (wsel dw.2.2.1 m + wLow dw.1.2.2.1.2 dw.2.2.2)

/-- The weighted term number `i`. -/
def termWR (dw : TDW) (i : ℕ) : ℤ :=
  termR dw.1 i * ((2 ^ expW dw (i % 2 ^ dw.1.2.2.1.1.length) : ℕ) : ℤ)

/-- The number of terms (that of the unweighted stream). -/
def tdNW (dw : TDW) : ℕ := tdN dw.1

/-- The weighted streamed value. -/
def tableStreamW (dw : TDW) : ℤ := ∑ i ∈ range (tdNW dw), termWR dw i

/-- The stream regrouped by masks: `Σ_m 2^{e(m)} · Σ_j termMJ d m j`. -/
theorem tableStreamW_eq_sum (dw : TDW) :
    tableStreamW dw = ∑ mm ∈ range (2 ^ dw.1.2.2.1.1.length),
      ((2 ^ expW dw mm : ℕ) : ℤ) *
        ∑ j ∈ range (8 ^ (dw.1.2.2.1.1.length + dw.1.2.2.1.2.length)), termMJ dw.1 mm j := by
  unfold tableStreamW tdNW tdN termWR termR
  rw [sum_range_mul_divmod (2 ^ dw.1.2.2.1.1.length)
    (fun mm j => termMJ dw.1 mm j * ((2 ^ expW dw mm : ℕ) : ℤ))
    (8 ^ (dw.1.2.2.1.1.length + dw.1.2.2.1.2.length)), sum_comm]
  refine sum_congr rfl fun mm _ => ?_
  rw [← sum_mul, mul_comm]

/-! ### Bounds on the exponent -/

theorem sublist_map_snd_zip {α β : Type} : ∀ (l : List α) (l' : List β), ((l.zip l').map Prod.snd).Sublist l'
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: l' => by
    rw [List.zip_cons_cons, List.map_cons]
    exact (sublist_map_snd_zip l l').cons_cons b

theorem length_flatten_le_of_sublist {α : Type} {l l' : List (List α)} (h : l.Sublist l') :
    l.flatten.length ≤ l'.flatten.length := by
  rw [List.length_flatten, List.length_flatten]
  exact (h.map _).sum_le_sum fun _ _ => Nat.zero_le _

theorem wsel_le (wes : List (List Unit)) (m : ℕ) : wsel wes m ≤ wes.flatten.length :=
  length_flatten_le_of_sublist (selR_sublist wes m)

theorem wLow_le (cl : List CE) (wcl : List (List Unit)) : wLow cl wcl ≤ wcl.flatten.length := by
  unfold wLow
  exact length_flatten_le_of_sublist ((List.Sublist.map _ List.filter_sublist).trans
    (sublist_map_snd_zip cl wcl))

/-- The total weight of all edges at the node, times `b`: a bound on every exponent. -/
def etot (dw : TDW) : ℕ := dw.2.1.length * (dw.2.2.1.flatten.length + dw.2.2.2.flatten.length)

theorem expW_le (dw : TDW) (m : ℕ) : expW dw m ≤ etot dw :=
  Nat.mul_le_mul_left _ (Nat.add_le_add (wsel_le _ _) (wLow_le _ _))

theorem termWR_le (dw : TDW) (i : ℕ) : (termWR dw i).natAbs ≤ 2 ^ etot dw := by
  unfold termWR
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  have h1 := termR_le dw.1 i
  have h2 : 2 ^ expW dw (i % 2 ^ dw.1.2.2.1.1.length) ≤ 2 ^ etot dw :=
    Nat.pow_le_pow_right (by norm_num) (expW_le dw _)
  calc (termR dw.1 i).natAbs * 2 ^ expW dw (i % 2 ^ dw.1.2.2.1.1.length)
      ≤ 1 * 2 ^ etot dw := Nat.mul_le_mul h1 h2
    _ = _ := one_mul _

/-! ### What the weighted data must hold -/

noncomputable section

variable {n g m : ℕ}

/-- **What the weighted data must hold**: the fields of `TDesc` (with the internal edges and their
weights listed in the same order), `b` in unary, and the weights of the crossing edges at `a` in
the order of `δ(a)`. -/
structure TDescW (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {β : Fin n → Fin g}
    (X : Crossing G β m) (r : Fin n) (a : Fin g) (ℓ : Fin m → Label) (y : Fin g × Fin g → ZMod 2)
    (w : Sym2 (Fin n) → ℕ) (b : ℕ) (dw : TDW) : Prop where
  r_eq : dw.1.1.1 = r.val
  a_eq : dw.1.1.2 = a.val
  va : ∃ L : List (Fin n), (∀ v, v ∈ L ↔ β v = a) ∧ dw.1.2.1.1 = L.map Fin.val
  vr_eq : dw.1.2.1.2 = (((blob β a).erase r).sort (· ≤ ·)).map Fin.val
  es : ∃ esF : List (Fin n × Fin n), (esF.map symP).Nodup ∧
    (∀ e, e ∈ esF.map symP ↔ e ∈ Crossing.Eint G β a) ∧ dw.1.2.2.1.1 = esF.map valP ∧
    dw.2.2.1 = esF.map fun p => List.replicate (w (symP p)) ()
  cl_eq : dw.1.2.2.1.2 = ((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)
  yl : ∃ ql : List (Fin g × Fin g), ql.Nodup ∧ (∀ p, p ∈ ql ↔ p ∈ Chords.Q a) ∧
    dw.1.2.2.2 = ql.map fun p => ((p.1.val, p.2.val), decide (y p = 1))
  b_eq : dw.2.1.length = b
  wcl_eq : dw.2.2.2 = ((X.chords.delta a).sort (· ≤ ·)).map fun k => List.replicate (w (X.edge k)) ()

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g} {X : Crossing G β m}
  {r : Fin n} {a : Fin g} {ℓ : Fin m → Label} {y : Fin g × Fin g → ZMod 2} {w : Sym2 (Fin n) → ℕ}
  {b : ℕ} {dw : TDW}

theorem TDescW.toTDesc (h : TDescW G X r a ℓ y w b dw) : TDesc G X r a ℓ y dw.1 where
  r_eq := h.r_eq
  a_eq := h.a_eq
  va := h.va
  vr_eq := h.vr_eq
  es := by
    obtain ⟨esF, h1, h2, h3, -⟩ := h.es
    exact ⟨esF, h1, h2, h3⟩
  cl_eq := h.cl_eq
  yl := h.yl

/-! ### The weights read from the data -/

theorem sum_map_filter_eq {α : Type} (p : α → Bool) (f : α → ℕ) :
    ∀ l : List α, ((l.filter p).map f).sum = (l.map fun k => if p k = true then f k else 0).sum
  | [] => rfl
  | k :: l => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← sum_map_filter_eq p f l]
    by_cases h : p k = true
    · rw [if_pos h, if_pos h, List.map_cons, List.sum_cons]
    · rw [if_neg h, if_neg h, zero_add]

/-- `wsel` of the unary weights is `w(x_m)`. -/
theorem wsel_eq (esF : List (Fin n × Fin n)) (hn : (esF.map symP).Nodup) (mm : ℕ) :
    wsel (esF.map fun p => List.replicate (w (symP p)) ()) mm =
      Hamiltonian.wt w (selR (esF.map symP) mm).toFinset := by
  unfold wsel Hamiltonian.wt
  have hnd : ((selR esF mm).map symP).Nodup := by
    rw [← selR_map]; exact (selR_sublist _ _).nodup hn
  rw [selR_map, selR_map, List.sum_toFinset _ hnd, List.length_flatten, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp

/-- `wLow` of the crossing data and the unary weights is `w_ℓ(a)`. -/
theorem wLow_eq (X : Crossing G β m) (ℓ : Fin m → Label) (a : Fin g) :
    wLow (((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a))
      (((X.chords.delta a).sort (· ≤ ·)).map fun k => List.replicate (w (X.edge k)) ()) =
      X.wtL w ℓ a := by
  unfold wLow Crossing.wtL
  rw [List.zip_map', List.filter_map, List.map_map, List.length_flatten, List.map_map,
    sum_filter, sum_sort, sum_map_filter_eq]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  have e : ((fun p : CE × List Unit => p.1.1.2 && decide (p.1.2.2.2 ≠ 0)) ∘
      fun k => (ceOf X ℓ a k, List.replicate (w (X.edge k)) ())) k = true ↔
      β (X.s k) = a ∧ ℓ k ≠ Label.N := by
    simp only [Function.comp_apply, ceOf, Bool.and_eq_true, decide_eq_true_eq, ne_eq, code_eq_zero]
  by_cases h : β (X.s k) = a ∧ ℓ k ≠ Label.N
  · rw [if_pos (e.2 h), if_pos h]; simp
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h]

/-! ### The streamed value is the weighted node table -/

section Main

variable (G) (X)

/-- **`tableStreamW` computes the weighted node table** `σ_a(ℓ) · χ_a(ℓ, y) · I^w_a(ℓ)` at `z = 2^b`. -/
theorem tableStreamW_eq (r : Fin n) (a : Fin g) (ℓ : Fin m → Label) (y : Fin g × Fin g → ZMod 2)
    (w : Sym2 (Fin n) → ℕ) (b : ℕ) (dw : TDW) (hD : TDescW G X r a ℓ y w b dw) :
    tableStreamW dw =
      X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * X.Iw r (2 ^ b) w ℓ a := by
  obtain ⟨⟨⟨rr, aa⟩, ⟨va, vr⟩, ⟨es, cl⟩, yl⟩, ⟨bu, wes, wcl⟩⟩ := dw
  obtain ⟨hr, ha, ⟨L, hL, hva⟩, hvr, ⟨esF, hn, hE, hes, hwes⟩, hcl, ⟨ql, hqn, hq, hyl⟩, hb, hwcl⟩ := hD
  simp only at hr ha hva hvr hes hwes hcl hyl hb hwcl
  subst hr ha hva hvr hes hwes hcl hyl hwcl hb
  set S := blob β a
  set cl0 := ((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)
  set wcl0 := ((X.chords.delta a).sort (· ≤ ·)).map fun k => List.replicate (w (X.edge k)) ()
  set wes0 := esF.map fun p => List.replicate (w (symP p)) ()
  set A := genSet r S
  set Ω := OmegaSet r S
  have hAl : ∀ γ ∈ genL ((((S.erase r).sort (· ≤ ·))).map Fin.val), γ < 2 * n := genL_lt _
  have hfA : finOf n (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val)) = A := finOf_genL r S
  -- the coefficient of `Ω` is streamed
  have hOm : finalC (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val))
      ((omL ((((S.erase r).sort (· ≤ ·))).map Fin.val)).foldl (stepL r.val) (some (1, []))) =
      Ω.coeff A := by
    have hw : ∀ x ∈ omL ((((S.erase r).sort (· ≤ ·))).map Fin.val), x.2 < n := by
      intro x hx
      simp only [omL, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨_, ⟨v, -, rfl⟩, h⟩ := hx
      rcases h with rfl | rfl <;> exact v.2
    obtain ⟨h1, h2⟩ := foldL_sem r _ hw _ (sInv_some_nil (n := n) 1)
    rw [finalC_eq hAl h2, h1, prod_omL, hfA]
    simp only [sem, Option.elim, one_smul]
    rw [show finOf n [] = ∅ by ext; simp, Grass.e_empty, one_mul]
    rfl
  -- the choices for a fixed mask
  have hlen : ∀ mm, (intR (esF.map valP) mm ++ cl0.map pieceAlts).length = esF.length + cl0.length := by
    intro mm; simp [intR, length_digR]
  have hfs : ∀ mm, ∀ f ∈ intR (esF.map valP) mm ++ cl0.map pieceAlts, AltOK n f ∧ f.length ≤ 8 := by
    intro mm f hf
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨e, he, dd, rfl⟩ := mem_digR 2 _ _ _ f hf
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
      split_ifs
      · exact ⟨altOK_qAlts p.1.2 p.2.2, by simp [qAlts]⟩
      · exact ⟨altOK_oneAlts, by simp [oneAlts]⟩
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hf
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hu
      refine ⟨altOK_pieceAlts G X ℓ a k, ?_⟩
      unfold pieceAlts aAlts bAlts
      split_ifs <;> simp
  have hchoice : ∀ mm, ∑ j ∈ range (8 ^ (esF.length + cl0.length)),
      valC r.val (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val))
        (digR 8 (pick r.val) (intR (esF.map valP) mm ++ cl0.map pieceAlts) j) =
      (edgeProd r (selR (esF.map symP) mm).toFinset * X.Gam r ℓ a).coeff A := by
    intro mm
    have hv : ∀ j, valC r.val (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val))
        (digR 8 (pick r.val) (intR (esF.map valP) mm ++ cl0.map pieceAlts) j) =
        (((digR 8 (pick r.val) (intR (esF.map valP) mm ++ cl0.map pieceAlts) j).map
          (altVal r)).prod).coeff A := by
      intro j
      rw [valC_eq r hAl _ ?_, hfA]
      intro c hc
      obtain ⟨f, hf, dd, rfl⟩ := mem_digR 8 _ _ _ c hc
      exact altOK_pick (hfs mm f hf).1 r.2 dd
    simp only [hv, ← Grass.coeff_sum]
    rw [← hlen mm, sum_choices r _ fun f hf => (hfs mm f hf).2, List.map_append, List.prod_append,
      prod_intR r esF hn mm, prod_pieces]
  -- the degree test
  have hdeg : ∀ mm, DC (L.map Fin.val) cl0 (selR (esF.map valP) mm) =
      X.degInd ℓ a (selR (esF.map symP) mm).toFinset := by
    intro mm
    unfold DC Crossing.degInd
    congr 1
    simp only [List.all_eq_true, List.mem_map, decide_eq_true_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, mem_blob]
    refine propext ⟨fun h v hv => ?_, fun h v hv => ?_⟩
    · rw [deg_eqC esF hn, degL_eqC]; exact h v ((hL v).2 hv)
    · rw [← deg_eqC esF hn, ← degL_eqC]; exact h v ((hL v).1 hv)
  -- the weights
  have hws : ∀ mm, wsel wes0 mm = Hamiltonian.wt w (selR (esF.map symP) mm).toFinset :=
    fun mm => wsel_eq esF hn mm
  have hwl : wLow cl0 wcl0 = X.wtL w ℓ a := wLow_eq X ℓ a
  -- assemble
  have hEint : (esF.map symP).toFinset = Crossing.Eint G β a := by
    ext e; simp only [List.mem_toFinset, hE]
  rw [tableStreamW_eq_sum]
  simp only [List.length_map, expW]
  unfold termMJ
  simp only
  have hs : sigmaC a.val cl0 = X.chords.sigma (labelPar ℓ) a := (sigma_eqC X ℓ a).symm
  have hc : chiC a.val cl0 (ql.map fun p => ((p.1.val, p.2.val), decide (y p = 1))) =
      X.chords.chi (labelPar ℓ) a y := (chi_eqC X ℓ a y ql hqn hq).symm
  simp only [hs, hc, hOm, hdeg, hws, hwl]
  simp only [← sum_mul, ← mul_sum, hchoice]
  rw [show esF.length = (esF.map symP).length by simp,
    sum_masks (esF.map symP) hn (fun x => ((2 ^ (bu.length * (Hamiltonian.wt w x + X.wtL w ℓ a)) : ℕ) : ℤ) *
      (X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * X.degInd ℓ a x *
        (edgeProd r x * X.Gam r ℓ a).coeff A * Ω.coeff A)),
    hEint, Crossing.Iw]
  simp only [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp only [Grass.topCoeff]
  push_cast
  rw [pow_mul, pow_add]
  ring

end Main

end

/-! ## The machine -/

section Poly

open Groundwork

variable {γ : Type} [Enc γ]

theorem selR_polyT' {es : γ → List (List Unit)} {mm : γ → ℕ} (he : PolyT es) (hm : PolyT mm) :
    PolyT fun x => selR (es x) (mm x) := by
  unfold selR
  exact PolyT.flatten (digR_polyT 2 (H := fun _ e d => if d = 1 then [e] else []) (by fun_prop) he hm)

theorem wsel_unary {es : γ → List (List Unit)} {mm : γ → ℕ} (he : PolyT es) (hm : PolyT mm) :
    Unary fun x => wsel (es x) (mm x) := by
  unfold wsel
  exact Unary.of_length (PolyT.flatten (selR_polyT' he hm))

theorem wLow_unary {cl : γ → List CE} {wcl : γ → List (List Unit)} (hc : PolyT cl) (hw : PolyT wcl) :
    Unary fun x => wLow (cl x) (wcl x) := by
  unfold wLow
  refine Unary.of_length (PolyT.flatten ?_)
  fun_prop

theorem expW_unary {dw : γ → TDW} {mm : γ → ℕ} (hd : PolyT dw) (hm : PolyT mm) :
    Unary fun x => expW (dw x) (mm x) := by
  unfold expW
  exact Unary.mul (Unary.of_length (by fun_prop))
    (Unary.add (wsel_unary (by fun_prop) hm) (wLow_unary (by fun_prop) (by fun_prop)))

theorem termWR_polyT : PolyT fun p : TDW × ℕ => termWR p.1 p.2 := by
  unfold termWR
  have h1 : PolyT fun p : TDW × ℕ => termR p.1.1 p.2 :=
    PolyT.comp termR_polyT (g := fun p : TDW × ℕ => (p.1.1, p.2)) (by fun_prop)
  have h2 : PolyT fun p : TDW × ℕ => 2 ^ p.1.1.2.2.1.1.length :=
    PolyT.two_pow (Unary.of_length (by fun_prop))
  have h3 : PolyT fun p : TDW × ℕ => p.2 % 2 ^ p.1.1.2.2.1.1.length := PolyT.mod (by fun_prop) h2
  have h4 : PolyT fun p : TDW × ℕ => 2 ^ expW p.1 (p.2 % 2 ^ p.1.1.2.2.1.1.length) :=
    PolyT.two_pow (expW_unary (by fun_prop) h3)
  exact PolyT.mulZ h1 (PolyT.natCast h4)

theorem tdNW_polyT : PolyT tdNW := by
  unfold tdNW
  exact PolyT.comp tdN_polyT (g := fun dw : TDW => dw.1) (by fun_prop)

end Poly

section Machine

open Groundwork

/-- **The weighted node-table machine**: one weighted term per step. -/
def tableMachineW : Stepped TDW ℤ :=
  Stepped.sumRange tdNW (Stepped.ofFun fun p : TDW × ℕ => termWR p.1 p.2)

theorem tableMachineW_poly : Nonempty (IsPolyT tableMachineW) := by
  have : IsPolyT (Stepped.ofFun fun p : TDW × ℕ => termWR p.1 p.2) := IsPolyT.ofFun termWR_polyT
  exact ⟨IsPolyT.sumRange tdNW_polyT⟩

/-- **Steps and states of the machine** (for any data): `2 · tdNW d` steps, states of size
`2 · size d + 3 · size (tdNW d) + 2 · etot d + 3`, result `tableStreamW d`. -/
theorem tableMachineW_runs' (dw : TDW) :
    tableMachineW.Runs dw (2 * tdNW dw) (2 * size dw + 3 * size (tdNW dw) + 2 * etot dw + 3)
      (tableStreamW dw) := by
  have hM : ∀ y < tdNW dw, (Stepped.ofFun fun p : TDW × ℕ => termWR p.1 p.2).Runs (dw, y) 1
      (size dw + size (tdNW dw) + etot dw + 2) (termWR dw y) := by
    intro y hy
    refine (Stepped.ofFun_runs (fun p : TDW × ℕ => termWR p.1 p.2) (dw, y)).mono le_rfl ?_
    have h1 : Nat.size y ≤ Nat.size (tdNW dw) := Nat.size_le_size hy.le
    have h2 : Nat.size (termWR dw y).natAbs ≤ etot dw + 1 := by
      refine Nat.size_le.2 ((termWR_le dw y).trans_lt ?_)
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    simp only [size_prod, size_nat, size_int]
    omega
  have h := Stepped.sumRange_runs (N := tdNW) (a := dw) (fun _ => 1) (fun y => termWR dw y)
    (2 ^ etot dw) _ hM (fun y _ => termWR_le dw y)
  refine h.mono ?_ ?_
  · simp [sum_const, card_range]; omega
  · have h3 : Nat.size (tdNW dw * 2 ^ etot dw) ≤ Nat.size (tdNW dw) + etot dw := by
      refine Nat.size_le.2 ?_
      rw [pow_add]
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity)
    simp only [size_nat] at h3 ⊢
    omega

end Machine

section Spec

open Groundwork

variable {n g m : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {β : Fin n → Fin g} (X : Crossing G β m)

/-- Under `TDescW` with all weights `≤ W`: `etot d ≤ b · W · μ_a`-ish, precisely
`etot d ≤ b · W · (|E_int(a)| + |δ(a)|)`. -/
theorem etot_le {r : Fin n} {a : Fin g} {ℓ : Fin m → Label} {y : Fin g × Fin g → ZMod 2}
    {w : Sym2 (Fin n) → ℕ} {b : ℕ} {dw : TDW} (hD : TDescW G X r a ℓ y w b dw) {W : ℕ}
    (hw : ∀ e, w e ≤ W) :
    etot dw ≤ b * (W * ((Crossing.Eint G β a).card + (X.chords.delta a).card)) := by
  obtain ⟨esF, hn, hE, hes, hwes⟩ := hD.es
  have hp : esF.length = (Crossing.Eint G β a).card := by
    have : (esF.map symP).toFinset = Crossing.Eint G β a := by ext e; simp only [List.mem_toFinset, hE]
    rw [← this, List.toFinset_card_of_nodup hn]; simp
  have h1 : dw.2.2.1.flatten.length ≤ (Crossing.Eint G β a).card * W := by
    rw [hwes, List.length_flatten, List.map_map, ← hp]
    have := List.sum_le_card_nsmul (esF.map ((fun l : List Unit => l.length) ∘
      fun p => List.replicate (w (symP p)) ())) W (by
        intro x hx
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
        simp only [Function.comp_apply, List.length_replicate]
        exact hw _)
    simpa using this
  have h2 : dw.2.2.2.flatten.length ≤ (X.chords.delta a).card * W := by
    rw [hD.wcl_eq, List.length_flatten, List.map_map]
    have := List.sum_le_card_nsmul ((((X.chords.delta a).sort (· ≤ ·))).map
      ((fun l : List Unit => l.length) ∘ fun k => List.replicate (w (X.edge k)) ())) W (by
        intro x hx
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
        simp only [Function.comp_apply, List.length_replicate]
        exact hw _)
    simpa using this
  unfold etot
  rw [hD.b_eq]
  refine Nat.mul_le_mul_left b ?_
  rw [mul_add]
  have := Nat.add_le_add h1 h2
  rw [mul_comm (Crossing.Eint G β a).card, mul_comm (X.chords.delta a).card] at this
  exact this

/-- **The weighted node-table machine computes `σ_a(ℓ) χ_a(ℓ, y) I^w_a(ℓ)`** (`z = 2^b`) within
`2 · 2^{4|E_int(a)| + 3|δ(a)|} ≤ 2 · 8^{μ_a}` steps on states of size
`2 · size d + 12|E_int(a)| + 9|δ(a)| + 2bW(|E_int(a)| + |δ(a)|) + 9`. -/
theorem tableMachineW_runs (r : Fin n) (a : Fin g) (ℓ : Fin m → Label) (y : Fin g × Fin g → ZMod 2)
    (w : Sym2 (Fin n) → ℕ) (b : ℕ) (dw : TDW) (hD : TDescW G X r a ℓ y w b dw) {W : ℕ}
    (hw : ∀ e, w e ≤ W) :
    tableMachineW.Runs dw (2 * 2 ^ (4 * (Crossing.Eint G β a).card + 3 * (X.chords.delta a).card))
      (2 * size dw + 12 * (Crossing.Eint G β a).card + 9 * (X.chords.delta a).card +
        2 * (b * (W * ((Crossing.Eint G β a).card + (X.chords.delta a).card))) + 9)
      (X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * X.Iw r (2 ^ b) w ℓ a) := by
  have h := tableMachineW_runs' dw
  rw [tableStreamW_eq G X r a ℓ y w b dw hD] at h
  have hN : tdNW dw = 2 ^ (4 * (Crossing.Eint G β a).card + 3 * (X.chords.delta a).card) :=
    tdN_eq G X hD.toTDesc
  rw [hN] at h
  refine h.mono le_rfl ?_
  have he := etot_le G X hD hw
  rw [size_nat, Nat.size_pow]
  omega

/-- The weighted T-procedure: read the data with `rd`, then run the weighted node-table machine. -/
def tableProcW {Q : Type} (rd : Q → TDW) : Stepped Q ℤ := Stepped.mapIn rd tableMachineW

theorem tableProcW_poly {Q : Type} [Enc Q] {rd : Q → TDW} (hrd : PolyT rd) :
    Nonempty (IsPolyT (tableProcW rd)) := by
  obtain ⟨i⟩ := tableMachineW_poly
  exact ⟨IsPolyT.mapIn hrd⟩

theorem tableProcW_runs {Q : Type} (rd : Q → TDW) (q : Q) (r : Fin n) (a : Fin g) (ℓ : Fin m → Label)
    (y : Fin g × Fin g → ZMod 2) (w : Sym2 (Fin n) → ℕ) (b : ℕ) (hD : TDescW G X r a ℓ y w b (rd q))
    {W : ℕ} (hw : ∀ e, w e ≤ W) :
    (tableProcW rd).Runs q (2 * 2 ^ (4 * (Crossing.Eint G β a).card + 3 * (X.chords.delta a).card))
      (2 * size (rd q) + 12 * (Crossing.Eint G β a).card + 9 * (X.chords.delta a).card +
        2 * (b * (W * ((Crossing.Eint G β a).card + (X.chords.delta a).card))) + 9)
      (X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * X.Iw r (2 ^ b) w ℓ a) :=
  Stepped.mapIn_runs (tableMachineW_runs G X r a ℓ y w b (rd q) hD hw)

end Spec

end EthFollowup.ExactHC
