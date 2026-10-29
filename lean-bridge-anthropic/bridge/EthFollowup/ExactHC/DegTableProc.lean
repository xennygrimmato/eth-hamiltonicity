/-
# The degree-pruned node-table procedure (workstream A, file 5)

The node table `σ_a(ℓ) · χ_a(ℓ, y) · I_a(ℓ)` of the blob network (`Blobs.lean`) computed by a step
machine whose number of steps is `≤ 3 · D^{2ν_a} · 5^{ν_a}` when every vertex of the blob has degree
`≤ D` (`D ≥ 2`), `ν_a = |V_a|`, with states of polynomial size. This is enumeration (D) of
Prop. 3.2(iii) of `research/hc-degree-theorem.md`, in the following form.

* **Owners.** Every internal edge `e = (u, w)` of the data (`TD`, as read by `TableProc.lean`) is owned
  by its first end `u`. The owners are `r :: (V_a \ {r})` (a duplicate-free list covering `V_a`), and the
  group of `v` is the list of internal edges owned by `v` (at most `deg v ≤ D` of them).
* **Outer enumeration.** A subset `x ⊆ E_int(a)` with `deg_x(v) ≤ 2` for all `v` has at most two edges
  in every group, so it is the union of one sublist of size `≤ 2` per group (`sm2`): mixed-radix
  digits (`mixR`) with radix `radS g = 1 + |g| + C(|g|, 2) ≤ D²` per group. Subsets with three edges in
  one group are not visited; they have degree `> 2` at the owner, so their term is `0`
  (`sum_mixR_union`).
* **Inner enumeration.** For a visited `x` that passes the degree test, one signed monomial is chosen
  from each factor `1 + q_e` (`e ∈ x`, 5 alternatives) and each piece (1 or 2 alternatives): mixed
  radix by the factor lengths (`sum_mixR_prod`). The number of choices is `5^{|x|} · 2^{s_a}`, and the
  degree test gives `2|x| + s_a = 2ν_a`, so it is `≤ 5^{ν_a}`. If the test fails the inner loop is
  empty.

Main results (the data `d : TD` and its description `TDesc` are those of `TableProc.lean`, so the
procedure plugs into every network whose reader decodes the local labels into `TDesc` data):

* **`tableStreamD_eq`**: `tableStreamD d = σ_a(ℓ) χ_a(ℓ, y) I_a(ℓ)` under `TDesc`;
* `tableMachineD = sumRange rD (sumRange nID (ofFun termD))`, `tableMachineD_poly`;
* **`tableMachineD_runs`**: under `TDesc`, `2 ≤ D` and `deg v ≤ D` on `V_a`,
  `Runs d (3 · D^{2ν_a} · 5^{ν_a}) (3 · size d + 8 · ν_a · (Nat.size D + 2) + 20) (σ_a χ_a I_a)`
  (`rD_le : rD d ≤ D^{2ν_a}` outer terms, `nID_le : nID d i ≤ 5^{ν_a}` inner terms each);
* `tableProcD rd = Stepped.mapIn rd tableMachineD`, `tableProcD_poly`, `tableProcD_runs`.
-/
import EthFollowup.ExactHC.TableProc

set_option autoImplicit true

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset

/-! ### Sublists with at most two elements -/

/-- The pairs `[e, e']` of elements of `l`, `e` before `e'`. -/
def prs {β : Type} : List β → List (List β)
  | [] => []
  | e :: l => l.map (fun e' => [e, e']) ++ prs l

/-- The sublists of `l` with at most two elements: `[]`, the singletons, the pairs. -/
def sm2 {β : Type} (l : List β) : List (List β) := [] :: (l.map (fun e => [e]) ++ prs l)

/-- Their number `1 + |l| + C(|l|, 2)`, the radix of a group. -/
def radS {β : Type} (l : List β) : ℕ := (sm2 l).length

/-- The choice number `c` among them (`[]` beyond the end). -/
def chS {β : Type} (l : List β) (c : ℕ) : List β := (sm2 l).getD c []

theorem length_prs {β : Type} : ∀ l : List β, 2 * (prs l).length + l.length = l.length ^ 2
  | [] => rfl
  | e :: l => by
    have ih := length_prs l
    simp only [prs, List.length_append, List.length_map, List.length_cons]
    nlinarith

theorem two_mul_radS {β : Type} (l : List β) : 2 * radS l = l.length ^ 2 + l.length + 2 := by
  have h := length_prs l
  simp only [radS, sm2, List.length_cons, List.length_append, List.length_map]
  omega

theorem radS_nil {β : Type} : radS ([] : List β) = 1 := rfl

/-- `1 + f + C(f, 2) ≤ D²` for `f ≤ D`, `2 ≤ D`. -/
theorem radS_le {β : Type} {l : List β} {D : ℕ} (hD : 2 ≤ D) (hl : l.length ≤ D) : radS l ≤ D ^ 2 := by
  have h := two_mul_radS l
  have h1 : l.length ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left hl 2
  nlinarith

theorem prs_map {β γ : Type} (φ : β → γ) : ∀ l : List β, prs (l.map φ) = (prs l).map (List.map φ)
  | [] => rfl
  | e :: l => by simp [prs, prs_map φ l]

theorem sm2_map {β γ : Type} (φ : β → γ) (l : List β) : sm2 (l.map φ) = (sm2 l).map (List.map φ) := by
  simp [sm2, prs_map]

theorem radS_map {β γ : Type} (φ : β → γ) (l : List β) : radS (l.map φ) = radS l := by
  simp [radS, sm2_map]

theorem chS_map {β γ : Type} (φ : β → γ) (l : List β) (c : ℕ) : chS (l.map φ) c = (chS l c).map φ := by
  unfold chS
  rw [sm2_map, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases (sm2 l)[c]? with _ | x <;> rfl

theorem sublist_of_mem_prs {β : Type} : ∀ {l : List β} {c : List β}, c ∈ prs l → c.Sublist l
  | [], _, h => absurd h (by simp [prs])
  | e :: l, c, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨e', he', rfl⟩ := List.mem_map.1 h
      exact (List.singleton_sublist.2 he').cons_cons e
    · exact (sublist_of_mem_prs h).cons e

theorem sublist_of_mem_sm2 {β : Type} {l c : List β} (h : c ∈ sm2 l) : c.Sublist l := by
  rcases List.mem_cons.1 h with rfl | h
  · exact List.nil_sublist _
  rcases List.mem_append.1 h with h | h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact List.singleton_sublist.2 he
  · exact sublist_of_mem_prs h

theorem chS_sublist {β : Type} (l : List β) (c : ℕ) : (chS l c).Sublist l := by
  unfold chS
  rw [List.getD_eq_getElem?_getD]
  rcases h : (sm2 l)[c]? with _ | x
  · exact List.nil_sublist _
  · exact sublist_of_mem_sm2 (List.mem_of_getElem? h)

section Sums

variable {β : Type} [DecidableEq β] {M : Type*} [AddCommMonoid M]

theorem sum_le1 (s : Finset β) (G : Finset β → M) :
    ∑ z ∈ s.powerset, (if z.card ≤ 1 then G z else 0) = G ∅ + ∑ e ∈ s, G {e} := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_powerset_insert ha, ih, sum_insert ha]
    have e : ∑ z ∈ s.powerset, (if (insert a z).card ≤ 1 then G (insert a z) else 0) = G {a} := by
      have h1 : ∀ z ∈ s.powerset, (if (insert a z).card ≤ 1 then G (insert a z) else 0) =
          if z = ∅ then G {a} else 0 := by
        intro z hz
        have haz : a ∉ z := fun h => ha (mem_powerset.1 hz h)
        rw [card_insert_of_notMem haz]
        by_cases h0 : z = ∅
        · subst h0; simp
        · rw [if_neg h0, if_neg]
          have := card_pos.2 (nonempty_iff_ne_empty.2 h0)
          omega
      rw [sum_congr rfl h1, sum_ite_eq' _ _ (fun _ => G {a}), if_pos (empty_mem_powerset s)]
    rw [e]
    abel

/-- **The sublists of size `≤ 2` enumerate the subsets of size `≤ 2`.** -/
theorem sum_sm2 : ∀ (l : List β), l.Nodup → ∀ H : Finset β → M,
    ((sm2 l).map fun c => H c.toFinset).sum = ∑ z ∈ l.toFinset.powerset, if z.card ≤ 2 then H z else 0
  | [], _, H => by simp [sm2, prs]
  | e :: l, hn, H => by
    have hl := List.nodup_cons.1 hn
    have he : e ∉ l.toFinset := by rw [List.mem_toFinset]; exact hl.1
    have ih := sum_sm2 l hl.2 H
    have e1 : ((sm2 (e :: l)).map fun c => H c.toFinset).sum =
        ((sm2 l).map fun c => H c.toFinset).sum + (H {e} + (l.map fun e' => H (insert e {e'})).sum) := by
      simp only [sm2, prs, List.map_cons, List.map_append, List.map_map, List.sum_cons, List.sum_append,
        Function.comp_def, List.toFinset_cons, List.toFinset_nil, insert_empty]
      abel
    rw [e1, ih, List.toFinset_cons, sum_powerset_insert he]
    congr 1
    have h2 : ∀ z ∈ l.toFinset.powerset, (if (insert e z).card ≤ 2 then H (insert e z) else 0) =
        if z.card ≤ 1 then H (insert e z) else 0 := by
      intro z hz
      have hez : e ∉ z := fun h => he (mem_powerset.1 hz h)
      rw [card_insert_of_notMem hez]
      by_cases h : z.card ≤ 1
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    rw [sum_congr rfl h2, sum_le1 l.toFinset (fun z => H (insert e z)), List.sum_toFinset _ hl.2]
    simp

theorem sum_range_getD {γ : Type} (dflt : γ) (F : γ → M) :
    ∀ L : List γ, ∑ d ∈ range L.length, F (L.getD d dflt) = (L.map F).sum
  | [] => by simp
  | c :: L => by
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, sum_range_getD dflt F L]

/-- Subsets of a disjoint union. -/
theorem sum_powerset_union (A B : Finset β) (h : Disjoint A B) (K : Finset β → M) :
    ∑ x ∈ (A ∪ B).powerset, K x = ∑ z ∈ A.powerset, ∑ y ∈ B.powerset, K (z ∪ y) := by
  induction A using Finset.induction_on generalizing K with
  | empty => simp
  | @insert a A ha ih =>
    have haB : a ∉ B := disjoint_left.1 h (mem_insert_self a A)
    have hA : Disjoint A B := disjoint_of_subset_left (subset_insert a A) h
    rw [insert_union, sum_powerset_insert (fun h' => (mem_union.1 h').elim ha haB), sum_powerset_insert ha,
      ih hA K, ih hA (fun x => K (insert a x))]
    simp only [insert_union]

end Sums

/-! ### Mixed radix -/

/-- Digit-wise map in mixed radix: the element number `k` of `l` is mapped with the digit number `k`
of `m`, the digit of the element `e` having radix `rad e`. -/
def mixR {α β : Type} (rad : α → ℕ) (H : α → ℕ → β) : List α → ℕ → List β
  | [], _ => []
  | e :: l, m => H e (m % rad e) :: mixR rad H l (m / rad e)

theorem length_mixR {α β : Type} (rad : α → ℕ) (H : α → ℕ → β) :
    ∀ (l : List α) (m : ℕ), (mixR rad H l m).length = l.length
  | [], _ => rfl
  | e :: l, m => by simp only [mixR, List.length_cons, length_mixR rad H l]

theorem mem_mixR {α β : Type} (rad : α → ℕ) (H : α → ℕ → β) :
    ∀ (l : List α) (m : ℕ) (c : β), c ∈ mixR rad H l m → ∃ e ∈ l, ∃ d, c = H e d
  | [], _, _, h => absurd h (by simp [mixR])
  | e :: l, m, c, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨e, List.mem_cons_self, _, rfl⟩
    · obtain ⟨e', he', d, rfl⟩ := mem_mixR rad H l _ c h
      exact ⟨e', List.mem_cons_of_mem _ he', d, rfl⟩

/-- **The sum over all mixed-radix choices of a product is the product of the sums.** -/
theorem sum_mixR_prod {α β : Type} {R : Type*} [Semiring R] (rad : α → ℕ) (H : α → ℕ → β) (φ : β → R) :
    ∀ l : List α, ∑ j ∈ range ((l.map rad).prod), ((mixR rad H l j).map φ).prod =
      (l.map fun e => ∑ d ∈ range (rad e), φ (H e d)).prod
  | [] => by simp [mixR]
  | e :: l => by
    simp only [mixR, List.map_cons, List.prod_cons]
    rw [sum_range_mul_divmod (rad e) (fun d j => φ (H e d) * ((mixR rad H l j).map φ).prod), sum_comm,
      ← sum_mul_sum, sum_mixR_prod rad H φ l]

/-- The selected sublists, one per group, put together. -/
def selG {β : Type} (gs : List (List β)) (m : ℕ) : List β := (mixR radS chS gs m).flatten

theorem selG_map {β γ : Type} (φ : β → γ) :
    ∀ (gs : List (List β)) (m : ℕ), selG (gs.map (List.map φ)) m = (selG gs m).map φ
  | [], _ => rfl
  | g :: gs, m => by
    have ih := selG_map φ gs (m / radS g)
    simp only [selG, List.map_cons, mixR, List.flatten_cons, radS_map, chS_map, List.map_append] at ih ⊢
    rw [ih]

theorem selG_sublist {β : Type} : ∀ (gs : List (List β)) (m : ℕ), (selG gs m).Sublist gs.flatten
  | [], _ => List.Sublist.slnil
  | g :: gs, m => by
    simp only [selG, mixR, List.flatten_cons]
    exact (chS_sublist g _).append (selG_sublist gs _)

/-- **The degree-pruned enumeration.** Choosing at most two elements from every group enumerates all
subsets of the union of the groups, if `K` vanishes on subsets with more than two elements in some
group. -/
theorem sum_selG {β : Type} [DecidableEq β] {M : Type*} [AddCommMonoid M] :
    ∀ (gs : List (List β)), gs.flatten.Nodup → ∀ K : Finset β → M,
      (∀ x ⊆ gs.flatten.toFinset, (∃ g ∈ gs, 2 < (x ∩ g.toFinset).card) → K x = 0) →
      ∑ m ∈ range ((gs.map radS).prod), K (selG gs m).toFinset = ∑ x ∈ gs.flatten.toFinset.powerset, K x
  | [], _, K, _ => by simp [selG, mixR]
  | g :: gs, hn, K, hK => by
    rw [List.flatten_cons] at hn
    obtain ⟨hg, hgs, hdis⟩ := List.nodup_append.1 hn
    have hD : Disjoint g.toFinset gs.flatten.toFinset := by
      rw [disjoint_left]
      intro e h1 h2
      exact hdis e (List.mem_toFinset.1 h1) e (List.mem_toFinset.1 h2) rfl
    have hsub : ∀ d, (chS g d).toFinset ⊆ g.toFinset := fun d e he =>
      List.mem_toFinset.2 ((chS_sublist g d).subset (List.mem_toFinset.1 he))
    have hfl : (g :: gs).flatten.toFinset = g.toFinset ∪ gs.flatten.toFinset := by
      rw [List.flatten_cons, List.toFinset_append]
    -- the inner sums, by induction
    have hin : ∀ z ⊆ g.toFinset, ∑ j ∈ range ((gs.map radS).prod), K (z ∪ (selG gs j).toFinset) =
        ∑ y ∈ gs.flatten.toFinset.powerset, K (z ∪ y) := by
      intro z hz
      refine sum_selG gs hgs (fun y => K (z ∪ y)) fun x hx ⟨g', hg', hc⟩ => hK _ ?_ ⟨g', List.mem_cons_of_mem _ hg', ?_⟩
      · rw [hfl]; exact union_subset_union hz hx
      · exact lt_of_lt_of_le hc (card_le_card (inter_subset_inter_right subset_union_right))
    -- the terms with more than two elements in `g` vanish
    have hvan : ∀ z ⊆ g.toFinset, 2 < z.card → ∑ y ∈ gs.flatten.toFinset.powerset, K (z ∪ y) = 0 := by
      intro z hz hc
      refine sum_eq_zero fun y hy => hK _ ?_ ⟨g, List.mem_cons_self, ?_⟩
      · rw [hfl]; exact union_subset_union hz (mem_powerset.1 hy)
      · refine lt_of_lt_of_le hc (card_le_card ?_)
        intro e he
        exact mem_inter.2 ⟨mem_union_left _ he, hz he⟩
    simp only [selG, List.map_cons, List.prod_cons, mixR, List.flatten_cons, List.toFinset_append]
    simp only [selG] at hin
    rw [sum_range_mul_divmod (radS g) (fun d j => K ((chS g d).toFinset ∪ (mixR radS chS gs j).flatten.toFinset)),
      sum_comm]
    rw [sum_congr rfl fun d _ => hin _ (hsub d)]
    unfold chS radS
    rw [sum_range_getD [] (fun c => ∑ y ∈ gs.flatten.toFinset.powerset, K (c.toFinset ∪ y)) (sm2 g),
      sum_sm2 g hg (fun z => ∑ y ∈ gs.flatten.toFinset.powerset, K (z ∪ y)), sum_powerset_union _ _ hD]
    refine sum_congr rfl fun z hz => ?_
    split_ifs with h
    · rfl
    · exact (hvan z (mem_powerset.1 hz) (by omega)).symm

/-! ### The degree-pruned streamed table -/

/-- The owners `r :: (V_a \ {r})`. -/
def ownD (d : TD) : List ℕ := d.1.1 :: d.2.1.2

/-- The groups: the internal edges owned by (whose first end is) each owner. -/
def grpD (d : TD) : List (List (ℕ × ℕ)) := (ownD d).map fun v => d.2.2.1.1.filter fun e => e.1 = v

/-- The number of outer terms `Π_g radS g`. -/
def rD (d : TD) : ℕ := ((grpD d).map radS).prod

/-- The internal edges selected by the outer index `i`. -/
def selD (d : TD) (i : ℕ) : List (ℕ × ℕ) := selG (grpD d) i

/-- The factors for the outer index `i`: `1 + q_e` for the selected edges, then the pieces. -/
def facD (d : TD) (i : ℕ) : List (List Alt) := (selD d i).map qAlts ++ d.2.2.1.2.map pieceAlts

/-- The degree test `Π_{v ∈ V_a} [deg_x(v) + deg_ℓ(v) = 2]` for the selected edges. -/
def okD (d : TD) (i : ℕ) : Bool :=
  d.2.1.1.all fun v => decide ((selD d i).countP (fun e => decide (e.1 = v ∨ e.2 = v)) + degC d.2.2.1.2 v = 2)

/-- The number of inner terms: the monomial choices if the degree test passes, else `0`. -/
def nID (d : TD) (i : ℕ) : ℕ := if okD d i then ((facD d i).map List.length).prod else 0

/-- The inner term `j` (a choice of one alternative per factor) for the outer index `i`. -/
def termD (d : TD) (i j : ℕ) : ℤ :=
  sigmaC d.1.2 d.2.2.1.2 * chiC d.1.2 d.2.2.1.2 d.2.2.2 *
    valC d.1.1 (genL d.2.1.2) (mixR List.length (pick d.1.1) (facD d i) j) *
    finalC (genL d.2.1.2) ((omL d.2.1.2).foldl (stepL d.1.1) (some (1, [])))

/-- **`tableStreamD`**: the degree-pruned streamed value. -/
def tableStreamD (d : TD) : ℤ := ∑ i ∈ range (rD d), ∑ j ∈ range (nID d i), termD d i j

theorem DC_selD (d : TD) (i : ℕ) : DC d.2.1.1 d.2.2.1.2 (selD d i) = if okD d i then 1 else 0 := rfl

noncomputable section

variable {n g m : ℕ}

/-- `F_a(x)` for `x` given as a duplicate-free list of edges. -/
theorem prod_qL (r : Fin n) : ∀ xF : List (Fin n × Fin n), (xF.map symP).Nodup →
    (((xF.map valP).map qAlts).map (fval r)).prod = edgeProd r (xF.map symP).toFinset
  | [], _ => by simp [edgeProd]
  | p :: xF, hn => by
    have hn' := List.nodup_cons.1 (by simpa using hn : (symP p :: xF.map symP).Nodup)
    have ih := prod_qL r xF hn'.2
    rw [edgeProd_eq] at ih ⊢
    simp only [List.map_cons, List.prod_cons, List.toFinset_cons]
    rw [ih, prod_insert (fun h => hn'.1 (List.mem_toFinset.1 h)), Subring.coe_mul]
    congr 1
    simp only [valP, fval_qAlts, oneQ, symP, qEdge_mk]

theorem deg_eqL (xF : List (Fin n × Fin n)) (hn : (xF.map symP).Nodup) (v : Fin n) :
    Crossing.deg (xF.map symP).toFinset v = (xF.map valP).countP (fun e => decide (e.1 = v.val ∨ e.2 = v.val)) := by
  unfold Crossing.deg
  rw [card_filter_toFinset _ hn, List.countP_map, List.countP_map]
  congr 1
  funext p
  simp only [Function.comp_apply, symP, valP, Sym2.mem_iff, ← Fin.ext_iff, eq_comm]

section MainD

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {β : Fin n → Fin g} (X : Crossing G β m)

/-- **The degree-pruned stream computes the node table** `σ_a(ℓ) · χ_a(ℓ, y) · I_a(ℓ)`. -/
theorem tableStreamD_eq (r : Fin n) (a : Fin g) (ℓ : Fin m → Label) (y : Fin g × Fin g → ZMod 2) (d : TD)
    (hD : TDesc G X r a ℓ y d) :
    tableStreamD d = X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * X.I r ℓ a := by
  obtain ⟨⟨rr, aa⟩, ⟨va, vr⟩, ⟨es, cl⟩, yl⟩ := d
  obtain ⟨hr, ha, ⟨L, hL, hva⟩, hvr, ⟨esF, hn, hE, hes⟩, hcl, ⟨ql, hqn, hq, hyl⟩⟩ := hD
  simp only at hr ha hva hvr hes hcl hyl
  subst hr ha hva hvr hes hcl hyl
  set S := blob β a
  set cl0 := ((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)
  set A := genSet r S
  set Ω := OmegaSet r S
  set vrl := (((S.erase r).sort (· ≤ ·))).map Fin.val
  set yl0 := ql.map fun p => ((p.1.val, p.2.val), decide (y p = 1))
  set d : TD := ((r.val, a.val), (L.map Fin.val, vrl), (esF.map valP, cl0), yl0) with hd
  have hAl : ∀ γ ∈ genL vrl, γ < 2 * n := genL_lt _
  have hfA : finOf n (genL vrl) = A := finOf_genL r S
  -- the coefficient of `Ω` is streamed
  have hOm : finalC (genL vrl) ((omL vrl).foldl (stepL r.val) (some (1, []))) = Ω.coeff A := by
    have hw : ∀ x ∈ omL vrl, x.2 < n := by
      intro x hx
      simp only [vrl, omL, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨_, ⟨v, -, rfl⟩, h⟩ := hx
      rcases h with rfl | rfl <;> exact v.2
    obtain ⟨h1, h2⟩ := foldL_sem r _ hw _ (sInv_some_nil (n := n) 1)
    rw [finalC_eq hAl h2, h1, prod_omL, hfA]
    simp only [sem, Option.elim, one_smul]
    rw [show finOf n [] = ∅ by ext; simp, Grass.e_empty, one_mul]
    rfl
  -- the edges of the data
  have hEsym : ∀ p ∈ esF, symP p ∈ Crossing.Eint G β a := fun p hp => (hE _).1 (List.mem_map_of_mem hp)
  have hown : ∀ p ∈ esF, β p.1 = a := fun p hp =>
    (Crossing.mem_Eint.1 (hEsym p hp)).2 p.1 (Sym2.mem_mk_left _ _)
  have hinj : ∀ p ∈ esF, ∀ q ∈ esF, symP p = symP q → p = q := List.inj_on_of_nodup_map hn
  have hnF : esF.Nodup := List.Nodup.of_map _ hn
  -- owners and groups
  set ownF : List (Fin n) := r :: (S.erase r).sort (· ≤ ·) with hownF
  have hownN : ownF.Nodup := by
    refine List.nodup_cons.2 ⟨?_, sort_nodup _ _⟩
    rw [mem_sort]; exact notMem_erase r S
  have hmemOwn : ∀ v, β v = a → v ∈ ownF := by
    intro v hv
    by_cases h : v = r
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ ((mem_sort _).2 (mem_erase.2 ⟨h, mem_blob.2 hv⟩))
  set gsF : List (List (Fin n × Fin n)) := ownF.map fun v => esF.filter fun p => p.1 = v with hgsF
  set gsS : List (List (Sym2 (Fin n))) := gsF.map (List.map symP) with hgsS
  have hgrp : grpD d = gsF.map (List.map valP) := by
    simp only [grpD, ownD, hd, gsF, ownF, vrl, List.map_cons, List.map_map]
    congr 1
    · rw [List.filter_map]
      congr 1
      refine List.filter_congr fun p _ => ?_
      rw [Bool.eq_iff_iff]
      simp only [Function.comp_apply, valP, decide_eq_true_eq, Fin.val_inj]
    · refine List.map_congr_left fun v _ => ?_
      simp only [Function.comp_apply]
      rw [List.filter_map]
      congr 1
      refine List.filter_congr fun p _ => ?_
      rw [Bool.eq_iff_iff]
      simp only [Function.comp_apply, valP, decide_eq_true_eq, Fin.val_inj]
  have hselD : ∀ i, selD d i = (selG gsF i).map valP := fun i => by
    rw [selD, hgrp, selG_map]
  have hselS : ∀ i, selG gsS i = (selG gsF i).map symP := fun i => selG_map symP gsF i
  have hrD : rD d = (gsS.map radS).prod := by
    simp only [rD, hgrp, gsS, List.map_map]
    congr 1
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply, radS_map]
  -- the union of the groups
  have hmemFl : ∀ p, p ∈ gsF.flatten ↔ p ∈ esF := by
    intro p
    rw [List.mem_flatten]
    constructor
    · rintro ⟨l, hl, hp⟩
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hl
      exact (List.mem_filter.1 hp).1
    · intro hp
      exact ⟨_, List.mem_map.2 ⟨p.1, hmemOwn _ (hown p hp), rfl⟩, List.mem_filter.2 ⟨hp, by simp⟩⟩
  have hnFl : gsF.flatten.Nodup := by
    rw [List.nodup_flatten]
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hl
      exact hnF.filter _
    · rw [List.pairwise_map]
      refine hownN.imp fun {v w} hvw => ?_
      rw [List.disjoint_left]
      intro p hp hq
      simp only [List.mem_filter, decide_eq_true_eq] at hp hq
      exact hvw (hp.2.symm.trans hq.2)
  have hnS : gsS.flatten.Nodup := by
    rw [hgsS, ← List.map_flatten]
    exact hnFl.map_on fun p hp q hq h => hinj p ((hmemFl p).1 hp) q ((hmemFl q).1 hq) h
  have hflS : gsS.flatten.toFinset = Crossing.Eint G β a := by
    ext e
    rw [hgsS, ← List.map_flatten, List.mem_toFinset, ← hE, List.mem_map, List.mem_map]
    simp only [hmemFl]
  -- the summand
  set K : Finset (Sym2 (Fin n)) → ℤ := fun x =>
    X.degInd ℓ a x * Grass.topCoeff A Ω (edgeProd r x * X.Gam r ℓ a) with hK
  have hvan : ∀ x ⊆ gsS.flatten.toFinset, (∃ g ∈ gsS, 2 < (x ∩ g.toFinset).card) → K x = 0 := by
    rintro x - ⟨g', hg', hc⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg'
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hl
    obtain ⟨e, he⟩ := card_pos.1 (by omega : 0 < (x ∩ ((esF.filter fun p => p.1 = v).map symP).toFinset).card)
    have hsub : x ∩ ((esF.filter fun p => p.1 = v).map symP).toFinset ⊆ x.filter fun e => v ∈ e := by
      intro e' he'
      obtain ⟨h1, h2⟩ := mem_inter.1 he'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 h2)
      simp only [List.mem_filter, decide_eq_true_eq] at hp
      refine mem_filter.2 ⟨h1, ?_⟩
      rw [← hp.2]; exact Sym2.mem_mk_left _ _
    have hvb : v ∈ S := by
      obtain ⟨p, hp, -⟩ := List.mem_map.1 (List.mem_toFinset.1 (mem_inter.1 he).2)
      simp only [List.mem_filter, decide_eq_true_eq] at hp
      rw [← hp.2]; exact mem_blob.2 (hown p hp.1)
    have hdeg : 2 < Crossing.deg x v := lt_of_lt_of_le hc (card_le_card hsub)
    simp only [hK, Crossing.degInd]
    rw [if_neg (fun h => by have := h v hvb; omega), zero_mul]
  -- one outer term
  have hinner : ∀ i, ∑ j ∈ range (nID d i), termD d i j =
      X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * K (selG gsS i).toFinset := by
    intro i
    rw [hselS i]
    set xF := selG gsF i
    have hxn : (xF.map symP).Nodup := by
      rw [← hselS]; exact (selG_sublist gsS i).nodup hnS
    have hdeg : DC (L.map Fin.val) cl0 (xF.map valP) = X.degInd ℓ a (xF.map symP).toFinset := by
      unfold DC Crossing.degInd
      congr 1
      simp only [List.all_eq_true, List.mem_map, decide_eq_true_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, mem_blob]
      refine propext ⟨fun h v hv => ?_, fun h v hv => ?_⟩
      · rw [deg_eqL xF hxn, degL_eqC]; exact h v ((hL v).2 hv)
      · rw [← deg_eqL xF hxn, ← degL_eqC]; exact h v ((hL v).1 hv)
    have hs : sigmaC a.val cl0 = X.chords.sigma (labelPar ℓ) a := (sigma_eqC X ℓ a).symm
    have hc : chiC a.val cl0 yl0 = X.chords.chi (labelPar ℓ) a y := (chi_eqC X ℓ a y ql hqn hq).symm
    have hDC := DC_selD d i
    rw [hselD i, hdeg] at hDC
    unfold nID
    by_cases hok : okD d i = true
    · rw [if_pos hok] at hDC ⊢
      set fs := facD d i
      have hfs : fs = (xF.map valP).map qAlts ++ cl0.map pieceAlts := by
        show (selD d i).map qAlts ++ cl0.map pieceAlts = _
        rw [hselD i]
      have hfok : ∀ f ∈ fs, AltOK n f := by
        intro f hf
        rw [hfs] at hf
        rcases List.mem_append.1 hf with hf | hf
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hf
          obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
          exact altOK_qAlts p.1.2 p.2.2
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hf
          obtain ⟨k, -, rfl⟩ := List.mem_map.1 hu
          exact altOK_pieceAlts G X ℓ a k
      have hv : ∀ j, valC r.val (genL vrl) (mixR List.length (pick r.val) fs j) =
          (((mixR List.length (pick r.val) fs j).map (altVal r)).prod).coeff A := by
        intro j
        rw [valC_eq r hAl _ ?_, hfA]
        intro c hc
        obtain ⟨f, hf, dd, rfl⟩ := mem_mixR _ _ _ _ c hc
        exact altOK_pick (hfok f hf) r.2 dd
      have hsum : ∑ j ∈ range ((fs.map List.length).prod),
          valC r.val (genL vrl) (mixR List.length (pick r.val) fs j) =
          (edgeProd r (xF.map symP).toFinset * X.Gam r ℓ a).coeff A := by
        simp only [hv, ← Grass.coeff_sum]
        rw [sum_mixR_prod List.length (pick r.val) (altVal r) fs]
        rw [List.map_congr_left (fun f _ => sum_pick r f f.length le_rfl)]
        rw [hfs, List.map_append, List.prod_append, prod_qL r xF hxn, prod_pieces]
      unfold termD
      simp only [hd]
      rw [hs, hc, hOm, ← sum_mul, ← mul_sum]
      rw [hsum, hK]
      simp only
      rw [hDC]
      simp only [one_mul, Grass.topCoeff]
      ring
    · rw [if_neg hok] at hDC ⊢
      rw [range_zero, sum_empty, hK]
      simp only
      rw [hDC]
      simp
  -- assemble
  unfold tableStreamD
  rw [sum_congr rfl fun i _ => hinner i, ← mul_sum, hrD, sum_selG gsS hnS K hvan, hflS]
  rfl

end MainD

end

/-! ### Polynomial time -/

/-- `prs` written with `zip`, `range` and `drop` (the form computed). -/
def prsC {β : Type} (l : List β) : List (List β) :=
  (l.zip (List.range l.length)).flatMap fun p => (l.drop (p.2 + 1)).map fun e' => [p.1, e']

theorem prsC_eq {β : Type} : ∀ l : List β, prsC l = prs l
  | [] => rfl
  | e :: l => by
    rw [prs, ← prsC_eq l]
    simp [prsC, List.range_succ_eq_map, List.zip_map_right, List.flatMap_map]

/-- `mixR` written with `zip`, `range` and prefix products (the form computed). -/
def mixC {α β : Type} (rad : α → ℕ) (H : α → ℕ → β) (l : List α) (m : ℕ) : List β :=
  (l.zip (List.range l.length)).map fun p => H p.1 (m / ((l.take p.2).map rad).prod % rad p.1)

theorem mixC_eq {α β : Type} (rad : α → ℕ) (H : α → ℕ → β) :
    ∀ (l : List α) (m : ℕ), mixC rad H l m = mixR rad H l m
  | [], _ => rfl
  | e :: l, m => by
    rw [mixR, ← mixC_eq rad H l (m / rad e)]
    simp only [mixC, List.length_cons, List.range_succ_eq_map, List.zip_cons_cons, List.map_cons,
      List.take_zero, List.map_nil, List.prod_nil, Nat.div_one, List.zip_map_right, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, Prod.map, id, List.take_succ_cons, List.map_cons, List.prod_cons,
      Nat.div_div_eq_div_mul]

section Poly

open Groundwork

variable {γ : Type} [Enc γ]

@[fun_prop] theorem natProd_polyT {l : γ → List ℕ} (hl : PolyT l) : PolyT fun x => (l x).prod := by
  obtain ⟨t, ht, -, hlen⟩ := PolyT.len_bound hl
  have h : PolyT (fun x => (l x).foldl (fun c e => c * e) 1) := by
    refine PolyT.foldl_add (g := fun _ c e => c * e) hl (by fun_prop) (by fun_prop) ⟨t, ht, fun x c e he => ?_⟩
    exact (PolyT.len_mul_le c e).trans (Nat.add_le_add_left ((len_le_of_mem he).trans (hlen x)) _)
  exact h.congr fun x => by rw [List.prod_eq_foldl]

@[fun_prop] theorem prsC_polyT {β : Type} [Enc β] {l : γ → List β} (hl : PolyT l) :
    PolyT fun x => prsC (l x) := by
  unfold prsC
  have hr : PolyT fun x => List.range (l x).length := PolyT.range (Unary.of_length hl)
  exact PolyT.flatMap (f := fun x (p : β × ℕ) => ((l x).drop (p.2 + 1)).map fun e' => [p.1, e'])
    (by fun_prop) (by fun_prop)

@[fun_prop] theorem sm2_polyT {β : Type} [Enc β] {l : γ → List β} (hl : PolyT l) :
    PolyT fun x => sm2 (l x) := by
  have h : PolyT fun x => ([] : List β) :: ((l x).map (fun e => [e]) ++ prsC (l x)) := by fun_prop
  exact h.congr fun x => by rw [prsC_eq]; rfl

@[fun_prop] theorem radS_polyT {β : Type} [Enc β] {l : γ → List β} (hl : PolyT l) :
    PolyT fun x => radS (l x) := by
  unfold radS; fun_prop

@[fun_prop] theorem chS_polyT {β : Type} [Enc β] {l : γ → List β} {c : γ → ℕ} (hl : PolyT l) (hc : PolyT c) :
    PolyT fun x => chS (l x) (c x) := by
  unfold chS; fun_prop

theorem mixR_polyT {α β : Type} [Enc α] [Enc β] {rad : γ → α → ℕ} {H : γ → α → ℕ → β}
    (hrad : PolyT fun q : γ × α => rad q.1 q.2) (hH : PolyT fun q : γ × α × ℕ => H q.1 q.2.1 q.2.2)
    {l : γ → List α} {m : γ → ℕ} (hl : PolyT l) (hm : PolyT m) :
    PolyT fun x => mixR (rad x) (H x) (l x) (m x) := by
  have hr : PolyT fun x => List.range (l x).length := PolyT.range (Unary.of_length hl)
  have h1 : PolyT fun q : γ × (α × ℕ) => q.1 := PolyT.fst PolyT.id'
  have h2 : PolyT fun q : γ × (α × ℕ) => q.2.1 := PolyT.fst (PolyT.snd PolyT.id')
  have h3 : PolyT fun q : γ × (α × ℕ) => q.2.2 := PolyT.snd (PolyT.snd PolyT.id')
  have hlq : PolyT fun q : γ × (α × ℕ) => (l q.1).take q.2.2 := PolyT.take h3 (PolyT.comp hl h1)
  have hmap : PolyT fun q : γ × (α × ℕ) => ((l q.1).take q.2.2).map (rad q.1) :=
    PolyT.map (f := fun q : γ × (α × ℕ) => fun a => rad q.1 a)
      (PolyT.comp (g := fun z : (γ × (α × ℕ)) × α => (z.1.1, z.2)) hrad
        (PolyT.prodMk (PolyT.fst (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id'))) hlq
  have hp : PolyT fun q : γ × (α × ℕ) => (((l q.1).take q.2.2).map (rad q.1)).prod := natProd_polyT hmap
  have hrd : PolyT fun q : γ × (α × ℕ) => rad q.1 q.2.1 :=
    PolyT.comp (g := fun q : γ × (α × ℕ) => (q.1, q.2.1)) hrad (PolyT.prodMk h1 h2)
  have hdig : PolyT fun q : γ × (α × ℕ) => m q.1 / (((l q.1).take q.2.2).map (rad q.1)).prod % rad q.1 q.2.1 :=
    PolyT.mod (PolyT.div (PolyT.comp hm h1) hp) hrd
  have hf : PolyT fun q : γ × (α × ℕ) =>
      H q.1 q.2.1 (m q.1 / (((l q.1).take q.2.2).map (rad q.1)).prod % rad q.1 q.2.1) :=
    PolyT.comp (g := fun q : γ × (α × ℕ) =>
      (q.1, q.2.1, m q.1 / (((l q.1).take q.2.2).map (rad q.1)).prod % rad q.1 q.2.1)) hH
      (PolyT.prodMk h1 (PolyT.prodMk h2 hdig))
  have h : PolyT fun x => mixC (rad x) (H x) (l x) (m x) := by
    unfold mixC
    exact PolyT.map (f := fun x (p : α × ℕ) => H x p.1 (m x / (((l x).take p.2).map (rad x)).prod % rad x p.1))
      hf (PolyT.zip hl hr)
  exact h.congr fun x => mixC_eq (rad x) (H x) (l x) (m x)

theorem mixLen_polyT {β : Type} [Enc β] {H : γ → List β → ℕ → β}
    (hH : PolyT fun q : γ × List β × ℕ => H q.1 q.2.1 q.2.2) {l : γ → List (List β)} {m : γ → ℕ}
    (hl : PolyT l) (hm : PolyT m) : PolyT fun x => mixR List.length (H x) (l x) (m x) :=
  mixR_polyT (rad := fun _ => List.length) (PolyT.length (PolyT.snd PolyT.id')) hH hl hm

@[fun_prop] theorem selG_polyT {β : Type} [Enc β] {gs : γ → List (List β)} {i : γ → ℕ} (hg : PolyT gs)
    (hi : PolyT i) : PolyT fun x => selG (gs x) (i x) := by
  unfold selG
  exact PolyT.flatten (mixR_polyT (rad := fun _ => radS) (H := fun _ => chS) (by fun_prop) (by fun_prop) hg hi)

theorem grpD_polyT : PolyT grpD := by
  unfold grpD ownD
  fun_prop

theorem rD_polyT : PolyT rD := by
  have := grpD_polyT
  unfold rD
  fun_prop

theorem selD_polyT : PolyT fun p : TD × ℕ => selD p.1 p.2 := by
  have := grpD_polyT
  unfold selD
  fun_prop

theorem facD_polyT : PolyT fun p : TD × ℕ => facD p.1 p.2 := by
  have := selD_polyT
  unfold facD
  fun_prop

theorem okD_polyT : PolyT fun p : TD × ℕ => okD p.1 p.2 := by
  have := selD_polyT
  unfold okD
  fun_prop

theorem nID_polyT : PolyT fun p : TD × ℕ => nID p.1 p.2 := by
  have := facD_polyT
  have := okD_polyT
  unfold nID
  fun_prop

theorem chooseD_polyT : PolyT fun q : (TD × ℕ) × ℕ => mixR List.length (pick q.1.1.1.1) (facD q.1.1 q.1.2) q.2 := by
  have hf : PolyT fun q : (TD × ℕ) × ℕ => facD q.1.1 q.1.2 :=
    PolyT.comp (g := fun q : (TD × ℕ) × ℕ => q.1) facD_polyT (by fun_prop)
  have hpk : PolyT fun z : ((TD × ℕ) × ℕ) × List Alt × ℕ => pick z.1.1.1.1.1 z.2.1 z.2.2 := by fun_prop
  have hj : PolyT fun q : (TD × ℕ) × ℕ => q.2 := by fun_prop
  exact mixLen_polyT hpk hf hj

theorem termD_polyT : PolyT fun q : (TD × ℕ) × ℕ => termD q.1.1 q.1.2 q.2 := by
  have hm := chooseD_polyT
  unfold termD
  fun_prop

end Poly

/-! ### Bounds on the terms and the counts -/

theorem termD_le (d : TD) (i j : ℕ) : (termD d i j).natAbs ≤ 1 := by
  unfold termD
  have h1 := sgnN_natAbs (List.flatMap (fun u => List.map (fun w => sigTerm d.1.2 u w) d.2.2.1.2) d.2.2.1.2).sum
  have h2 := sgnN_natAbs (List.map (chiTerm d.1.2 d.2.2.1.2) d.2.2.2).sum
  have h4 := valC_le d.1.1 (genL d.2.1.2) (mixR List.length (pick d.1.1) (facD d i) j)
  have h5 := finalC_le (genL d.2.1.2) (foldL_SOK d.1.1 (omL d.2.1.2) (s := some (1, [])) (sOK_some 0))
  unfold sigmaC chiC
  simp only [Int.natAbs_mul]
  have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1.le h2.le) h4) h5
  simpa using this

/-! ### The machine -/

section Machine

open Groundwork

/-- The inner loop: one monomial choice per step. -/
def innerD : Stepped (TD × ℕ) ℤ :=
  Stepped.sumRange (fun p : TD × ℕ => nID p.1 p.2) (Stepped.ofFun fun q : (TD × ℕ) × ℕ => termD q.1.1 q.1.2 q.2)

/-- **The degree-pruned node-table machine**: the outer loop runs over the choices of at most two
owned edges per vertex, the inner loop over the monomial choices; the states hold the data, the two
counters and the running sums. -/
def tableMachineD : Stepped TD ℤ := Stepped.sumRange rD innerD

/-- The machine has polynomial-time steps. -/
theorem tableMachineD_poly : Nonempty (IsPolyT tableMachineD) := by
  have : IsPolyT (Stepped.ofFun fun q : (TD × ℕ) × ℕ => termD q.1.1 q.1.2 q.2) := IsPolyT.ofFun termD_polyT
  have : IsPolyT innerD := IsPolyT.sumRange nID_polyT
  exact ⟨IsPolyT.sumRange rD_polyT⟩

/-- **Steps and states of the machine** (for any data), if every inner count is `≤ V`. -/
theorem tableMachineD_runs' (d : TD) (V : ℕ) (hV : ∀ i < rD d, nID d i ≤ V) :
    tableMachineD.Runs d (rD d * (2 * V + 1))
      (3 * size d + 3 * size (rD d) + size (rD d * V) + 3 * size V + 6) (tableStreamD d) := by
  have hin : ∀ i < rD d, innerD.Runs (d, i) (2 * nID d i)
      (2 * size d + 2 * size (rD d) + 3 * size V + 4) (∑ j ∈ range (nID d i), termD d i j) := by
    intro i hi
    have hM : ∀ j < nID d i, (Stepped.ofFun fun q : (TD × ℕ) × ℕ => termD q.1.1 q.1.2 q.2).Runs ((d, i), j) 1
        (size d + size (rD d) + size V + 3) (termD d i j) := by
      intro j hj
      refine (Stepped.ofFun_runs (fun q : (TD × ℕ) × ℕ => termD q.1.1 q.1.2 q.2) ((d, i), j)).mono le_rfl ?_
      have h1 : Nat.size i ≤ Nat.size (rD d) := Nat.size_le_size hi.le
      have h2 : Nat.size j ≤ Nat.size V := Nat.size_le_size (hj.le.trans (hV i hi))
      have h3 : Nat.size (termD d i j).natAbs ≤ 1 := Nat.size_le.2 (by have := termD_le d i j; omega)
      simp only [size_prod, size_nat, size_int]
      omega
    have h := Stepped.sumRange_runs (N := fun p : TD × ℕ => nID p.1 p.2) (a := (d, i)) (fun _ => 1)
      (fun j => termD d i j) 1 _ hM (fun j _ => termD_le d i j)
    refine h.mono ?_ ?_
    · simp [sum_const, card_range]; omega
    · have h1 : Nat.size i ≤ Nat.size (rD d) := Nat.size_le_size hi.le
      have h2 : Nat.size (nID d i) ≤ Nat.size V := Nat.size_le_size (hV i hi)
      simp only [size_prod, size_nat, mul_one] at *
      omega
  have hval : ∀ i < rD d, (∑ j ∈ range (nID d i), termD d i j).natAbs ≤ V := fun i hi =>
    (Stepped.natAbs_sum_le _ 1 _ fun j _ => termD_le d i j).trans (by rw [mul_one]; exact hV i hi)
  have h := Stepped.sumRange_runs (N := rD) (a := d) (fun i => 2 * nID d i)
    (fun i => ∑ j ∈ range (nID d i), termD d i j) V _ hin hval
  refine h.mono ?_ ?_
  · calc ∑ i ∈ range (rD d), (2 * nID d i + 1) ≤ ∑ i ∈ range (rD d), (2 * V + 1) :=
          sum_le_sum fun i hi => by have := hV i (mem_range.1 hi); omega
      _ = rD d * (2 * V + 1) := by rw [sum_const, card_range, smul_eq_mul]
  · omega

end Machine

/-! ### The counts under `TDesc` -/

noncomputable section

variable {n g m : ℕ}

section BoundsD

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {β : Fin n → Fin g} (X : Crossing G β m)

/-- `Σ_{v ∈ V_a} deg_x(v) = 2|x|` for `x ⊆ E_int(a)`. -/
theorem sum_deg_blob {a : Fin g} {x : Finset (Sym2 (Fin n))} (hx : x ⊆ Crossing.Eint G β a) :
    ∑ v ∈ blob β a, Crossing.deg x v = 2 * x.card := by
  unfold Crossing.deg
  simp only [card_filter]
  rw [sum_comm, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun e he => ?_
  rw [← card_filter]
  have he' := hx he
  induction e using Sym2.ind with
  | _ u w =>
    have hu := (Crossing.mem_Eint.1 he').2 u (Sym2.mem_mk_left u w)
    have hw := (Crossing.mem_Eint.1 he').2 w (Sym2.mem_mk_right u w)
    have huw : u ≠ w := G.ne_of_adj (by simpa using (Crossing.mem_Eint.1 he').1)
    rw [card_blob_mem a huw, if_pos hu, if_pos hw]

/-- `Σ_{v ∈ V_a} deg_ℓ(v) = #{k ∈ δ(a) : ℓ_k ≠ N}`: every crossing edge at `a` has one end in `V_a`. -/
theorem sum_degL_blob (ℓ : Fin m → Label) (a : Fin g) :
    ∑ v ∈ blob β a, X.degL ℓ a v = ((X.chords.delta a).filter fun k => ℓ k ≠ Label.N).card := by
  unfold Crossing.degL
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  by_cases hN : ℓ k = Label.N
  · simp [hN]
  · rw [if_pos hN]
    simp only [ne_eq, hN, not_false_eq_true, true_and]
    rw [← card_filter]
    have hlt := X.lt k
    have hne : X.s k ≠ X.t k := fun h => (lt_irrefl (β (X.s k))) (by rwa [← h] at hlt)
    have e : ((blob β a).filter fun v => X.s k = v ∨ X.t k = v) = (blob β a).filter fun v => v ∈ s(X.s k, X.t k) := by
      refine filter_congr fun v _ => ?_
      rw [Sym2.mem_iff]; constructor <;> rintro (h | h) <;> simp [h]
    rw [e, card_blob_mem a hne]
    rcases X.mem_delta.1 hk with h | h
    · rw [if_pos h, if_neg (fun h' => by rw [h, h'] at hlt; exact lt_irrefl a hlt)]
    · rw [if_neg (fun h' => by rw [h, h'] at hlt; exact lt_irrefl a hlt), if_pos h]

variable {G X}

/-- The groups of the data, described. -/
theorem grpD_desc {r : Fin n} {a : Fin g} {ℓ : Fin m → Label} {y : Fin g × Fin g → ZMod 2} {d : TD}
    (hD : TDesc G X r a ℓ y d) : ∃ esF : List (Fin n × Fin n), (esF.map symP).Nodup ∧
      (∀ e, e ∈ esF.map symP ↔ e ∈ Crossing.Eint G β a) ∧
      grpD d = ((r :: ((blob β a).erase r).sort (· ≤ ·)).map fun v => esF.filter fun p => p.1 = v).map
        (List.map valP) := by
  obtain ⟨esF, hn, hE, hes⟩ := hD.es
  refine ⟨esF, hn, hE, ?_⟩
  simp only [grpD, ownD, hD.r_eq, hD.vr_eq, hes, List.map_cons, List.map_map]
  congr 1
  · rw [List.filter_map]
    congr 1
    refine List.filter_congr fun p _ => ?_
    rw [Bool.eq_iff_iff]
    simp only [Function.comp_apply, valP, decide_eq_true_eq, Fin.val_inj]
  · refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp_apply]
    rw [List.filter_map]
    congr 1
    refine List.filter_congr fun p _ => ?_
    rw [Bool.eq_iff_iff]
    simp only [Function.comp_apply, valP, decide_eq_true_eq, Fin.val_inj]

theorem own_of_mem {a : Fin g} {esF : List (Fin n × Fin n)} (hE : ∀ e, e ∈ esF.map symP ↔ e ∈ Crossing.Eint G β a)
    {p : Fin n × Fin n} (hp : p ∈ esF) : β p.1 = a :=
  (Crossing.mem_Eint.1 ((hE _).1 (List.mem_map_of_mem hp))).2 p.1 (Sym2.mem_mk_left _ _)

/-- A group has at most `deg v` edges. -/
theorem length_group_le {a : Fin g} {esF : List (Fin n × Fin n)} (hn : (esF.map symP).Nodup)
    (hE : ∀ e, e ∈ esF.map symP ↔ e ∈ Crossing.Eint G β a) (v : Fin n) :
    (esF.filter fun p => p.1 = v).length ≤ G.degree v := by
  set F := esF.filter fun p => p.1 = v
  have hF : (F.map symP).Nodup := (List.filter_sublist.map symP).nodup hn
  have h1 : F.length = (F.map symP).toFinset.card := by rw [List.toFinset_card_of_nodup hF, List.length_map]
  rw [h1, ← G.card_incidenceFinset_eq_degree, G.incidenceFinset_eq_filter]
  refine card_le_card fun e he => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 he)
  obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
  simp only [decide_eq_true_eq] at hp2
  refine mem_filter.2 ⟨(Crossing.mem_Eint.1 ((hE _).1 (List.mem_map_of_mem hp1))).1, ?_⟩
  rw [← hp2]; exact Sym2.mem_mk_left _ _

/-- **The number of outer terms**: `rD d ≤ D^{2ν_a}` if every vertex of `V_a` has degree `≤ D`, `2 ≤ D`. -/
theorem rD_le {r : Fin n} {a : Fin g} {ℓ : Fin m → Label} {y : Fin g × Fin g → ZMod 2} {d : TD}
    (hD : TDesc G X r a ℓ y d) {D : ℕ} (hD2 : 2 ≤ D) (hdeg : ∀ v ∈ blob β a, G.degree v ≤ D) :
    rD d ≤ D ^ (2 * (blob β a).card) := by
  obtain ⟨esF, hn, hE, hg⟩ := grpD_desc hD
  set ownF : List (Fin n) := r :: ((blob β a).erase r).sort (· ≤ ·)
  have hownN : ownF.Nodup := by
    refine List.nodup_cons.2 ⟨?_, sort_nodup _ _⟩
    rw [mem_sort]; exact notMem_erase r _
  set f : Fin n → ℕ := fun v => radS (esF.filter fun p => p.1 = v)
  have hr : rD d = (ownF.map f).prod := by
    rw [rD, hg, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp_apply, radS_map, f]
  have h1 : ∀ v, v ∉ blob β a → f v = 1 := by
    intro v hv
    have : (esF.filter fun p => p.1 = v) = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp h
      simp only [decide_eq_true_eq] at h
      exact hv (mem_blob.2 (h ▸ own_of_mem hE hp))
    simp only [f, this, radS_nil]
  have hsub : blob β a ⊆ ownF.toFinset := by
    intro v hv
    rw [List.mem_toFinset]
    by_cases h : v = r
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ ((mem_sort _).2 (mem_erase.2 ⟨h, hv⟩))
  rw [hr, ← List.prod_toFinset f hownN, ← prod_subset hsub fun v _ hv => h1 v hv, pow_mul]
  exact prod_le_pow_card _ _ _ fun v hv =>
    radS_le hD2 ((length_group_le hn hE v).trans (hdeg v hv))

/-- The selected edges, described. -/
theorem selD_desc {r : Fin n} {a : Fin g} {ℓ : Fin m → Label} {y : Fin g × Fin g → ZMod 2} {d : TD}
    (hD : TDesc G X r a ℓ y d) (i : ℕ) : ∃ xF : List (Fin n × Fin n), selD d i = xF.map valP ∧
      (xF.map symP).Nodup ∧ (xF.map symP).toFinset ⊆ Crossing.Eint G β a := by
  obtain ⟨esF, hn, hE, hg⟩ := grpD_desc hD
  set ownF : List (Fin n) := r :: ((blob β a).erase r).sort (· ≤ ·)
  have hownN : ownF.Nodup := by
    refine List.nodup_cons.2 ⟨?_, sort_nodup _ _⟩
    rw [mem_sort]; exact notMem_erase r _
  set gsF := ownF.map fun v => esF.filter fun p => p.1 = v
  have hinj : ∀ p ∈ esF, ∀ q ∈ esF, symP p = symP q → p = q := List.inj_on_of_nodup_map hn
  have hnF : esF.Nodup := List.Nodup.of_map _ hn
  have hmemFl : ∀ p ∈ gsF.flatten, p ∈ esF := by
    intro p hp
    obtain ⟨l, hl, hp⟩ := List.mem_flatten.1 hp
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hl
    exact (List.mem_filter.1 hp).1
  have hnFl : gsF.flatten.Nodup := by
    rw [List.nodup_flatten]
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hl
      exact hnF.filter _
    · rw [List.pairwise_map]
      refine hownN.imp fun {v w} hvw => ?_
      rw [List.disjoint_left]
      intro p hp hq
      simp only [List.mem_filter, decide_eq_true_eq] at hp hq
      exact hvw (hp.2.symm.trans hq.2)
  refine ⟨selG gsF i, by rw [selD, hg, selG_map], ?_, ?_⟩
  · exact ((selG_sublist gsF i).nodup hnFl).map_on fun p hp q hq h =>
      hinj p (hmemFl p ((selG_sublist gsF i).subset hp)) q (hmemFl q ((selG_sublist gsF i).subset hq)) h
  · intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 he)
    exact (hE _).1 (List.mem_map_of_mem (hmemFl p ((selG_sublist gsF i).subset hp)))

theorem length_pieceAlts_le (Y : Crossing G β m) (ℓ : Fin m → Label) (a : Fin g) (k : Fin m) :
    (pieceAlts (ceOf Y ℓ a k)).length ≤ if ℓ k = Label.N then 1 else 2 := by
  unfold pieceAlts aAlts bAlts ceOf
  cases ℓ k <;> split_ifs <;> simp_all [Label.code]

theorem pow_five_le {x s ν : ℕ} (h : 2 * x + s = 2 * ν) : 5 ^ x * 2 ^ s ≤ 5 ^ ν := by
  obtain ⟨t, rfl⟩ : ∃ t, ν = x + t := ⟨ν - x, by omega⟩
  have hs : s = 2 * t := by omega
  rw [hs, pow_mul, pow_add]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) t)

/-- **The number of inner terms**: `nID d i ≤ 5^{ν_a}`. -/
theorem nID_le {r : Fin n} {a : Fin g} {ℓ : Fin m → Label} {y : Fin g × Fin g → ZMod 2} {d : TD}
    (hD : TDesc G X r a ℓ y d) (i : ℕ) : nID d i ≤ 5 ^ (blob β a).card := by
  unfold nID
  split_ifs with hok
  swap; · exact Nat.zero_le _
  obtain ⟨xF, hxF, hxn, hsub⟩ := selD_desc hD i
  obtain ⟨L, hL, hva⟩ := hD.va
  set x := (xF.map symP).toFinset
  -- the degree test
  have hdeg : ∀ v ∈ blob β a, Crossing.deg x v + X.degL ℓ a v = 2 := by
    intro v hv
    have := List.all_eq_true.1 hok v.val (by rw [hva]; exact List.mem_map_of_mem ((hL v).2 (mem_blob.1 hv)))
    rw [decide_eq_true_eq, hxF, hD.cl_eq] at this
    rw [deg_eqL xF hxn, degL_eqC]
    exact this
  have h1 : ∑ v ∈ blob β a, (Crossing.deg x v + X.degL ℓ a v) = 2 * (blob β a).card := by
    rw [sum_congr rfl hdeg, sum_const, smul_eq_mul, mul_comm]
  rw [sum_add_distrib, sum_deg_blob G hsub, sum_degL_blob G X ℓ a] at h1
  have hx : x.card = xF.length := by rw [List.toFinset_card_of_nodup hxn, List.length_map]
  -- the product of the factor lengths
  have hfac : ((facD d i).map List.length).prod = 5 ^ xF.length *
      (((((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)).map pieceAlts).map List.length).prod := by
    unfold facD
    rw [hxF, hD.cl_eq, List.map_append, List.prod_append, List.map_map, List.map_map]
    congr 1
    rw [show ((List.length ∘ qAlts) ∘ valP : Fin n × Fin n → ℕ) = fun _ => 5 from rfl, List.map_const',
      List.prod_replicate]
  have hpc : (((((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)).map pieceAlts).map List.length).prod ≤
      2 ^ ((X.chords.delta a).filter fun k => ℓ k ≠ Label.N).card := by
    rw [List.map_map, List.map_map]
    refine (List.prod_le_prod' fun k _ => length_pieceAlts_le X ℓ a k).trans (le_of_eq ?_)
    rw [← List.prod_toFinset _ (sort_nodup _ _), sort_toFinset, prod_ite, prod_const_one, one_mul, prod_const]
  rw [hfac]
  refine (Nat.mul_le_mul_left _ hpc).trans (pow_five_le ?_)
  rw [← hx]; exact h1

end BoundsD

end

/-! ### The degree-pruned table procedure -/

section SpecD

open Groundwork

variable {n g m : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {β : Fin n → Fin g} (X : Crossing G β m)

/-- **The degree-pruned node-table machine computes `σ_a(ℓ) χ_a(ℓ, y) I_a(ℓ)`** within
`3 · D^{2ν_a} · 5^{ν_a}` steps on states of size `3 · size d + 8 ν_a (Nat.size D + 2) + 20`, where
`ν_a = |V_a|` and `D ≥ 2` bounds the degrees of the vertices of `V_a`. -/
theorem tableMachineD_runs (r : Fin n) (a : Fin g) (ℓ : Fin m → Label) (y : Fin g × Fin g → ZMod 2) (d : TD)
    (hD : TDesc G X r a ℓ y d) {D : ℕ} (hD2 : 2 ≤ D) (hdeg : ∀ v ∈ blob β a, G.degree v ≤ D) :
    tableMachineD.Runs d (3 * D ^ (2 * (blob β a).card) * 5 ^ (blob β a).card)
      (3 * size d + 8 * (blob β a).card * (Nat.size D + 2) + 20)
      (X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * X.I r ℓ a) := by
  set ν := (blob β a).card
  have hR := rD_le hD hD2 hdeg
  have h := tableMachineD_runs' d (5 ^ ν) fun i _ => nID_le hD i
  rw [tableStreamD_eq G X r a ℓ y d hD] at h
  have hV1 : 1 ≤ 5 ^ ν := Nat.one_le_pow _ _ (by norm_num)
  refine h.mono ?_ ?_
  · calc rD d * (2 * 5 ^ ν + 1) ≤ D ^ (2 * ν) * (3 * 5 ^ ν) := Nat.mul_le_mul hR (by omega)
      _ = 3 * D ^ (2 * ν) * 5 ^ ν := by ring
  · have hsD : D < 2 ^ Nat.size D := Nat.lt_size_self D
    have hpow : D ^ (2 * ν) ≤ 2 ^ (2 * (ν * Nat.size D)) := by
      calc D ^ (2 * ν) ≤ (2 ^ Nat.size D) ^ (2 * ν) := Nat.pow_le_pow_left hsD.le _
        _ = 2 ^ (2 * (ν * Nat.size D)) := by rw [← pow_mul]; ring_nf
    have h5 : 5 ^ ν ≤ 2 ^ (3 * ν) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) _
    have s1 : Nat.size (rD d) ≤ 2 * (ν * Nat.size D) + 1 :=
      Nat.size_le.2 (lt_of_le_of_lt (hR.trans hpow) (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    have s2 : Nat.size (5 ^ ν) ≤ 3 * ν + 1 :=
      Nat.size_le.2 (lt_of_le_of_lt h5 (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    have s3 : Nat.size (rD d * 5 ^ ν) ≤ 2 * (ν * Nat.size D) + 3 * ν + 1 := by
      refine Nat.size_le.2 (lt_of_le_of_lt (Nat.mul_le_mul (hR.trans hpow) h5) ?_)
      rw [← pow_add]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have e : 8 * ν * (Nat.size D + 2) = 8 * (ν * Nat.size D) + 16 * ν := by ring
    rw [e]
    simp only [size_nat]
    generalize ν * Nat.size D = t at s1 s3 ⊢
    omega

/-- The degree-pruned T-procedure: read the data with `rd`, then run the degree-pruned machine. -/
def tableProcD {Q : Type} (rd : Q → TD) : Stepped Q ℤ := Stepped.mapIn rd tableMachineD

theorem tableProcD_poly {Q : Type} [Enc Q] {rd : Q → TD} (hrd : PolyT rd) :
    Nonempty (IsPolyT (tableProcD rd)) := by
  obtain ⟨i⟩ := tableMachineD_poly
  exact ⟨IsPolyT.mapIn hrd⟩

theorem tableProcD_runs {Q : Type} (rd : Q → TD) (q : Q) (r : Fin n) (a : Fin g) (ℓ : Fin m → Label)
    (y : Fin g × Fin g → ZMod 2) (hD : TDesc G X r a ℓ y (rd q)) {D : ℕ} (hD2 : 2 ≤ D)
    (hdeg : ∀ v ∈ blob β a, G.degree v ≤ D) :
    (tableProcD rd).Runs q (3 * D ^ (2 * (blob β a).card) * 5 ^ (blob β a).card)
      (3 * size (rd q) + 8 * (blob β a).card * (Nat.size D + 2) + 20)
      (X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * X.I r ℓ a) :=
  Stepped.mapIn_runs (tableMachineD_runs G X r a ℓ y (rd q) hD hD2 hdeg)

end SpecD

end EthFollowup.ExactHC
