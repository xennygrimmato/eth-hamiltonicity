import Mathlib
open BitVec
#check @BitVec.getLsbD_cons
#check @BitVec.getLsbD_signExtend
#check @BitVec.getLsbD_extractLsb'
#check @finFunctionFinEquiv_symm_apply_val
#check @Nat.testBit_eq_decide_div_mod_eq
#check @Submodule.mem_span_range_iff_exists_fun
#check @Submodule.mem_span_insert
#check @finrank_range_le_card
#check @finrank_span_eq_card
#check @Submodule.finrank_lt_finrank_of_lt
#check @Submodule.finrank_mono
#check @LinearMap.funLeft
#check @Fintype.linearIndependent_iff
example : (2:ℕ)^8 = 256 := rfl
