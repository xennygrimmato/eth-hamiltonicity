/-
Exploratory file (`research/next/v3`).  Not imported by the root module and not a claimed result.

The bridge between the rank metric on matrices (Anthropic's contracting hypothesis) and the Grassmannian
(OpenAI's port graphs): for linear maps `f g : V → W`,

  `dim (graph f + graph g) = dim V + rank (f - g)`.

So `a ↦ graph a` carries `rk (a - b)` on `Mat_μ` to `dim (U + U') - μ` on the `μ`-dimensional subspaces of a
`2μ`-dimensional space.
-/
import Mathlib

namespace EthFollowup.Spectral

open Module Submodule

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem graph_sup_graph (f g : V →ₗ[K] W) :
    f.graph ⊔ g.graph = f.graph ⊔ (LinearMap.range (f - g)).map (LinearMap.inr K V W) := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rintro ⟨x, y⟩ hxy
    rw [LinearMap.mem_graph_iff] at hxy
    simp only at hxy
    have h1 : ((x, f x) : V × W) ∈ f.graph := by rw [LinearMap.mem_graph_iff]
    have h2 : ((0, g x - f x) : V × W) ∈ (LinearMap.range (f - g)).map (LinearMap.inr K V W) := by
      refine ⟨g x - f x, ⟨-x, ?_⟩, rfl⟩
      simp only [map_neg, LinearMap.sub_apply]
      abel
    have : ((x, y) : V × W) = (x, f x) + (0, g x - f x) := by
      simp [hxy]
    rw [this]
    exact add_mem (mem_sup_left h1) (mem_sup_right h2)
  · refine sup_le le_sup_left ?_
    rintro _ ⟨w, ⟨x, rfl⟩, rfl⟩
    have h1 : ((x, f x) : V × W) ∈ f.graph := by rw [LinearMap.mem_graph_iff]
    have h2 : ((x, g x) : V × W) ∈ g.graph := by rw [LinearMap.mem_graph_iff]
    have : (LinearMap.inr K V W) ((f - g) x) = (x, f x) - (x, g x) := by simp
    rw [this]
    exact sub_mem (mem_sup_left h1) (mem_sup_right h2)

theorem graph_disjoint_inr (f : V →ₗ[K] W) (P : Submodule K W) :
    Disjoint f.graph (P.map (LinearMap.inr K V W)) := by
  rw [Submodule.disjoint_def]
  rintro ⟨x, y⟩ h1 ⟨w, _, hw⟩
  rw [LinearMap.mem_graph_iff] at h1
  simp only [LinearMap.inr_apply, Prod.mk.injEq] at hw
  simp only at h1
  obtain ⟨hx, _⟩ := hw
  subst hx
  simp [h1]

theorem finrank_graph [FiniteDimensional K V] [FiniteDimensional K W] (f : V →ₗ[K] W) :
    finrank K f.graph = finrank K V := by
  rw [LinearMap.graph_eq_range_prod]
  exact LinearMap.finrank_range_of_inj (fun x y h => by simpa using congrArg Prod.fst h)

/-- `dim (graph f + graph g) = dim V + rank (f - g)`. -/
theorem finrank_graph_sup_graph [FiniteDimensional K V] [FiniteDimensional K W] (f g : V →ₗ[K] W) :
    finrank K ↥(f.graph ⊔ g.graph) = finrank K V + finrank K (LinearMap.range (f - g)) := by
  rw [graph_sup_graph]
  have hd := graph_disjoint_inr f (LinearMap.range (f - g))
  have h := Submodule.finrank_sup_add_finrank_inf_eq f.graph ((LinearMap.range (f - g)).map (LinearMap.inr K V W))
  rw [hd.eq_bot, finrank_bot, add_zero] at h
  rw [h, finrank_graph]
  congr 1
  exact (Submodule.equivMapOfInjective (LinearMap.inr K V W) LinearMap.inr_injective _).symm.finrank_eq

end EthFollowup.Spectral
