import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh.CoreCover




 





set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

variable {U : Set ℂ} (hU : IsPathConnected U)
  (γ : C(unitInterval, ℂ)) (hγ : range γ ⊆ U)

private def base : U := ⟨γ 0, hγ ⟨0, rfl⟩⟩

private def pathToBase (x : U) : Path (x : ℂ) (base γ hγ : ℂ) :=
  (hU.joinedIn (x : ℂ) x.property (base γ hγ : ℂ) (base γ hγ).property).somePath

 
def core (F : Finset U) : Set ℂ :=
  range γ ∪ ⋃ x : F, range (pathToBase hU γ hγ x)

 
theorem mem_core_of_mem {F : Finset U} {x : U} (hx : x ∈ F) :
    (x : ℂ) ∈ core hU γ hγ F := by
  right
  refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
  exact ⟨0, by simp [pathToBase]⟩

 
theorem spine_subset_core (F : Finset U) : range γ ⊆ core hU γ hγ F :=
  subset_union_left

 
theorem core_subset (F : Finset U) : core hU γ hγ F ⊆ U := by
  rintro y (hy | hy)
  · exact hγ hy
  · obtain ⟨x, ⟨t, rfl⟩⟩ := mem_iUnion.mp hy
    exact (hU.joinedIn (x : ℂ) x.val.property (base γ hγ : ℂ)
      (base γ hγ).property).somePath_mem t

 
theorem core_compact (F : Finset U) : IsCompact (core hU γ hγ F) := by
  apply IsCompact.union (isCompact_range γ.continuous)
  exact isCompact_iUnion (fun x : F => isCompact_range (pathToBase hU γ hγ x).continuous)

 
theorem core_preconnected (F : Finset U) : IsPreconnected (core hU γ hγ F) := by
  by_cases hF : F.Nonempty
  · have hpaths : IsPreconnected (⋃ x : F, range (pathToBase hU γ hγ x)) := by
      apply isPreconnected_iUnion
      · refine ⟨base γ hγ, ?_⟩
        simp only [mem_iInter]
        intro x
        exact ⟨1, by simp [pathToBase]⟩
      · intro x
        exact (isConnected_range (pathToBase hU γ hγ x).continuous).isPreconnected
    apply IsPreconnected.union (base γ hγ : ℂ)
    · exact ⟨0, rfl⟩
    · obtain ⟨x, hx⟩ := hF
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, ⟨1, by simp [pathToBase]⟩⟩
    · exact (isConnected_range γ.continuous).isPreconnected
    · exact hpaths
  · have hEmpty : IsEmpty F := ⟨fun x => hF ⟨x.val, x.property⟩⟩
    letI : IsEmpty F := hEmpty
    simpa [core] using (isConnected_range γ.continuous).isPreconnected


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh
