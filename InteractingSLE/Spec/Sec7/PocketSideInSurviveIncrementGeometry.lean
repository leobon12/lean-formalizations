/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurviveActual

/-!
# The old and current filled sets agree at a surviving incoming side

PROVE-POCKET-SIDEIN. Local survival of the initial physical pocket means
the added ambient hull contributes no new filled points there. The initial
and current filled sets therefore have the same physical germ.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

open PocketUnionPt

/-- Initial and current fillings agree near a point where the initial
pocket remains active. The hull may touch the initial frontier itself. -/
theorem filled_initial_agreement_of_active_neighborhood {C F : Set ℂ} {c : Chart}
    (hDomain : (c.dom : Set ℂ) = C ∩ (H \ F)) {p : ℂ}
    (hActive : ∀ᶠ z in 𝓝[C] p, z ∈ (c.dom : Set ℂ)) :
    ∃ ε > 0, extHullSet C F ∩ ball p ε = extHullSet C ∅ ∩ ball p ε := by
  obtain ⟨ε, hε, hSub⟩ := Metric.mem_nhdsWithin_iff.1 hActive
  refine ⟨ε, hε, Set.Subset.antisymm ?_ ?_⟩
  · rintro z ⟨⟨hzH, hzC | hzF⟩, hzball⟩
    · exact ⟨⟨hzH, Or.inl hzC⟩, hzball⟩
    · have hzC : z ∉ C := by
        intro hzC
        have hmem := hSub ⟨hzball, hzC⟩
        rw [hDomain] at hmem
        exact hmem.2.2 hzF
      exact ⟨⟨hzH, Or.inl hzC⟩, hzball⟩
  · rintro z ⟨⟨hzH, hzC | hzEmpty⟩, hzball⟩
    · exact ⟨⟨hzH, Or.inl hzC⟩, hzball⟩
    · exact hzEmpty.elim

/-- The initial normalized filling is always smaller than its current
version, including outside its own candidate event. -/
theorem eventFilled_initial_subset {Ω : Type*} (M : Set Ω) (C F : Ω → Set ℂ) (ω : Ω) :
    eventFilled M C (fun _ => ∅) ω ⊆ eventFilled M C F ω := by
  by_cases hω : ω ∈ M
  · simp only [eventFilled, hω, ↓reduceIte]
    rintro z ⟨hzH, hzC | hzEmpty⟩
    · exact ⟨hzH, Or.inl hzC⟩
    · exact hzEmpty.elim
  · simp only [eventFilled, hω, ↓reduceIte, subset_refl]

end InteractingSLE.Sec7.PocketStopSide
