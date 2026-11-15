/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqInf
import InteractingSLE.Spec.Sec6.Aux31Outer
import InteractingSLE.Foundations.Topology.Schoenflies.Plane

/-!
# The forbidden-side collar from local connectivity

PROVE-R7-GAPEQ continuation. The exterior of a Jordan pocket is locally connected at its
boundary. If the forbidden side's frontier near an outer point lies in the closed pocket,
its exterior relative neighborhood lies entirely in the forbidden side. This supplies the
actual `HasExteriorCollar`, rather than taking that predicate as an input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology

namespace InteractingSLE.Sec7.R7GapEqFin

open Sec6 R7GapEq

/-- Local exterior connectivity and the location of the forbidden frontier imply the collar
used to exclude strict outer gap endpoints. Only a local frontier inclusion is required. -/
theorem hasExteriorCollar_of_locConn {C F K : Set ℂ} {p : ℂ}
    (hCo : IsOpen C) (hFo : IsOpen F) (hCF : Disjoint C F)
    (hfrK : frontier C ⊆ K) (hpF : p ∈ closure F)
    (hloc : IsLocConnWithin (closure C)ᶜ p)
    (hfr : ∃ ε > 0, frontier F ∩ ball p ε ⊆ closure C) :
    HasExteriorCollar C F K p := by
  obtain ⟨ε, hε, hfr⟩ := hfr
  have hFD : F ⊆ (closure C)ᶜ := fun z hz hzc =>
    Set.disjoint_left.1 (hCF.closure_left hFo) hzc hz
  obtain ⟨S, hS, hSc, hSN⟩ := hloc ε hε
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhdsWithin_iff.1 hSN
  have hSF : (S ∩ F).Nonempty := by
    obtain ⟨z, hz, hzp⟩ := Metric.mem_closure_iff.1 hpF δ hδ
    exact ⟨z, hδS ⟨by rwa [mem_ball, dist_comm], hFD hz⟩, hz⟩
  have hSfr : Disjoint S (frontier F) := Set.disjoint_left.2 fun z hz hzfr =>
    (hS hz).1 (hfr ⟨hzfr, (hS hz).2⟩)
  have hSin : S ⊆ F := subset_of_isPreconnected_of_disjoint_frontier hSc hFo hSF hSfr
  refine ⟨ball p δ, isOpen_ball, mem_ball_self hδ, fun z hz => ?_⟩
  by_cases hzc : z ∈ closure C
  · by_cases hzC : z ∈ C
    · exact Or.inl (Or.inl hzC)
    · exact Or.inr (hfrK ⟨hzc, by rwa [hCo.interior_eq]⟩)
  · exact Or.inl (Or.inr (hSin (hδS ⟨hz, hzc⟩)))

end InteractingSLE.Sec7.R7GapEqFin
