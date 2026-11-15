/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInActCollar

/-!
# An old incident collar survives a separated trace increment

PROVE-POCKET-SIDEIN. The real access is required to be in the closure of
the current domain in the old coordinate. This supplies the active point
in the same incident half-disc. Connectedness then excludes a newly filled
component. No separation of the old filled hull in a physical ball is used.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- A separated increment and an incident access construct an unfilled
old-chart half-disc. The access condition selects the relevant fibre. -/
theorem exists_old_halfDisc_in_current_domain {old : Chart} (hOld : old.IsConformal)
    {C Γ₀ Γ₁ : Set ℂ}
    (hOldDomain : (old.dom : Set ℂ) = C ∩ (H \ fillH Γ₀))
    (hClosed : IsClosed (Γ₀ ∪ Γ₁)) {x : ℝ} {p : ℂ}
    (hLanding : Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 p))
    (hIncident : (x : ℂ) ∈ closure (old.1 '' (C ∩ (H \ fillH (Γ₀ ∪ Γ₁)))))
    {r : ℝ} (hr : 0 < r) (hTail : Disjoint Γ₁ (closedBall p r)) :
    ∃ d > 0,
      old.2.1 '' (H ∩ ball (x : ℂ) d) ⊆ ball p r ∧
      old.2.1 '' (H ∩ ball (x : ℂ) d) ⊆ C ∩ (H \ fillH (Γ₀ ∪ Γ₁)) ∧
      H ∩ ball (x : ℂ) d ⊆ old.1 '' (C ∩ (H \ fillH (Γ₀ ∪ Γ₁))) := by
  obtain ⟨d, hd, hBall⟩ := exists_incident_halfDisc_maps_into hLanding hr
  let V := H ∩ ball (x : ℂ) d
  let U := old.2.1 '' V
  have hCurrentOld : C ∩ (H \ fillH (Γ₀ ∪ Γ₁)) ⊆ (old.dom : Set ℂ) := by
    rw [hOldDomain]
    exact fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2 (fillH_mono subset_union_left h)⟩
  have hOldImage : U ⊆ (old.dom : Set ℂ) := by
    rintro z ⟨y, hy, rfl⟩
    exact hOld.inv_mem_dom hy.1
  have hAway : U ⊆ H \ closure (Γ₀ ∪ Γ₁) := by
    intro z hz
    have hzOld := hOldImage hz
    rw [hOldDomain] at hzOld
    refine ⟨hzOld.2.1, ?_⟩
    rw [hClosed.closure_eq]
    rintro (hz₀ | hz₁)
    · exact hzOld.2.2 (mem_fillH_of_mem_closure hzOld.2.1 (subset_closure hz₀))
    · exact disjoint_left.1 hTail hz₁ (ball_subset_closedBall (hBall hz))
  obtain ⟨y, ⟨z₀, hz₀, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 hIncident d hd
  have hyV : old.1 z₀ ∈ V := ⟨hOld.fwd_mem (hCurrentOld hz₀), by
    rw [mem_ball, dist_comm]
    exact hy⟩
  have hz₀U : z₀ ∈ U := by
    have he := hOld.inv_fwd (hCurrentOld hz₀)
    exact he ▸ mem_image_of_mem old.2.1 hyV
  have hU : IsPreconnected U :=
    (convex_H.inter (convex_ball (x : ℂ) d)).isPreconnected.image old.2.1
      (hOld.1.continuousOn.mono inter_subset_left)
  have hUnfilled := collar_subset_compl_fillH hU hAway hz₀U hz₀.2
  have hImage : U ⊆ C ∩ (H \ fillH (Γ₀ ∪ Γ₁)) := by
    intro z hz
    have hzOld := hOldImage hz
    rw [hOldDomain] at hzOld
    exact ⟨hzOld.1, hUnfilled hz⟩
  refine ⟨d, hd, hBall, hImage, ?_⟩
  intro y hyV
  exact ⟨old.2.1 y, hImage (mem_image_of_mem old.2.1 hyV), hOld.2.2 y hyV.1⟩

end InteractingSLE.Sec7.PocketStopSide
