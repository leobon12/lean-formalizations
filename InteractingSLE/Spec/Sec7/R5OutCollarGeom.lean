/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutRef
import InteractingSLE.Spec.Sec7.PocketSideInTailGeometry

/-!
# Incident collars from a separated component frontier

Connectedness keeps a small old inverse half-disc in the current component.
Only the frontier inside the old chart must miss the physical ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.R5Out

open PocketStopSide

/-- The frontier of a charted relative complement, inside the initial pocket,
lands on the frontier of the coordinate complement. -/
theorem mem_frontier_of_mem_frontier_inter_preimage {C D : Set ℂ} {ψ : ℂ → ℂ}
    (hCo : IsOpen C) (hψ : ContinuousOn ψ C) (hD : IsOpen D) {p : ℂ} (hpC : p ∈ C)
    (hp : p ∈ frontier (C ∩ ψ ⁻¹' D)) : ψ p ∈ frontier D := by
  have hcl : ψ p ∈ closure D :=
    ((hψ p hpC).mono inter_subset_left).mem_closure hp.1 (fun _ hz => hz.2)
  rw [(hψ.isOpen_inter_preimage hCo hD).frontier_eq] at hp
  rw [hD.frontier_eq]
  exact ⟨hcl, fun hpD => hp.2 ⟨hpC, hpD⟩⟩

/-- An old incident inverse half-disc survives if the current frontier inside
the old chart avoids a physical ball about its landing. -/
theorem exists_old_halfDisc_in_current_component {old now : Chart}
    (hOld : old.IsConformal) (hNested : (now.dom : Set ℂ) ⊆ old.dom)
    {x : ℝ} {p : ℂ}
    (hLanding : Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 p))
    (hIncident : (x : ℂ) ∈ closure (old.1 '' (now.dom : Set ℂ)))
    {r : ℝ} (hr : 0 < r)
    (hFrontier : Disjoint (frontier (now.dom : Set ℂ) ∩ (old.dom : Set ℂ))
      (ball p r)) :
    ∃ d > 0, old.2.1 '' (H ∩ ball (x : ℂ) d) ⊆ (now.dom : Set ℂ) := by
  obtain ⟨d, hd, hBall⟩ := exists_incident_halfDisc_maps_into hLanding hr
  let U := old.2.1 '' (H ∩ ball (x : ℂ) d)
  have hUOld : U ⊆ (old.dom : Set ℂ) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hOld.inv_mem_dom hy.1
  obtain ⟨_, ⟨z, hz, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 hIncident d hd
  have hzU : z ∈ U := by
    have he := hOld.inv_fwd (hNested hz)
    exact he ▸ mem_image_of_mem old.2.1
      ⟨hOld.fwd_mem (hNested hz), by rwa [mem_ball, dist_comm]⟩
  have hU : IsPreconnected U :=
    (convex_H.inter (convex_ball (x : ℂ) d)).isPreconnected.image old.2.1
      (hOld.1.continuousOn.mono inter_subset_left)
  refine ⟨d, hd, hU.subset_of_closure_inter_subset now.dom.isOpen ⟨z, hzU, hz⟩ ?_⟩
  intro y hy
  by_contra hyn
  have hyfr : y ∈ frontier (now.dom : Set ℂ) := by
    rw [now.dom.isOpen.frontier_eq]
    exact ⟨hy.1, hyn⟩
  exact disjoint_left.1 hFrontier ⟨hyfr, hUOld hy.2⟩ (hBall hy.2)

end InteractingSLE.Sec7.R5Out
