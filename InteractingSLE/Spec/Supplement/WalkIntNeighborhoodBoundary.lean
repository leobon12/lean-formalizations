/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntNeighborhoodCore

/-!
# A physical frontier collar supplies a common incident coordinate

The component inverse already has a continuous boundary extension.
A frontier neighborhood covered by the retained raw closure and real
line therefore places the anchor inside its supported coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntNeighborhood

/-- Restrict the existing continuous inverse extension to real coordinates. -/
theorem continuous_real_invExt {R L C : Set ℂ} {c : Chart}
    (hchart : IsComponentChart R L C c) (hCo : IsOpen C) :
    Continuous (fun x : ℝ => GW4Traverse.invExt c (x : ℂ)) :=
  (GW4Traverse.continuousOn_invExt hchart hCo).comp_continuous
    Complex.continuous_ofReal (fun x => by simp only [Hbar, mem_ofPred_eq, ofReal_im, le_refl])

/-- Every finite real coordinate lands on the physical frontier of the
component chart. No injectivity of the boundary extension is needed. -/
theorem invExt_real_mem_frontier {R L C : Set ℂ} {c : Chart}
    (hchart : IsComponentChart R L C c) (hCo : IsOpen C) (hc : c.IsConformal) (x : ℝ) :
    GW4Traverse.invExt c (x : ℂ) ∈ frontier (c.dom : Set ℂ) := by
  have hx : (x : ℂ) ∈ Hbar := by simp only [Hbar, mem_ofPred_eq, ofReal_im, le_refl]
  have hlim := GW4Traverse.tendsto_invExt hchart hCo hx
  let _ := GW1P.neBot_nhdsWithin_H hx
  rw [c.dom.isOpen.frontier_eq]
  exact ⟨mem_closure_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun z hz => hc.inv_mem_dom hz),
    Sec7.PocketStopSide.inverse_real_landing_notMem_dom hc hlim⟩

/-- A physical collar at the anchor makes it an interior supported landing
coordinate. This is the sole local coverage input for the interval builder. -/
theorem anchor_mem_interior_of_frontier_collar {R L C F : Set ℂ} {c : Chart}
    (hchart : IsComponentChart R L C c) (hCo : IsOpen C) (hc : c.IsConformal)
    {anchor r : ℝ} (hr : 0 < r)
    (hcover : frontier (c.dom : Set ℂ) ∩
      ball (GW4Traverse.invExt c (anchor : ℂ)) r ⊆ closure F ∪ {z : ℂ | z.im = 0}) :
    anchor ∈ interior (landingCoordinates c F) := by
  have hopen : IsOpen ((fun x : ℝ => GW4Traverse.invExt c (x : ℂ)) ⁻¹'
      ball (GW4Traverse.invExt c (anchor : ℂ)) r) :=
    isOpen_ball.preimage (continuous_real_invExt hchart hCo)
  apply mem_interior_iff_mem_nhds.2
  apply Filter.mem_of_superset (hopen.mem_nhds (mem_ball_self hr))
  intro x hx
  exact hcover ⟨invExt_real_mem_frontier hchart hCo hc x, hx⟩

/-- The canonical interval carries the physical landing and its inverse
limit at every coordinate, including real landing values. -/
theorem landing_of_mem_interval {R L C F : Set ℂ} {c : Chart}
    (hchart : IsComponentChart R L C c) (hCo : IsOpen C) {anchor x : ℝ}
    (hx : x ∈ incidentInterval c F anchor) :
    ∃ p : ℂ, (p ∈ closure F ∨ p.im = 0) ∧
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) :=
  ⟨GW4Traverse.invExt c (x : ℂ), mem_landingCoordinates_of_mem_interval hx,
    GW4Traverse.tendsto_invExt hchart hCo
      (by simp only [Hbar, mem_ofPred_eq, ofReal_im, le_refl])⟩

end InteractingSLE.Theorem14.WalkIntNeighborhood
