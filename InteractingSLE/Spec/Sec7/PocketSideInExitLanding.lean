/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFinite

/-!
# Finite real inverse landings lie on the current frontier

PROVE-POCKET-SIDEIN. A conformal chart's inverse cannot land at an interior
domain point on a real access. The actual canonical original-visit landing
therefore lies on the current physical frontier.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

/-- The inverse of a conformal chart cannot land in its own open domain
when its coordinate approaches the real boundary from H. -/
theorem inverse_real_landing_notMem_dom {c : Chart} (hc : c.IsConformal)
    {x : ℝ} {p : ℂ} (hLanding : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) :
    p ∉ c.dom := by
  intro hp
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  have hi : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝[(c.dom : Set ℂ)] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hLanding,
      eventually_nhdsWithin_of_forall fun _ hz => hc.inv_mem_dom hz⟩
  have hforward := (hc.differentiableOn_fwd.continuousOn p hp).tendsto.comp hi
  have hid : Tendsto (fun z => c.1 (c.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) :=
    (show Tendsto (fun z : ℂ => z) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) from
      nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun z hz => (hc.2.2 z hz).symm)
  have he := tendsto_nhds_unique hforward hid
  have hpos := hc.fwd_mem hp
  rw [he] at hpos
  simp [H] at hpos

/-- Every finite real inverse landing is on the physical frontier. -/
theorem inverse_real_landing_mem_frontier {c : Chart} (hc : c.IsConformal)
    {x : ℝ} {p : ℂ} (hLanding : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) :
    p ∈ frontier (c.dom : Set ℂ) := by
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  rw [c.dom.isOpen.frontier_eq]
  exact ⟨isClosed_closure.mem_of_tendsto hLanding
    (eventually_nhdsWithin_of_forall fun _ hz => subset_closure (hc.inv_mem_dom hz)),
    inverse_real_landing_notMem_dom hc hLanding⟩

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketStopField

variable {Ω : Type} [MeasurableSpace Ω]

/-- The canonical original-visit landing is on the actual current frontier,
including visits in either initial pocket shape. -/
theorem currentVisitLanding_mem_current_frontier {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) (x : ℝ) :
    j.currentVisitLanding i d ω t x ∈ frontier
      ((j.target i d).domain ω ∩
        (H \ QuantumZipper.fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t)) := by
  have hc := (isDomainChart_relChart_visitCapacity hj hRc hLc hω ht hvisit).1
  have hf := inverse_real_landing_mem_frontier hc
    (tendsto_currentVisitLanding hj hRc hLc hω ht hvisit x)
  rwa [relChart_dom_visitCapacity hj hRc hLc hω ht hvisit] at hf

end InteractingSLE.Wire.Current.SideTest
