/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QrBase
import InteractingSLE.Spec.Supplement.SBS3MarkedRecenter

/-!
# A chart transport in a run chart is a chart transport in the canonical hull chart

Worker REVIEW-FABLE-T14 (the retained law in the canonical hull chart; orchestrator split of PROVE-SB2-LCMEAN's
handoff R13.8, items 2–3).

A normalized chart `c` with a hull model `M` (`dom c = ℍ ∖ hull`, `c + shift` the map-out of the hull) is the canonical
hull chart of `M.hull` recentred by the shift: forward maps, inverses and lifts agree (the lift by the normalization at
`i∞`, `WalkIntCanon.HullModel.lift_eq_canonDerivLog`). So a chart transport in `c` becomes one in the canonical hull
chart, with the field translated by the shift:

* `image_inv_recenter`: recentring does not change the domain;
* **`isChartTransport_hullChart_of_hullModel`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.SB.Qt

open Restart Exist

/-- Recentring a chart does not change its domain. -/
theorem image_inv_recenter (c : Chart) (a : ℝ) : (c.recenter a).2.1 '' H = c.2.1 '' H := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y + a, ?_, rfl⟩
    have hy' : 0 < y.im := hy
    show 0 < (y + (a : ℂ)).im
    simpa using hy'
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w - a, ?_, ?_⟩
    · have hw' : 0 < w.im := hw
      show 0 < (w - (a : ℂ)).im
      simpa using hw'
    · show c.2.1 (w - (a : ℂ) + a) = c.2.1 w
      rw [sub_add_cancel]

/-- **A chart transport in a normalized chart with a hull model is a chart transport in the canonical hull chart**,
with the field translated by the hull model's shift. -/
theorem isChartTransport_hullChart_of_hullModel {c : Chart} (hcc : c.IsConformal)
    (hN : WalkIntCanon.IsNormalized c) (M : WalkIntCanon.HullModel c)
    (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H) {χ : ℝ} {h Y : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport c 1 0 χ h Y) :
    IsChartTransport (Mo.hullChart M.hull 0) 1 0 χ h (Exist.flowField (-M.shift) 0 Y) := by
  have ht' := S3.isChartTransport_recenter_word hcc hℓ ht (-M.shift)
  have hc' := Mo.isConformal_hullChart M.isHull 0
  have hmo : EqOn (ConformalImage.mapOut M.hull) (fun z => c.1 z + (M.shift : ℂ)) (H \ M.hull) :=
    (ConformalImage.isMapOut_mapOut M.isHull).eqOn M.isHull M.mapOut
  have hdom : c.2.1 '' H = H \ M.hull := by
    rw [← hcc.coe_dom]
    exact M.dom_eq
  have himg : (c.recenter (-M.shift)).2.1 '' H = H \ M.hull := by
    rw [image_inv_recenter, hdom]
  refine Sec5.CrossCond.Staged.isChartTransport_congr_dom (hcc.recenter _).isOpen_image ?_ ?_ ?_ ht'
  · intro y hy
    have hys : y - (M.shift : ℂ) ∈ H := by
      have hy' : 0 < y.im := hy
      show 0 < (y - (M.shift : ℂ)).im
      simpa using hy'
    have hz : c.2.1 (y - (M.shift : ℂ)) ∈ H \ M.hull := by
      rw [← hdom]
      exact mem_image_of_mem _ hys
    have hzd : c.2.1 (y - (M.shift : ℂ)) ∈ (Mo.hullChart M.hull 0).dom := by
      show c.2.1 (y - (M.shift : ℂ)) ∈ ((Mo.hullChart M.hull 0).dom : Set ℂ)
      rw [Mo.coe_dom_hullChart M.isHull 0]
      exact hz
    have hfwd : (Mo.hullChart M.hull 0).1 (c.2.1 (y - (M.shift : ℂ))) = y := by
      rw [Mo.hullChart_fwd, hmo hz]
      show c.1 (c.2.1 (y - (M.shift : ℂ))) + (M.shift : ℂ) - ((0 : ℝ) : ℂ) = y
      rw [hcc.2.2 _ hys]
      push_cast
      ring
    have e := hc'.inv_fwd hzd
    rw [hfwd] at e
    rw [e]
    show c.2.1 (y + ((-M.shift : ℝ) : ℂ)) = c.2.1 (y - (M.shift : ℂ))
    push_cast
    ring_nf
  · intro z hz
    rw [himg] at hz
    show c.1 z - ((-M.shift : ℝ) : ℂ) = (Mo.hullChart M.hull 0).1 z
    rw [Mo.hullChart_fwd, hmo hz]
    push_cast
    ring
  · intro z hz
    rw [himg] at hz
    show c.2.2 z = (Mo.hullChart M.hull 0).2.2 z
    rw [Mo.hullChart_lift]
    exact M.lift_eq_canonDerivLog hN hz

end InteractingSLE.Theorem14.SB.Qt
