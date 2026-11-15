/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TsBoundary

/-!
# Common-time nesting from the central target components

PROVE-R6-TWO, Astra §2.4 (R98). A common driver collar fixes the same
component for both nested pockets. Other surviving outer components
are allowed throughout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R6Ts

open Sec6

/-- Component maximality for nested pockets, after one common active
point has fixed the incident component. -/
theorem components_nested_of_intersection {P C D : Set ℂ} (hPC : P ⊆ C) {i o : ℂ}
    (hinter : (connectedComponentIn (P ∩ D) i ∩ connectedComponentIn (C ∩ D) o).Nonempty) :
    connectedComponentIn (P ∩ D) i ⊆ connectedComponentIn (C ∩ D) o := by
  obtain ⟨z, hzI, hzO⟩ := hinter
  rw [connectedComponentIn_eq hzI, connectedComponentIn_eq hzO]
  exact connectedComponentIn_mono _ (inter_subset_inter_left _ hPC)

/-- Once the ambient faces are identified with surviving components,
their driver collars prove both physical and chart-domain nesting.
Neither whole surviving pocket is assumed connected. -/
theorem faces_nested_of_driver_collars
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {P C F G : Set ℂ} (hPC : P ⊆ C) (hFH : F ⊆ H) (hGH : G ⊆ H)
    {i o : ℂ}
    (hinner : trMap W 0 t '' F = connectedComponentIn (P ∩ (H \ fwdHull W t)) i)
    (houter : trMap W 0 t '' G = connectedComponentIn (C ∩ (H \ fwdHull W t)) o)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hF : H ∩ ball (0 : ℂ) r ⊆ F) (hG : H ∩ ball (0 : ℂ) s ⊆ G) :
    trMap W 0 t '' F ⊆ trMap W 0 t '' G ∧ F ⊆ G := by
  have hzero : (0 : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact show 0 ≤ (0 : ℂ).im from le_rfl
  obtain ⟨z, hzH, hzd⟩ := Metric.mem_closure_iff.1 hzero (min r s) (lt_min hr hs)
  have hzF : z ∈ F := hF ⟨hzH, mem_ball.2 (by
    rw [dist_comm]; exact hzd.trans_le (min_le_left _ _))⟩
  have hzG : z ∈ G := hG ⟨hzH, mem_ball.2 (by
    rw [dist_comm]; exact hzd.trans_le (min_le_right _ _))⟩
  have hzI : trMap W 0 t z ∈ connectedComponentIn (P ∩ (H \ fwdHull W t)) i :=
    hinner ▸ ⟨z, hzF, rfl⟩
  have hzO : trMap W 0 t z ∈ connectedComponentIn (C ∩ (H \ fwdHull W t)) o :=
    houter ▸ ⟨z, hzG, rfl⟩
  have hphysical : trMap W 0 t '' F ⊆ trMap W 0 t '' G := by
    rw [hinner, houter]
    exact components_nested_of_intersection hPC ⟨trMap W 0 t z, hzI, hzO⟩
  refine ⟨hphysical, fun w hw => ?_⟩
  obtain ⟨v, hv, hvw⟩ := hphysical ⟨w, hw, rfl⟩
  have hveq : v = w := by
    have heq := congrArg (fwdMap W t) hvw
    rwa [fwdMap_trMap_zero hW hW0 ht (hGH hv), fwdMap_trMap_zero hW hW0 ht (hFH hw)] at heq
  exact hveq ▸ hv

end InteractingSLE.Sec7.R6Ts
