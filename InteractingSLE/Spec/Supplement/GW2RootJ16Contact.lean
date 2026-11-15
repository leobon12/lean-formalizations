/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Restart

/-!
# Positive pre-contact horizon for finite generating traces

Packet PROVE-T14-GW2ROOT2. At time zero, continuity before a positive
physical lifetime suffices for the landed compact-set first-contact
theorem. The retained chart trace is compact before its own lifetime.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ16

open Supp8.GB6

/-- The actual first-contact horizon, cut off at the physical lifetime,
is positive for two finite generating traces with a live chart stop. -/
theorem precontact_horizon_pos {wα w : ℝ≥0 → ℝ} {Tα T : ℝ≥0∞}
    {α γ : ℝ≥0 → ℂ} (hα : IsGeneratingTrace wα Tα α)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < Tα)
    (hγ : IsGeneratingTrace w T γ) (hT : 0 < T) :
    0 < min
      (firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) T := by
  have hN : {t : ℝ≥0 | (t : ℝ≥0∞) < T} ∈ 𝓝 0 :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds
      (show ((0 : ℝ≥0) : ℝ≥0∞) < T by simpa only [ENNReal.coe_zero] using hT)
  have hc : ContinuousOn γ {t : ℝ≥0 | (t : ℝ≥0∞) < T} :=
    hγ.2.1.mono fun t ht =>
      show (t : ℝ≥0∞) ≤ T from (show (t : ℝ≥0∞) < T from ht).le
  have hγ0 : ContinuousAt γ 0 := hc.continuousAt hN
  have hk : IsCompact (α '' Icc 0 s) := isCompact_Icc.image_of_continuousOn
    (hα.2.1.mono fun t ht => (ENNReal.coe_le_coe.mpr ht.2).trans hs.le)
  have hC := firstContactTime_pos hγ0 hγ.1 hk.isBounded
  rw [image_image] at hC
  exact lt_min hC hT

end InteractingSLE.Theorem14.GW2TipSystem.RootJ16
