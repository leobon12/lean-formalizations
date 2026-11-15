/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndPasting
import Mathlib.MeasureTheory.Group.Measure

/-!
# Original-clock adaptedness and time regularity

Packet PROVE-ZHAN-GT4-A22. Pull shifted adapted coefficients back to the
original filtration and transport their almost-everywhere left continuity
using translation invariance of Lebesgue measure.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov LP.LP4HB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {c : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0}

/-- The returned coefficient is adapted to the original filtration. -/
theorem seedEndCoef_adapted (hc : StronglyAdapted (shiftFiltration 𝓕 ε) c) :
    StronglyAdapted 𝓕 (seedEndCoef ε c) := by
  intro r
  by_cases hr : ε ≤ r
  · have hh := hc (r - ε)
    change StronglyMeasurable[𝓕 (ε + (r - ε))] (c (r - ε)) at hh
    rw [add_tsub_cancel_of_le hr] at hh
    have he : seedEndCoef ε c r = c (r - ε) := by
      funext ω
      exact ite_eq_left hr
    rw [he]
    exact hh
  · have he : seedEndCoef ε c r = fun _ => 0 := by
      funext ω
      exact ite_eq_right hr
    rw [he]
    exact stronglyMeasurable_const

/-- Riemann regularity survives return to the original clock. The
possible jump at the deterministic restart is a null time exception. -/
theorem seedEndCoef_isRiemannRegular (hc : IsRiemannRegular P c) :
    IsRiemannRegular P (seedEndCoef ε c) := by
  filter_upwards [hc] with ω hω
  have hh : ∀ᵐ r ∂(volume : Measure ℝ),
      ContinuousWithinAt (fun s => c s ω) (Iic (r - (ε : ℝ)).toNNReal) (r - (ε : ℝ)).toNNReal :=
    (eventually_sub_right_iff (volume : Measure ℝ) (ε : ℝ)).2 hω
  filter_upwards [hh, ae_ne_real ε] with r hr hne
  rcases le_or_gt r 0 with h0 | h0
  · have he : Iic r.toNNReal = {r.toNNReal} := by
      simp only [Real.toNNReal_of_nonpos h0]
      ext u
      simp only [mem_Iic, nonpos_iff_eq_zero, mem_singleton_iff]
    rw [he]
    exact continuousWithinAt_singleton
  · have hu : (r.toNNReal : ℝ) = r := Real.coe_toNNReal _ h0.le
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt' : r.toNNReal < ε := by exact_mod_cast hu.trans_lt hlt
      have hz : ∀ v ∈ Iic r.toNNReal, seedEndCoef ε c v ω = 0 := fun v hv =>
        ite_eq_right (not_le_of_gt (hv.trans_lt hlt'))
      exact (continuousWithinAt_const (b := (0 : ℝ))).congr hz (hz _ (mem_Iic.2 le_rfl))
    · have hgt' : ε < r.toNNReal := by exact_mod_cast hgt.trans_eq hu.symm
      have ht : (r - (ε : ℝ)).toNNReal = r.toNNReal - ε := by
        apply NNReal.coe_injective
        rw [Real.coe_toNNReal _ (sub_nonneg.2 hgt.le), NNReal.coe_sub hgt'.le, hu]
      rw [ht] at hr
      have hcc : ContinuousWithinAt (fun v : ℝ≥0 => c (v - ε) ω) (Iic r.toNNReal) r.toNNReal :=
        ContinuousWithinAt.comp (g := fun u : ℝ≥0 => c u ω) (f := fun v : ℝ≥0 => v - ε)
          hr (show Continuous (fun v : ℝ≥0 => v - ε) from
            continuous_id.sub continuous_const).continuousWithinAt
          (fun v hv => tsub_le_tsub_right (mem_Iic.1 hv) ε)
      apply hcc.congr_of_eventuallyEq
      · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hgt')] with v hv
        exact ite_eq_left (mem_Ioi.1 hv).le
      · exact ite_eq_left hgt'.le

end InteractingSLE.ZhanGT4
