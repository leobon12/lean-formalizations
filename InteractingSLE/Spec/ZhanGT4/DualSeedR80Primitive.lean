/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalTView

/-!
# Adapted entrance integrals for the actual image drift

Packet PROVE-ZHAN-GT4-A22. Positive-time continuity gives a progressive
stopped rate. Its primitive is adapted without a boundedness assumption.
Entrance integrability then permits evaluation at the actual stopping
horizon, rather than replacement by an almost-everywhere integral version.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Entrance-integrable positive-time rates have adapted stopped primitives.
No global bound on the rate or continuity of its entrance value is needed. -/
theorem measurable_stopped_seed_primitive {𝓕 : Filtration ℝ≥0 mΩ}
    {S : Ω → ℝ≥0} {g : Ω → ℝ → ℝ}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hm : ∀ u : ℝ≥0, Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => g ω u))
    (hc : ∀ ω, ContinuousOn (fun u : ℝ≥0 => g ω u) (Ioc 0 (S ω)))
    (hi : ∀ ω, IntervalIntegrable (g ω) volume 0 (S ω)) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => ∫ u in (0 : ℝ)..(min t (S ω) : ℝ≥0), g ω u := by
  have hp := (isStronglyPredictable_positiveStopped 𝓕 hm hc).isStronglyProgressive
  have hprim (u : ℝ≥0) : Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => ∫ r in (0 : ℝ)..(u : ℝ), g ω r) := by
    have hh := (Girsanov.stronglyMeasurable_integral_comp hp measurable_id u).measurable
    have hE : MeasurableSet[𝓕 u] {ω | u ≤ S ω} := measurableSet_ge_of_isStoppingTime hS u
    convert hh.indicator hE using 1
    funext ω
    by_cases hω : u ≤ S ω
    · simp only [indicator_of_mem (show ω ∈ {ω | u ≤ S ω} from hω)]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with r hr
      rw [uIoc_of_le u.coe_nonneg] at hr
      have hr0 : 0 < r.toNNReal := Real.toNNReal_pos.2 hr.1
      have hrS : r.toNNReal ≤ S ω := Real.toNNReal_le_iff_le_coe.2
        (hr.2.trans (NNReal.coe_le_coe.2 hω))
      simp only [positiveStopped, hr0, hrS, and_self, ite_true,
        Real.coe_toNNReal _ hr.1.le, id_eq]
    · simp only [indicator_of_notMem (show ω ∉ {ω | u ≤ S ω} from hω)]
  have hcont (ω : Ω) : ContinuousOn (fun s => ∫ r in (0 : ℝ)..s, g ω r) (Icc 0 (S ω)) := by
    simpa only [uIcc_of_le (S ω).coe_nonneg] using
      intervalIntegral.continuousOn_primitive_interval' (hi ω) left_mem_uIcc
  exact measurable_stopped_of_indicator hS hprim hcont t

end InteractingSLE.ZhanGT4
