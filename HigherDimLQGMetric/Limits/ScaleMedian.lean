import HigherDimLQGMetric.Limits.Median
import HigherDimLQGMetric.Metric.ContMetric
import HigherDimLQGMetric.Sphere.Cont

/-!
# Positivity of the canonical scale normalizer

The corrected Lemma 3.7 uses the lower median of a positive rescaled point
distance.  This file proves its measurability and positivity on any probability
space carrying a measurable continuous metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- The scale-`r` point distance, before median normalization, is measurable. -/
theorem l6c_measurable_scalePoint {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ξ r : ℝ) (h : Ω → DistRd d) (hh : Measurable h)
    (Dh : Ω → ContMetric d) (hDh : Measurable Dh) :
    Measurable (fun ω =>
      Real.exp (-ξ * sphereAvg (h ω) r 0) * (Dh ω).1 (0, r • e₁ d)) := by
  have hs : Measurable (fun ω => sphereAvg (h ω) r 0) :=
    (measurable_sphereAvg_left r 0).comp hh
  have hD : Measurable (fun ω => (Dh ω).1 (0, r • e₁ d)) :=
    (continuous_eval_const _).measurable.comp
      (measurable_subtype_coe.comp hDh)
  exact (Real.measurable_exp.comp (measurable_const.mul hs)).mul hD

/-- For positive `r`, the scale-`r` point distance is strictly positive. -/
theorem l6c_scalePoint_pos {d : ℕ} (hd : 0 < d) (ξ : ℝ) {r : ℝ} (hr : 0 < r)
    (h : DistRd d) (D : ContMetric d) :
    0 < Real.exp (-ξ * sphereAvg h r 0) * D.1 (0, r • e₁ d) := by
  have he : r • e₁ d ≠ 0 := smul_ne_zero hr.ne' (HigherDimLFPP.e₁_ne_zero hd)
  exact mul_pos (Real.exp_pos _) (D.apply_pos (Ne.symm he))

/-- The canonical lower-median scale normalizer is positive. -/
theorem l6c_scaleMedian_pos {d : ℕ} (hd : 0 < d) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : Measurable h)
    (Dh : Ω → ContMetric d) (hDh : Measurable Dh)
    {r : ℝ} (hr : 0 < r) :
    0 < lowerMedian P (fun ω =>
      Real.exp (-ξ * sphereAvg (h ω) r 0) * (Dh ω).1 (0, r • e₁ d)) := by
  exact l6c_lowerMedian_pos
    (l6c_measurable_scalePoint ξ r h hh Dh hDh).aemeasurable
    (Filter.Eventually.of_forall fun ω => l6c_scalePoint_pos hd ξ hr (h ω) (Dh ω))

end HigherDimLQGMetric
