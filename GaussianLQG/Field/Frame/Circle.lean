import GaussianLQG.Core.Defs
import GaussianLQG.Energy.Measures
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# The uniform measure on the unit circle (blueprint Appendix B, `lem:heat`(c))

Facts about `σ = circleMeasure 0 1` used in the white-noise frame construction. That `σ_{z,r}` is
a probability measure and that `∫ f dσ_{z,r} = Real.circleAverage f z r` are
`GaussianLQG.isProbabilityMeasure_circleMeasure` and `GaussianLQG.integral_circleMeasure`
(`GaussianLQG/Energy/Measures.lean`).

* `circleMeasure_apply`, `circleMeasure_real_univ`: the formula for `σ_{z,r}(s)`, and
  `σ_{z,r}(ℂ) = 1`;
* `circleMeasure_singleton`: `σ_{z,r}` has no atoms (`r ≠ 0`);
* `circleMeasure_compl_closedBall`: `σ` is carried by the closed unit disc;
* `integrable_log_norm_sub_circleMeasure`, `integral_log_norm_sub_circleMeasure`:
  `∫ log|u − v| σ(dv) = log⁺|u|` (Mathlib `circleAverage_log_norm_sub_const_eq_posLog`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Real

namespace GaussianLQG
namespace WNFrame

lemma circleMeasure_apply (z : ℂ) (r : ℝ) {s : Set ℂ} (hs : MeasurableSet s) :
    circleMeasure z r s = ENNReal.ofReal (2 * π)⁻¹ *
      volume (Ioc (0 : ℝ) (2 * π) ∩ circleMap z r ⁻¹' s) := by
  unfold circleMeasure
  rw [Measure.map_apply (measurable_circleMap z r) hs, Measure.smul_apply,
    Measure.restrict_apply ((measurable_circleMap z r) hs), smul_eq_mul, inter_comm]

lemma circleMeasure_real_univ (z : ℂ) (r : ℝ) : (circleMeasure z r).real univ = 1 := by
  simp

/-- `σ_{z,r}` has no atoms. -/
lemma circleMeasure_singleton (z : ℂ) {r : ℝ} (hr : r ≠ 0) (u : ℂ) :
    circleMeasure z r {u} = 0 := by
  rw [circleMeasure_apply z r (measurableSet_singleton u)]
  have h0 : volume (circleMap z r ⁻¹' {u}) = 0 :=
    ((countable_singleton u).preimage_circleMap z hr).measure_zero _
  rw [measure_mono_null inter_subset_right h0, mul_zero]

lemma ae_circleMeasure_mem_sphere (z : ℂ) (r : ℝ) :
    ∀ᵐ u ∂(circleMeasure z r), u ∈ Metric.sphere z |r| := by
  rw [ae_iff]
  show circleMeasure z r (Metric.sphere z |r|)ᶜ = 0
  rw [circleMeasure_apply z r Metric.isClosed_sphere.measurableSet.compl]
  have : circleMap z r ⁻¹' (Metric.sphere z |r|)ᶜ = ∅ := by
    ext θ; simp
  rw [this, inter_empty, measure_empty, mul_zero]

lemma circleMeasure_compl_closedBall : circleMeasure 0 1 (Metric.closedBall (0 : ℂ) 1)ᶜ = 0 := by
  rw [circleMeasure_apply 0 1 Metric.isClosed_closedBall.measurableSet.compl]
  have : circleMap 0 1 ⁻¹' (Metric.closedBall (0 : ℂ) 1)ᶜ = ∅ := by
    ext θ; simp [circleMap_mem_closedBall (0 : ℂ) zero_le_one θ]
  rw [this, inter_empty, measure_empty, mul_zero]

/-- `v ↦ log|u − v|` is `σ`-integrable. -/
lemma integrable_log_norm_sub_circleMeasure (u : ℂ) :
    Integrable (fun v => Real.log ‖u - v‖) (circleMeasure 0 1) := by
  have hm : Measurable fun v : ℂ => Real.log ‖u - v‖ := by fun_prop
  have hci : CircleIntegrable (fun v : ℂ => Real.log ‖v - u‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  unfold circleMeasure
  rw [integrable_map_measure hm.aestronglyMeasurable (measurable_circleMap 0 1).aemeasurable]
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  have h1 := hci.1
  refine h1.congr_fun (fun θ _ => ?_) measurableSet_Ioc
  simp only [Function.comp_apply, norm_sub_rev]

/-- `∫ log|u − v| σ(dv) = log⁺|u|`. -/
lemma integral_log_norm_sub_circleMeasure (u : ℂ) :
    ∫ v, Real.log ‖u - v‖ ∂(circleMeasure 0 1) = Real.posLog ‖u‖ := by
  rw [integral_circleMeasure 0 1 (by fun_prop : Measurable fun v : ℂ =>
    Real.log ‖u - v‖).aestronglyMeasurable]
  have e : (fun v : ℂ => Real.log ‖u - v‖) = fun v => Real.log ‖v - u‖ := by
    funext v; rw [norm_sub_rev]
  rw [e, circleAverage_log_norm_sub_const_eq_posLog]

/-! ## Compatibility names (cleanup W15)

Old names of facts that now come from `GaussianLQG/Energy/Measures.lean` and Mathlib, kept so that
code written against them still compiles. They are `protected`, so inside `GaussianLQG.WNFrame` the
short names still refer to the general versions. -/

protected alias measurable_circleMap := _root_.measurable_circleMap

protected alias isProbabilityMeasure_circleMeasure :=
  GaussianLQG.isProbabilityMeasure_circleMeasure

protected theorem integral_circleMeasure (z : ℂ) (r : ℝ) {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f (circleMeasure z r)) :
    ∫ u, f u ∂(circleMeasure z r) = Real.circleAverage f z r :=
  GaussianLQG.integral_circleMeasure z r hf

end WNFrame
end GaussianLQG
