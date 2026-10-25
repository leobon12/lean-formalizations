import LQGMetric.Field.CircleAvgProc
import LQGMetric.Papers.DFGPS.L3_4Tail
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Distributions.Gaussian.Real




 















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric (DistC IsWholePlaneGFF)
open LQGMetric.CircleAvg (circCov incCov circLog cInc)

 
theorem gaussianReal_upper_tail {v : ℝ≥0} (hv : 0 < (v : ℝ)) {x : ℝ} (hx : 0 ≤ x) :
    (gaussianReal 0 v).real {y : ℝ | x ≤ y} ≤ Real.exp (-x ^ 2 / (2 * v)) := by
  have hc := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) x
    (t := x / v) (div_nonneg hx hv.le) (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (x / v))
  have hm : mgf id (gaussianReal 0 v) (x / v) =
      Real.exp (0 * (x / v) + v * (x / v) ^ 2 / 2) :=
    congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) (x / v)
  rw [hm, ← Real.exp_add] at hc
  refine hc.trans_eq ?_
  congr 1
  field_simp
  ring

 
theorem gaussianReal_lower_tail {v : ℝ≥0} (hv : 0 < (v : ℝ)) {x : ℝ} (hx : 0 ≤ x) :
    (gaussianReal 0 v).real {y : ℝ | y ≤ -x} ≤ Real.exp (-x ^ 2 / (2 * v)) := by
  have hc := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) (-x)
    (t := -(x / v)) (neg_nonpos.2 (div_nonneg hx hv.le))
    (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-(x / v)))
  have hm : mgf id (gaussianReal 0 v) (-(x / v)) =
      Real.exp (0 * (-(x / v)) + v * (-(x / v)) ^ 2 / 2) :=
    congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) (-(x / v))
  rw [hm, ← Real.exp_add] at hc
  refine hc.trans_eq ?_
  congr 1
  field_simp
  ring

 

theorem gaussianReal_abs_tail {v : ℝ≥0} {V : ℝ} (hvV : (v : ℝ) ≤ V) {x : ℝ}
    (hx : 0 < x) :
    (gaussianReal 0 v) {y : ℝ | x ≤ |y|} ≤ ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * V))) := by
  rcases eq_or_ne v 0 with hv0 | hvne
  · rw [hv0, gaussianReal_zero_var, Measure.dirac_apply' _ (measurableSet_le measurable_const
      continuous_abs.measurable)]
    have : (0 : ℝ) ∉ {y : ℝ | x ≤ |y|} := by
      simp only [mem_ofPred_eq, abs_zero, not_le]
      exact hx
    rw [Set.indicator_of_notMem this]
    exact bot_le
  · have hv : 0 < (v : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hvne)
    have hsub : {y : ℝ | x ≤ |y|} ⊆ {y : ℝ | x ≤ y} ∪ {y : ℝ | y ≤ -x} := by
      intro y hy
      simp only [mem_ofPred_eq] at hy
      rcases le_abs'.1 hy with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hmono : Real.exp (-x ^ 2 / (2 * v)) ≤ Real.exp (-x ^ 2 / (2 * V)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (by linarith)
    have h1 := (gaussianReal_upper_tail hv hx.le).trans hmono
    have h2 := (gaussianReal_lower_tail hv hx.le).trans hmono
    calc (gaussianReal 0 v) {y : ℝ | x ≤ |y|}
        ≤ (gaussianReal 0 v) {y : ℝ | x ≤ y} + (gaussianReal 0 v) {y : ℝ | y ≤ -x} :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ = ENNReal.ofReal ((gaussianReal 0 v).real {y : ℝ | x ≤ y}) +
            ENNReal.ofReal ((gaussianReal 0 v).real {y : ℝ | y ≤ -x}) := by
          rw [ofReal_measureReal (measure_ne_top _ _), ofReal_measureReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * V))) +
            ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * V))) :=
          add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
      _ = ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * V))) := by
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
          congr 1
          ring

 
theorem circLog_add {s : ℝ} (hs : s ≠ 0) (w c u : ℂ) :
    circLog (w + c) s (u + c) = circLog w s u := by
  rw [LQGMetric.CircleAvg.circLog_eq hs, LQGMetric.CircleAvg.circLog_eq hs, add_sub_add_right_eq_sub]

 
theorem circCov_add (z w c : ℂ) (r : ℝ) {s : ℝ} (hs : s ≠ 0) :
    circCov (z + c) r (w + c) s = circCov z r w s := by
  unfold circCov
  rw [← Real.circleAverage_map_add_const (f := circLog (w + c) s) (c := z + c),
    ← Real.circleAverage_map_add_const (f := circLog w s) (c := z)]
  congr 1
  funext u
  rw [show u + (z + c) = (u + z) + c by ring, circLog_add hs]

 
theorem incCov_add (z w z' w' c : ℂ) {r s r' s' : ℝ} (hr' : r' ≠ 0) (hs' : s' ≠ 0) :
    incCov (z + c) r (w + c) s (z' + c) r' (w' + c) s' = incCov z r w s z' r' w' s' := by
  unfold incCov
  rw [circCov_add z z' c r hr', circCov_add z w' c r hs', circCov_add w z' c s hr',
    circCov_add w w' c s hs']

 

theorem incCov_le_of_far (w y : ℂ) {a s R : ℝ} (ha : 0 < a) (has : a ≤ s) (hR : 0 ≤ R)
    (hwy : ‖w - y‖ ≤ R * s) :
    incCov w a y s w a y s ≤ Real.log (s / a) + 2 * Real.log (R + 1) := by
  have hs : 0 < s := ha.trans_le has
  have h := LQGMetric.DFGPS.L34.incCov_far_le (w - y) ha has hR hwy
  have he := incCov_add (w - y) 0 (w - y) 0 y (r := a) (s := s) (r' := a) (s' := s) ha.ne' hs.ne'
  simp only [sub_add_cancel, zero_add] at he
  rw [he]
  exact h

 
theorem circleAvg_inc_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {a s R : ℝ} (ha : 0 < a) (has : a ≤ s) (hR : 0 ≤ R)
    (w y : ℂ) (hwy : ‖w - y‖ ≤ R * s) (hV : 0 < Real.log (s / a) + 2 * Real.log (R + 1))
    {x : ℝ} (hx : 0 < x) :
    P {ω | x ≤ |LQGMetric.circleAvg (h ω) a w - LQGMetric.circleAvg (h ω) s y|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-x ^ 2 / (2 * (Real.log (s / a) + 2 * Real.log (R + 1))))) := by
  have hs : 0 < s := ha.trans_le has
  have hlaw := (LQGMetric.CircleAvg.map_cInc hh ha hs w y).1
  have hm := LQGMetric.CircleAvg.measurable_cInc hh a w s y
  have hset : MeasurableSet {y : ℝ | x ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hpre : {ω | x ≤ |LQGMetric.circleAvg (h ω) a w - LQGMetric.circleAvg (h ω) s y|} =
      cInc h a w s y ⁻¹' {y : ℝ | x ≤ |y|} := rfl
  rw [hpre, ← Measure.map_apply hm hset, hlaw]
  refine gaussianReal_abs_tail ?_ hx
  have hle := incCov_le_of_far w y ha has hR hwy
  rw [Real.coe_toNNReal']
  exact max_le hle hV.le

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
