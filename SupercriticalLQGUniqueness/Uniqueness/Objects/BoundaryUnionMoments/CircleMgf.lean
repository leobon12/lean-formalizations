import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Gauss




 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments

 

theorem mgf_circleAvg_increment_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistC}
    (hh : LQGMetric.IsWholePlaneGFF h P) {a s R : ℝ}
    (ha : 0 < a) (has : a ≤ s) (hR : 0 ≤ R)
    (w y : ℂ) (hwy : ‖w - y‖ ≤ R * s) (t : ℝ) :
    mgf (LQGMetric.CircleAvg.cInc h a w s y) P t ≤
      Real.exp (t ^ 2 * (Real.log (s / a) + 2 * Real.log (R + 1)) / 2) := by
  let V := LQGMetric.CircleAvg.incCov w a y s w a y s
  have hmap := (LQGMetric.CircleAvg.map_cInc hh ha (ha.trans_le has) w y).1
  have hmeas := LQGMetric.CircleAvg.measurable_cInc hh a w s y
  have hlaw : HasLaw (LQGMetric.CircleAvg.cInc h a w s y)
      (gaussianReal 0 V.toNNReal) P := ⟨hmeas.aemeasurable, hmap⟩
  have hmgf := mgf_gaussianReal hlaw t
  have hVbound := Objects.AnnulusTails.incCov_le_of_far w y ha has hR hwy
  have hVnonneg : 0 ≤ Real.log (s / a) + 2 * Real.log (R + 1) := by
    have hs : 0 < s := ha.trans_le has
    have hsa : 1 ≤ s / a := (one_le_div ha).2 has
    have hR1 : 1 ≤ R + 1 := by linarith only [hR]
    have hlogsa := Real.log_nonneg hsa
    have hlogR := Real.log_nonneg hR1
    linarith only [hlogsa, hlogR]
  have hVbound' : (V.toNNReal : ℝ) ≤ Real.log (s / a) + 2 * Real.log (R + 1) := by
    rw [Real.coe_toNNReal']
    exact max_le hVbound hVnonneg
  rw [hmgf]
  apply Real.exp_le_exp.mpr
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  nlinarith only [hVbound', ht2]

end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments
