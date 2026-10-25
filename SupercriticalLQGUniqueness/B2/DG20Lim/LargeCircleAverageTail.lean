import SupercriticalLQGUniqueness.B2.DG20Lim.ScaledCircleAverageTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem large_circle_average_lower_tail
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (r : Ioi (1 : ℝ)) (β : ℝ) (hβ : 0 < β) :
    μ {g | circleAvg (affineComp (r : ℝ) 0 g) 1 0 ≤
          -(β * Real.log (r : ℝ))} ≤
      ENNReal.ofReal (2 * (r : ℝ) ^ (-(β ^ 2 / 2))) := by
  let ρ : ℝ := r
  have hr : (0 : ℝ) < r := lt_trans one_pos r.property
  have hlog : 0 < Real.log (r : ℝ) := Real.log_pos r.property
  have hx : 0 < β * Real.log (r : ℝ) := mul_pos hβ hlog
  have htail :=
    SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.circleAvg_inc_tail
      hμ.1 (a := 1) (s := (r : ℝ)) (R := 0)
      (by norm_num) r.property.le (by norm_num) 0 0 (by simp)
      (by simpa using hlog)
      hx
  have hzero : ∀ᵐ g ∂μ, circleAvg g 1 0 = 0 := by
    filter_upwards [hμ.2] with g hg
    exact LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hg
  have hscale := LQGMetric.CircleAvg.ae_circleAvg_affineComp hμ.1 hr (0 : ℂ)
  calc
    μ {g | circleAvg (affineComp ρ 0 g) 1 0 ≤
        -(β * Real.log (r : ℝ))} ≤
        μ {g | β * Real.log (r : ℝ) ≤
          |circleAvg g 1 0 - circleAvg g r 0|} := by
          apply measure_mono_ae
          filter_upwards [hzero, hscale] with g hg0 hgs hg
          have hgs' : circleAvg (affineComp ρ 0 g) 1 0 =
              circleAvg g r 0 := by simpa only [ρ, id] using hgs
          rw [hgs'] at hg
          rw [hg0]
          exact le_trans (by linarith : β * Real.log (r : ℝ) ≤
            0 - circleAvg g r 0) (le_abs_self _)
    _ ≤ ENNReal.ofReal (2 * Real.exp
        (-(β * Real.log (r : ℝ)) ^ 2 /
          (2 * Real.log (r : ℝ)))) := by
          simpa only [id, div_one, zero_add, zero_mul, mul_zero, add_zero,
            Real.log_one] using htail
    _ = ENNReal.ofReal (2 * (r : ℝ) ^ (-(β ^ 2 / 2))) := by
          congr 1
          rw [Real.rpow_def_of_pos hr]
          congr 1
          field_simp [hlog.ne']

end SupercriticalLQGUniqueness.B2.DG20Lim
