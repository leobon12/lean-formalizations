import SupercriticalLQGUniqueness.B2.DG20Lim.ScaledUnitPointUpperTail
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Gauss

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem scaled_circle_average_upper_tail
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (r : Ioo (0 : ℝ) 1) (β : ℝ) (hβ : 0 < β) :
    μ {g | β * Real.log ((r : ℝ)⁻¹) ≤
      circleAvg (affineComp r 0 g) 1 0} ≤
      ENNReal.ofReal (2 * Real.exp
        (-(β * Real.log ((r : ℝ)⁻¹)) ^ 2 /
          (2 * Real.log ((r : ℝ)⁻¹)))) := by
  have hr : (0 : ℝ) < r := r.property.1
  have hr1 : (r : ℝ) < 1 := r.property.2
  have hlog : 0 < Real.log ((r : ℝ)⁻¹) :=
    Real.log_pos (one_lt_inv_iff₀.mpr ⟨hr, hr1⟩)
  have hx : 0 < β * Real.log ((r : ℝ)⁻¹) := mul_pos hβ hlog
  have htail :=
    SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.circleAvg_inc_tail
      hμ.1 hr hr1.le (by norm_num : (0 : ℝ) ≤ 0)
      0 0 (by simp) (by simpa using hlog) hx
  have hzero : ∀ᵐ g ∂μ, circleAvg g 1 0 = 0 := by
    filter_upwards [hμ.2] with g hg
    exact LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hg
  have hscale := LQGMetric.CircleAvg.ae_circleAvg_affineComp
    hμ.1 hr (0 : ℂ)
  calc
    μ {g | β * Real.log ((r : ℝ)⁻¹) ≤
      circleAvg (affineComp r 0 g) 1 0}
      ≤ μ {g | β * Real.log ((r : ℝ)⁻¹) ≤
        |circleAvg g r 0 - circleAvg g 1 0|} := by
          apply measure_mono_ae
          filter_upwards [hzero, hscale] with g hg0 hgs hg
          have hgs' : circleAvg (affineComp r 0 g) 1 0 =
              circleAvg g r 0 := by simpa only [id] using hgs
          rw [hgs'] at hg
          simpa only [hg0, sub_zero] using hg.trans (le_abs_self _)
    _ ≤ ENNReal.ofReal (2 * Real.exp
        (-(β * Real.log ((r : ℝ)⁻¹)) ^ 2 /
          (2 * Real.log ((r : ℝ)⁻¹)))) := by
          simpa only [id, one_div, zero_add, zero_mul, mul_zero, add_zero,
            Real.log_one] using htail

end SupercriticalLQGUniqueness.B2.DG20Lim
