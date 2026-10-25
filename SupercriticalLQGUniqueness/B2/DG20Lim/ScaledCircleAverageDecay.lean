import SupercriticalLQGUniqueness.B2.DG20Lim.ScaledCircleAverageTail
import SupercriticalLQGUniqueness.B2.Polylog.P7Compact

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

private theorem gaussian_radius_identity {r β : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    2 * Real.exp (-(β * Real.log r⁻¹) ^ 2 /
        (2 * Real.log r⁻¹)) =
      2 * r ^ (β ^ 2 / 2) := by
  have hlog : 0 < Real.log r⁻¹ :=
    Real.log_pos (one_lt_inv_iff₀.mpr ⟨hr, hr1⟩)
  rw [Real.rpow_def_of_pos hr]
  congr 1
  rw [Real.log_inv]
  field_simp [hlog.ne']

theorem exists_small_scaled_circle_average_tail
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (β η : ℝ) (hβ : 0 < β) (hη : 0 < η) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : Ioo (0 : ℝ) 1, (r : ℝ) ≤ r₀ →
        μ {g | β * Real.log ((r : ℝ)⁻¹) ≤
          circleAvg (affineComp r 0 g) 1 0} ≤
            ENNReal.ofReal η := by
  have hp : 0 < β ^ 2 / 2 := by positivity
  obtain ⟨r₀, hr₀, hsmall⟩ :=
    B2.Polylog.exists_rpow_le hp (t := η / 2) (half_pos hη)
  refine ⟨r₀, hr₀, ?_⟩
  intro r hrr₀
  have hpow : (r : ℝ) ^ (β ^ 2 / 2) ≤ η / 2 :=
    hsmall r r.property.1.le hrr₀
  calc
    μ {g | β * Real.log ((r : ℝ)⁻¹) ≤
      circleAvg (affineComp r 0 g) 1 0} ≤
        ENNReal.ofReal (2 * Real.exp
          (-(β * Real.log ((r : ℝ)⁻¹)) ^ 2 /
            (2 * Real.log ((r : ℝ)⁻¹)))) :=
      scaled_circle_average_upper_tail μ hμ r β hβ
    _ = ENNReal.ofReal (2 * (r : ℝ) ^ (β ^ 2 / 2)) := by
      rw [gaussian_radius_identity r.property.1 r.property.2]
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)

end SupercriticalLQGUniqueness.B2.DG20Lim
