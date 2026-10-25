import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.NormalizerRatio




 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem ennreal_div_eq_div_mul_div
    (A n m : ENNReal) (hn0 : n ≠ 0) (hnt : n ≠ ∞) :
    A / m = (A / n) * (n / m) := by
  simp only [div_eq_mul_inv]
  calc
    A * m⁻¹ = A * (n⁻¹ * n) * m⁻¹ := by rw [ENNReal.inv_mul_cancel hn0 hnt, mul_one]
    _ = (A * n⁻¹) * (n * m⁻¹) := by ac_rfl

def normalizedAroundAt (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (g : LQGMetric.DistC) (a s : Set.Ioi (0 : ℝ)) (y c : ℂ) : ENNReal :=
  Objects.CorrectedEvent.around (D g) y ((1/2) * a) (1 * a) / Objects.AnnulusTails.nrm ξ Q g s c

theorem normalizedAroundAt_eq
    (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (g : LQGMetric.DistC) (a s : Set.Ioi (0 : ℝ)) (y c : ℂ) :
    normalizedAroundAt ξ Q D g a s y c =
      ENNReal.ofReal ((a / s) ^ (ξ * Q)) *
        normalizedAroundCost ξ Q D g a y *
        ENNReal.ofReal
          (Real.exp (ξ * (LQGMetric.circleAvg g a y -
            LQGMetric.circleAvg g s c))) := by
  have hn0 : Objects.AnnulusTails.nrm ξ Q g a y ≠ 0 := by
    unfold Objects.AnnulusTails.nrm
    exact (ENNReal.ofReal_pos.mpr
      (mul_pos (Real.rpow_pos_of_pos a.2 _) (Real.exp_pos _))).ne'
  have hnt : Objects.AnnulusTails.nrm ξ Q g a y ≠ ∞ := by
    unfold Objects.AnnulusTails.nrm
    exact ENNReal.ofReal_ne_top
  unfold normalizedAroundAt normalizedAroundCost
  rw [ennreal_div_eq_div_mul_div _ _ _ hn0 hnt,
    nrm_div_nrm_eq_scale_mul_exp]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg a.2.le s.2.le) _)]
  ac_rfl


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
