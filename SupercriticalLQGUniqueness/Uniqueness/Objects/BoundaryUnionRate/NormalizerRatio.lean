import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.AroundMoment




 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem nrm_div_nrm_eq_scale_mul_exp
    (ξ Q : ℝ) (g : LQGMetric.DistC)
    (a s : Set.Ioi (0 : ℝ)) (y c : ℂ) :
    Objects.AnnulusTails.nrm ξ Q g a y / Objects.AnnulusTails.nrm ξ Q g s c =
      ENNReal.ofReal
        ((a / s) ^ (ξ * Q) *
          Real.exp (ξ * (LQGMetric.circleAvg g a y -
            LQGMetric.circleAvg g s c))) := by
  have hden : 0 < (s : ℝ) ^ (ξ * Q) *
      Real.exp (ξ * LQGMetric.circleAvg g s c) :=
    mul_pos (Real.rpow_pos_of_pos s.2 _) (Real.exp_pos _)
  unfold Objects.AnnulusTails.nrm
  rw [← ENNReal.ofReal_div_of_pos hden]
  congr 1
  rw [mul_div_mul_comm]
  rw [← Real.div_rpow a.2.le s.2.le]
  rw [← Real.exp_sub]
  congr 1
  ring_nf


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
