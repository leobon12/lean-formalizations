import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.FV2ScaleCore




 


set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

theorem inverse_metric_addConst_scale
    (D : DistC → LSCMetric) (ξ : ℝ) (g : DistC) (c : ℝ)
    (hscale : ∀ x y : ℂ,
      D (LQGMetric.addConst g c) (x, y) =
        ENNReal.ofReal (Real.exp (ξ * c)) * D g (x, y)) :
    ∀ x y : ℂ,
      D (LQGMetric.addConst (LQGMetric.addConst g c) (-c)) (x, y) =
        ENNReal.ofReal (Real.exp (ξ * -c)) *
          D (LQGMetric.addConst g c) (x, y) := by
  have hreal : Real.exp (ξ * -c) * Real.exp (ξ * c) = 1 := by
    rw [mul_neg, Real.exp_neg]
    field_simp
  have hmul : ENNReal.ofReal (Real.exp (ξ * -c)) *
      ENNReal.ofReal (Real.exp (ξ * c)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hreal]
    exact ENNReal.ofReal_one
  intro x y
  rw [LQGMetric.GFFLaw.addConst_addConst, add_neg_cancel,
    LQGMetric.GFFLaw.addConst_zero', hscale, ← mul_assoc, hmul, one_mul]

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
