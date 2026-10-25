import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.OriginBoundarySmall
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.HTranslate




 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

private theorem image_sub_closedBall (c : ℂ) (r : ℝ) :
    (fun z : ℂ => z - c) '' closedBall c r = closedBall 0 r := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hv
  · intro hz
    refine ⟨z + c, ?_, by simp only [add_sub_cancel_right]⟩
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right,
      sub_zero] using hz

theorem boundaryInternal_translate_scale
    (M E : LSCMetric) (c w : ℂ) (k : ENNReal)
    (hk0 : k ≠ 0) (hkt : k ≠ ∞)
    (h : ∀ x y : ℂ, E (x - c, y - c) = k * M (x, y)) :
    E.internal (closedBall 0 ‖w‖)
      (⟨w, by simp only [mem_closedBall, dist_zero_right, le_refl]⟩,
       ⟨0, mem_closedBall_self (norm_nonneg w)⟩) =
      k * M.internal (closedBall c ‖w‖)
        (⟨w + c, by simp only [mem_closedBall, dist_eq_norm,
            add_sub_cancel_right, le_refl]⟩,
         ⟨c, mem_closedBall_self (norm_nonneg w)⟩) := by
  have hx : w + c ∈ closedBall c ‖w‖ := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, le_refl]
  have hy : c ∈ closedBall c ‖w‖ :=
    mem_closedBall_self (norm_nonneg w)
  have hi := OptimalConstants.FirstExit.internal_translate_scale hk0 hkt c h
    (closedBall c ‖w‖) ⟨w + c, hx⟩ ⟨c, hy⟩
  unfold LSCMetric.internal at hi ⊢
  simpa only [image_sub_closedBall, add_sub_cancel_right, sub_self] using hi


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
