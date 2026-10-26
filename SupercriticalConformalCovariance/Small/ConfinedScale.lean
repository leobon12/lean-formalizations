import SupercriticalConformalCovariance.Small.AffineInternal
import SupercriticalConformalCovariance.Small.ConfinedLSC
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FirstExit.FirstExit

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness

/-- Pointwise metric scaling commutes with diagonal-corrected disk confinement. -/
theorem conf_apply_of_pointwise_scale
    {D E : LSCMetric} {s : ℝ≥0∞}
    (hs0 : s ≠ 0) (hst : s ≠ ⊤)
    (h : ∀ x y : ℂ, E (x,y) = s * D (x,y))
    (c : ℂ) (R : ℝ) (p : ℂ × ℂ) :
    conf E c R p = s * conf D c R p := by
  rcases p with ⟨x,y⟩
  by_cases hxy : x = y
  · subst y
    simp [conf_apply,confKernel]
  by_cases hx : x ∈ closedBall c R
  · by_cases hy : y ∈ closedBall c R
    · rw [conf_apply, conf_apply,
        confKernel_eq_intrinsic E c R hx hy,
        confKernel_eq_intrinsic D c R hx hy]
      exact SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FirstExit.internal_of_scale
        hs0 hst h (closedBall c R) (⟨x,hx⟩) (⟨y,hy⟩)
    · rw [conf_apply, conf_apply,
        confKernel_outside E c R hxy (by simp [hy]),
        confKernel_outside D c R hxy (by simp [hy])]
      simp [hs0]
  · rw [conf_apply, conf_apply,
      confKernel_outside E c R hxy (by simp [hx]),
      confKernel_outside D c R hxy (by simp [hx])]
    simp [hs0]

end SupercriticalConformalCovariance.Small
