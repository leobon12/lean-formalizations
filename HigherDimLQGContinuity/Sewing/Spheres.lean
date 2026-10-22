import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Shell.Geom

/-!
# Intersections of boundaries of overlapping balls

The deterministic sphere lemma used in the sewing argument for Lemma 3.1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLFPP (Rd)

/-- Two overlapping, non-nested open balls in dimension at least two have intersecting
boundary spheres. -/
theorem sphere_inter_nonempty {d : ℕ} (hd : 2 ≤ d) (z₁ z₂ : Rd d) (r₁ r₂ : ℝ)
    (hover : (ball z₁ r₁ ∩ ball z₂ r₂).Nonempty)
    (h₁₂ : ¬ ball z₁ r₁ ⊆ ball z₂ r₂)
    (h₂₁ : ¬ ball z₂ r₂ ⊆ ball z₁ r₁) :
    (sphere z₁ r₁ ∩ sphere z₂ r₂).Nonempty := by
  obtain ⟨x, hx₁, hx₂⟩ := hover
  have hr₁ : 0 < r₁ := lt_of_le_of_lt dist_nonneg hx₁
  have hr₂ : 0 < r₂ := lt_of_le_of_lt dist_nonneg hx₂
  have hmeet : (ball z₂ r₂ ∩ sphere z₁ r₁).Nonempty :=
    HigherDimLQGMetric.connected_inter_sphere (ball z₂ r₂) (isConnected_ball hr₂)
      ⟨x, hx₂, hx₁⟩ h₂₁
  obtain ⟨w, hw₂, hw₁⟩ := hmeet
  have hnot : ¬ closedBall z₁ r₁ ⊆ ball z₂ r₂ := by
    intro h
    exact h₁₂ (ball_subset_closedBall.trans h)
  exact HigherDimLQGMetric.sphere_inter_sphere_nonempty hd hr₁.le hnot hw₁ hw₂

end HigherDimLQGContinuity
