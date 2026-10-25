import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistBufferedRegion

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_terminal_ball_subset_of_collar
    {U K : Set ℂ} {k₀ : ℕ}
    (hcollar : ∀ k, k₀ ≤ k → ∀ v ∈ K, ∀ x : ℂ,
      dist v x < ((2 : ℝ)⁻¹) ^ k / 4 →
      ball x (17 * ((2 : ℝ)⁻¹) ^ k) ⊆ U)
    {v : ℂ} (hv : v ∈ K) {n : ℕ} (hn : k₀ ≤ n) :
    closedBall v (((2 : ℝ)⁻¹) ^ n) ⊆ U := by
  have hr : 0 < ((2 : ℝ)⁻¹) ^ n := by positivity
  have hvball : ball v (17 * ((2 : ℝ)⁻¹) ^ n) ⊆ U :=
    hcollar n hn v hv v (by simp only [dist_self]; positivity)
  intro x hx
  apply hvball
  have hxr : dist x v ≤ ((2 : ℝ)⁻¹) ^ n := mem_closedBall.mp hx
  rw [mem_ball]
  linarith

end SupercriticalLQGUniqueness.B2.DG20Pt
