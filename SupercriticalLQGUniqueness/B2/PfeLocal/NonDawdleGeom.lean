import SupercriticalLQGUniqueness.B2.PfeLocal.Crossing

 





set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 

theorem near_endpoint_ball_subset {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {y z : ℂ} (hz : z ∈ Metric.ball y (3 * ε)) :
    Metric.ball y (ε ^ 2 / 2) ⊆ Metric.ball z (4 * ε) := by
  intro u hu
  rw [Metric.mem_ball] at hz hu ⊢
  have hsq : ε ^ 2 / 2 ≤ ε := by nlinarith [sq_nonneg ε]
  have htri : dist u z ≤ dist u y + dist y z := dist_triangle _ _ _
  have : dist y z = dist z y := dist_comm _ _
  rw [this] at htri
  linarith

 

theorem far_endpoint_outside_lattice_ball {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {y x z : ℂ} (hz : z ∉ Metric.ball y (3 * ε))
    (hx : x ∈ Metric.ball y (ε ^ 2 / 2)) :
    z ∉ Metric.ball x (2 * ε) := by
  rw [Metric.mem_ball] at hx
  rw [Metric.mem_ball, not_lt] at hz ⊢
  have hsq : ε ^ 2 / 2 ≤ ε / 2 := by nlinarith [sq_nonneg ε]
  have htri : dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
  have hxy : dist x y = dist y x := dist_comm _ _
  rw [hxy] at htri
  linarith

 

theorem small_ball_subset_lattice_ball {ε : ℝ}
    {y x : ℂ} (hx : x ∈ Metric.ball y (ε ^ 2 / 2)) :
    Metric.ball y (ε ^ 2 / 2) ⊆ Metric.ball x (ε ^ 2) := by
  intro u hu
  rw [Metric.mem_ball] at hx hu ⊢
  have htri : dist u x ≤ dist u y + dist y x := dist_triangle _ _ _
  have hxy : dist y x = dist x y := dist_comm _ _
  rw [hxy] at htri
  linarith

end SupercriticalLQGUniqueness.B2.PfeLocal
