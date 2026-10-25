import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.SourceStatementsV2




 
set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces

 
theorem euclidSetDist_closedBalls_ge (z w : ℂ) (s q : ℝ)
    (hsep : q + 2 * s ≤ dist z w) :
    ENNReal.ofReal q ≤
      euclidSetDist (Metric.closedBall z s) (Metric.closedBall w s) := by
  unfold euclidSetDist
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  have hx' : dist z x ≤ s := by simpa only [dist_comm] using (Metric.mem_closedBall.mp hx)
  have hy' : dist y w ≤ s := by simpa only [dist_comm] using Metric.mem_closedBall.mp hy
  have h1 := dist_triangle z x w
  have h2 := dist_triangle x y w
  exact ENNReal.ofReal_le_ofReal (by linarith only [hsep, hx', hy', h1, h2])

 
theorem euclidSetDist_closedBall_sphere_ge (z : ℂ) (b s q : ℝ)
    (hclear : q + s ≤ Metric.infDist z (Metric.sphere (0 : ℂ) b)) :
    ENNReal.ofReal q ≤
      euclidSetDist (Metric.closedBall z s) (Metric.sphere (0 : ℂ) b) := by
  unfold euclidSetDist
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  have hx' : dist z x ≤ s := by simpa only [dist_comm] using (Metric.mem_closedBall.mp hx)
  have hzy : Metric.infDist z (Metric.sphere (0 : ℂ) b) ≤ dist z y :=
    Metric.infDist_le_dist_of_mem hy
  have htri := dist_triangle z x y
  exact ENNReal.ofReal_le_ofReal (by linarith only [hclear, hx', hzy, htri])

 
theorem closedBalls_disjoint_of_two_radius_lt (z w : ℂ) (s : ℝ)
    (hsep : 2 * s < dist z w) :
    Disjoint (Metric.closedBall z s) (Metric.closedBall w s) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' : dist z x ≤ s := by simpa only [dist_comm] using (Metric.mem_closedBall.mp hx)
  have hy' : dist x w ≤ s := by simpa only [dist_comm] using (Metric.mem_closedBall.mp hy)
  have htri := dist_triangle z x w
  linarith only [hsep, hx', hy', htri]

 
theorem closedBall_subset_double_origin (z : ℂ) (b s : ℝ)
    (hz : z ∈ Metric.ball (0 : ℂ) b) (hs : s ≤ b) :
    Metric.closedBall z s ⊆ Metric.ball (0 : ℂ) (2 * b) := by
  intro x hx
  rw [Metric.mem_ball] at hz ⊢
  have hx' : dist x z ≤ s := Metric.mem_closedBall.mp hx
  have htri := dist_triangle x z 0
  have hzero : dist x 0 = dist 0 x := dist_comm x 0
  have hz' : dist z 0 = dist 0 z := dist_comm z 0
  linarith only [hz, hs, hx', htri, hzero, hz']

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
