import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleEventually
import LQGMetric.Papers.DDDF.S6DGOsc

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_separator_intersects_square
    {X E F : Set ℂ} (hsep : LQGMetric.Disconnects X E F)
    {x y : ℂ} (hx : x ∈ (rectAB 1 1).toSet)
    (hy : y ∈ (rectAB 1 1).toSet) (hxE : x ∈ E) (hyF : y ∈ F) :
    (X ∩ (rectAB 1 1).toSet).Nonempty := by
  have hconn : IsPathConnected (rectAB 1 1).toSet :=
    S6DG.convex_unit.isPathConnected ⟨x, hx⟩
  obtain ⟨γ, hγ⟩ := hconn.joinedIn x hx y hy
  obtain ⟨z, ⟨t, ht⟩, hzX⟩ := hsep x y γ hxE hyF
  exact ⟨z, hzX, ht ▸ hγ t⟩

 

theorem laneC_exists_outer_square_corner (c : ℂ) {r : ℝ}
    (hr : 2 * r < 1 / 8) :
    ∃ y ∈ (rectAB 1 1).toSet, 2 * r < dist y c := by
  have hzero : (0 : ℂ) ∈ (rectAB 1 1).toSet := by
    rw [mem_rectAB_toSet]
    simp
  have hone : (1 : ℂ) ∈ (rectAB 1 1).toSet := by
    rw [mem_rectAB_toSet]
    simp
  by_cases h0 : 2 * r < dist (0 : ℂ) c
  · exact ⟨0, hzero, h0⟩
  refine ⟨1, hone, ?_⟩
  have htri : (1 : ℝ) ≤ dist (0 : ℂ) c + dist (1 : ℂ) c := by
    simpa [dist_comm c (1 : ℂ)] using dist_triangle (0 : ℂ) c (1 : ℂ)
  by_contra hnot
  have h0' : dist (0 : ℂ) c ≤ 2 * r := le_of_not_gt h0
  have h1' : dist (1 : ℂ) c ≤ 2 * r := le_of_not_gt hnot
  linarith

 

theorem laneC_separator_of_visited_block_intersects_square
    {X : Set ℂ} {c : ℂ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r < 1 / 8)
    (hsep : LQGMetric.Disconnects X (sphere c r) (sphere c (2 * r)))
    {x : ℂ} (hxSq : x ∈ (rectAB 1 1).toSet)
    (hxIn : dist x c ≤ r) :
    (X ∩ (rectAB 1 1).toSet).Nonempty := by
  obtain ⟨y, hySq, hyOut⟩ := laneC_exists_outer_square_corner c hr
  have hsep' : LQGMetric.Disconnects X (closedBall c r) (ball c (2 * r))ᶜ :=
    hsep.closedBall_compl_ball (by linarith)
  exact laneC_separator_intersects_square hsep' hxSq hySq hxIn (not_lt.mpr hyOut.le)

end SupercriticalLQGUniqueness.B2.DG20Conc
