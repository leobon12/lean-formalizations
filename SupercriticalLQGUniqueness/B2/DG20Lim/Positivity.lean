import SupercriticalLQGUniqueness.B2.DG20Lim.Geometry

 

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

private theorem exists_rat_center_near (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x y : ℚ, dist (Complex.mk (x : ℝ) (y : ℝ)) z < δ := by
  obtain ⟨x, hxlo, hxhi⟩ := exists_rat_btwn
    (show z.re - δ / 4 < z.re + δ / 4 by linarith)
  obtain ⟨y, hylo, hyhi⟩ := exists_rat_btwn
    (show z.im - δ / 4 < z.im + δ / 4 by linarith)
  refine ⟨x, y, ?_⟩
  have hx : |(x : ℝ) - z.re| < δ / 4 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hy : |(y : ℝ) - z.im| < δ / 4 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have h := Complex.norm_le_abs_re_add_abs_im (Complex.mk (x : ℝ) (y : ℝ) - z)
  simp only [Complex.sub_re, Complex.sub_im] at h
  rw [dist_eq_norm]
  linarith

 
theorem exists_ratCircle_surrounding_small (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ O : RatCircle, O.Surrounds z ∧ O.closedDisk ⊆ ball z δ ∧
      (O.radius : ℝ) < δ := by
  obtain ⟨x, y, hc⟩ := exists_rat_center_near z (by positivity : 0 < δ / 4)
  have hc' : dist z (Complex.mk (x : ℝ) (y : ℝ)) < δ / 4 := by
    simpa only [dist_comm] using hc
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn
    (show dist z (Complex.mk (x : ℝ) (y : ℝ)) < δ / 2 by linarith)
  have hrpos : 0 < (r : ℝ) := lt_of_le_of_lt dist_nonneg hrlo
  let O : RatCircle := ⟨x, y, r, Rat.cast_nonneg.mp hrpos.le⟩
  refine ⟨O, ?_, ?_, ?_⟩
  · exact ⟨Rat.cast_pos.mp hrpos, mem_ball.mpr hrlo⟩
  · intro u hu
    have hu' : dist u O.center ≤ (r : ℝ) := mem_closedBall.mp hu
    have htri : dist u z ≤ dist u O.center + dist O.center z := dist_triangle _ _ _
    apply mem_ball.mpr
    dsimp [RatCircle.center, O] at hu' htri
    linarith [hc]
  · dsimp [O]
    linarith

theorem exists_disjoint_ratCircles (z w : ℂ) (hzw : z ≠ w) :
    ∃ O P : RatCircle, O.Surrounds z ∧ P.Surrounds w ∧
      Disjoint O.closedDisk P.closedDisk := by
  have hdist : 0 < dist z w := dist_pos.mpr hzw
  obtain ⟨O, hO, hOsmall, _⟩ := exists_ratCircle_surrounding_small z
    (show 0 < dist z w / 4 by positivity)
  obtain ⟨P, hP, hPsmall, _⟩ := exists_ratCircle_surrounding_small w
    (show 0 < dist z w / 4 by positivity)
  refine ⟨O, P, hO, hP, ?_⟩
  exact (ball_disjoint_ball (show dist z w / 4 + dist z w / 4 ≤ dist z w by linarith)).mono
    hOsmall hPsmall

theorem RData.DfromR_pos (R : RData) {z w : ℂ} (hzw : z ≠ w) :
    0 < R.DfromR z w := by
  obtain ⟨O, P, hO, hP, hdisj⟩ := exists_disjoint_ratCircles z w hzw
  exact R.DfromR_pos_of_pair hzw O P hO hP hdisj

theorem RData.DfromR_eq_zero_iff (R : RData) (z w : ℂ) :
    R.DfromR z w = 0 ↔ z = w := by
  constructor
  · intro h
    by_contra hzw
    exact (ne_of_gt (R.DfromR_pos hzw)) h
  · intro h
    subst w
    exact R.DfromR_self z

end SupercriticalLQGUniqueness.B2.DG20Lim
