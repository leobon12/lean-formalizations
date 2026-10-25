import SupercriticalLQGUniqueness.B2.DG20Lim.UniformGoodAnnulusRatio

 

set_option autoImplicit false
noncomputable section

open Set Metric
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def centeredInnerCircle (x y r : ℚ) (hr : 0 < r) : RatCircle :=
  ⟨x, y, r, hr.le⟩

def centeredOuterCircle (x y r : ℚ) (hr : 0 < r) : RatCircle :=
  ⟨x, y, 2 * r, (mul_pos (by norm_num) hr).le⟩

def centeredRatAnnulus (x y r : ℚ) (hr : 0 < r) : RatAnnulus := by
  refine ⟨centeredInnerCircle x y r hr, centeredOuterCircle x y r hr,
    hr, ?_⟩
  constructor
  · exact mul_pos (by norm_num) hr
  · intro w hw
    have hdist : dist w (Complex.mk (x : ℝ) (y : ℝ)) ≤ (r : ℝ) := by
      simpa [RatCircle.closedDisk, RatCircle.center, centeredInnerCircle] using
        (mem_closedBall.mp hw)
    change w ∈ ball (Complex.mk (x : ℝ) (y : ℝ)) ((2 * r : ℚ) : ℝ)
    apply mem_ball.mpr
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    push_cast
    linarith

private theorem unitInner_center_zero : unitInnerCircle.center = (0 : ℂ) := by
  apply Complex.ext <;> simp [RatCircle.center, unitInnerCircle]

private theorem unitOuter_center_zero : unitOuterCircle.center = (0 : ℂ) := by
  apply Complex.ext <;> simp [RatCircle.center, unitOuterCircle]

theorem unitRatAnnulus_eq_closedAnn :
    unitRatAnnulus.toSet = closedAnn (0 : ℂ) 1 2 := by
  have hi : unitRatAnnulus.inner = unitInnerCircle := rfl
  have ho : unitRatAnnulus.outer = unitOuterCircle := rfl
  rw [RatAnnulus.toSet, hi, ho, RatCircle.closedDisk, RatCircle.openDisk,
    unitOuter_center_zero, unitInner_center_zero]
  ext w
  simp only [mem_sdiff, mem_closedBall, mem_ball, not_lt, closedAnn,
    mem_ofPred_eq, dist_eq_norm]
  change (‖w - (0 : ℂ)‖ ≤ (unitOuterCircle.radius : ℝ) ∧
    (unitInnerCircle.radius : ℝ) ≤ ‖w - (0 : ℂ)‖) ↔ _
  simp [unitInnerCircle, unitOuterCircle, and_comm]

theorem centeredRatAnnulus_eq_closedAnn (x y r : ℚ) (hr : 0 < r) :
    (centeredRatAnnulus x y r hr).toSet =
      closedAnn (Complex.mk (x : ℝ) (y : ℝ)) (r : ℝ) (2 * (r : ℝ)) := by
  ext w
  simp only [RatAnnulus.toSet, mem_sdiff, RatCircle.closedDisk,
    RatCircle.openDisk, mem_closedBall, mem_ball, not_lt, closedAnn,
    mem_ofPred_eq, dist_eq_norm]
  change (‖w - Complex.mk (x : ℝ) (y : ℝ)‖ ≤
    ((centeredOuterCircle x y r hr).radius : ℝ) ∧
    ((centeredInnerCircle x y r hr).radius : ℝ) ≤
    ‖w - Complex.mk (x : ℝ) (y : ℝ)‖) ↔ _
  simp [centeredInnerCircle, centeredOuterCircle, and_comm]

theorem centeredInnerCircle_affine (x y r : ℚ) (hr : 0 < r) :
    let T : ℂ ≃ₜ ℂ := dilateHomeo (Rat.cast_pos.mpr hr)
    let U : ℂ ≃ₜ ℂ := Homeomorph.addRight (Complex.mk (x : ℝ) (y : ℝ))
    U '' (T '' unitInnerCircle.toSet) = (centeredInnerCircle x y r hr).toSet := by
  dsimp
  change (fun w : ℂ => w + Complex.mk (x : ℝ) (y : ℝ)) ''
      ((fun w : ℂ => (r : ℝ) • w) '' unitInnerCircle.toSet) =
      (centeredInnerCircle x y r hr).toSet
  rw [RatCircle.toSet, unitInner_center_zero,
    image_smul_sphere (Rat.cast_pos.mpr hr), image_add_sphere]
  simp [RatCircle.toSet, RatCircle.center, centeredInnerCircle, unitInnerCircle]

theorem centeredOuterCircle_affine (x y r : ℚ) (hr : 0 < r) :
    let T : ℂ ≃ₜ ℂ := dilateHomeo (Rat.cast_pos.mpr hr)
    let U : ℂ ≃ₜ ℂ := Homeomorph.addRight (Complex.mk (x : ℝ) (y : ℝ))
    U '' (T '' unitOuterCircle.toSet) = (centeredOuterCircle x y r hr).toSet := by
  dsimp
  change (fun w : ℂ => w + Complex.mk (x : ℝ) (y : ℝ)) ''
      ((fun w : ℂ => (r : ℝ) • w) '' unitOuterCircle.toSet) =
      (centeredOuterCircle x y r hr).toSet
  rw [RatCircle.toSet, unitOuter_center_zero,
    image_smul_sphere (Rat.cast_pos.mpr hr), image_add_sphere]
  simp [RatCircle.toSet, RatCircle.center, centeredOuterCircle,
    unitOuterCircle, mul_comm]

theorem centeredRatAnnulus_affine (x y r : ℚ) (hr : 0 < r) :
    let T : ℂ ≃ₜ ℂ := dilateHomeo (Rat.cast_pos.mpr hr)
    let U : ℂ ≃ₜ ℂ := Homeomorph.addRight (Complex.mk (x : ℝ) (y : ℝ))
    U '' (T '' unitRatAnnulus.toSet) = (centeredRatAnnulus x y r hr).toSet := by
  dsimp
  change (fun w : ℂ => w + Complex.mk (x : ℝ) (y : ℝ)) ''
      ((fun w : ℂ => (r : ℝ) • w) '' unitRatAnnulus.toSet) =
      (centeredRatAnnulus x y r hr).toSet
  rw [unitRatAnnulus_eq_closedAnn,
    image_smul_closedAnn (Rat.cast_pos.mpr hr), image_add_closedAnn,
    centeredRatAnnulus_eq_closedAnn]
  simp [mul_comm]

end SupercriticalLQGUniqueness.B2.DG20Lim
