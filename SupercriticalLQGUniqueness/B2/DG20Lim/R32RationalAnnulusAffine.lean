import SupercriticalLQGUniqueness.B2.DG20Lim.R32UniformGoodAnnulusRatio

 



set_option autoImplicit false
noncomputable section

open Set Metric
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def centeredInnerCircleR32 (x y r : ℚ) (hr : 0 < r) : RatCircle :=
  ⟨x, y, r, hr.le⟩

def centeredOuterCircleR32 (x y r : ℚ) (hr : 0 < r) : RatCircle :=
  ⟨x, y, 3 / 2 * r, (mul_pos (by norm_num) hr).le⟩

def centeredRatAnnulusR32 (x y r : ℚ) (hr : 0 < r) : RatAnnulus := by
  refine ⟨centeredInnerCircleR32 x y r hr, centeredOuterCircleR32 x y r hr,
    hr, ?_⟩
  constructor
  · exact mul_pos (by norm_num) hr
  · intro w hw
    have hdist : dist w (Complex.mk (x : ℝ) (y : ℝ)) ≤ (r : ℝ) := by
      simpa [RatCircle.closedDisk, RatCircle.center, centeredInnerCircleR32] using
        (mem_closedBall.mp hw)
    change w ∈ ball (Complex.mk (x : ℝ) (y : ℝ)) ((3 / 2 * r : ℚ) : ℝ)
    apply mem_ball.mpr
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    push_cast
    linarith

private theorem unitInner_center_zeroR32 : unitInnerCircleR32.center = (0 : ℂ) := by
  apply Complex.ext <;> simp [RatCircle.center, unitInnerCircleR32]

private theorem unitOuter_center_zeroR32 : unitOuterCircleR32.center = (0 : ℂ) := by
  apply Complex.ext <;> simp [RatCircle.center, unitOuterCircleR32]

theorem unitRatAnnulus_eq_closedAnnR32 :
    unitRatAnnulusR32.toSet = closedAnn (0 : ℂ) 1 (3 / 2) := by
  have hi : unitRatAnnulusR32.inner = unitInnerCircleR32 := rfl
  have ho : unitRatAnnulusR32.outer = unitOuterCircleR32 := rfl
  rw [RatAnnulus.toSet, hi, ho, RatCircle.closedDisk, RatCircle.openDisk,
    unitOuter_center_zeroR32, unitInner_center_zeroR32]
  ext w
  simp only [mem_sdiff, mem_closedBall, mem_ball, not_lt, closedAnn,
    mem_ofPred_eq, dist_eq_norm]
  change (‖w - (0 : ℂ)‖ ≤ (unitOuterCircleR32.radius : ℝ) ∧
    (unitInnerCircleR32.radius : ℝ) ≤ ‖w - (0 : ℂ)‖) ↔ _
  simp [unitInnerCircleR32, unitOuterCircleR32, and_comm]

theorem centeredRatAnnulus_eq_closedAnnR32 (x y r : ℚ) (hr : 0 < r) :
    (centeredRatAnnulusR32 x y r hr).toSet =
      closedAnn (Complex.mk (x : ℝ) (y : ℝ)) (r : ℝ) (3 / 2 * (r : ℝ)) := by
  ext w
  simp only [RatAnnulus.toSet, mem_sdiff, RatCircle.closedDisk,
    RatCircle.openDisk, mem_closedBall, mem_ball, not_lt, closedAnn,
    mem_ofPred_eq, dist_eq_norm]
  change (‖w - Complex.mk (x : ℝ) (y : ℝ)‖ ≤
    ((centeredOuterCircleR32 x y r hr).radius : ℝ) ∧
    ((centeredInnerCircleR32 x y r hr).radius : ℝ) ≤
    ‖w - Complex.mk (x : ℝ) (y : ℝ)‖) ↔ _
  simp [centeredInnerCircleR32, centeredOuterCircleR32, and_comm]

theorem centeredInnerCircle_affineR32 (x y r : ℚ) (hr : 0 < r) :
    let T : ℂ ≃ₜ ℂ := dilateHomeo (Rat.cast_pos.mpr hr)
    let U : ℂ ≃ₜ ℂ := Homeomorph.addRight (Complex.mk (x : ℝ) (y : ℝ))
    U '' (T '' unitInnerCircleR32.toSet) = (centeredInnerCircleR32 x y r hr).toSet := by
  dsimp
  change (fun w : ℂ => w + Complex.mk (x : ℝ) (y : ℝ)) ''
      ((fun w : ℂ => (r : ℝ) • w) '' unitInnerCircleR32.toSet) =
      (centeredInnerCircleR32 x y r hr).toSet
  rw [RatCircle.toSet, unitInner_center_zeroR32,
    image_smul_sphere (Rat.cast_pos.mpr hr), image_add_sphere]
  simp [RatCircle.toSet, RatCircle.center, centeredInnerCircleR32, unitInnerCircleR32]

theorem centeredOuterCircle_affineR32 (x y r : ℚ) (hr : 0 < r) :
    let T : ℂ ≃ₜ ℂ := dilateHomeo (Rat.cast_pos.mpr hr)
    let U : ℂ ≃ₜ ℂ := Homeomorph.addRight (Complex.mk (x : ℝ) (y : ℝ))
    U '' (T '' unitOuterCircleR32.toSet) = (centeredOuterCircleR32 x y r hr).toSet := by
  dsimp
  change (fun w : ℂ => w + Complex.mk (x : ℝ) (y : ℝ)) ''
      ((fun w : ℂ => (r : ℝ) • w) '' unitOuterCircleR32.toSet) =
      (centeredOuterCircleR32 x y r hr).toSet
  rw [RatCircle.toSet, unitOuter_center_zeroR32,
    image_smul_sphere (Rat.cast_pos.mpr hr), image_add_sphere]
  simp [RatCircle.toSet, RatCircle.center, centeredOuterCircleR32,
    unitOuterCircleR32, mul_comm]

theorem centeredRatAnnulus_affineR32 (x y r : ℚ) (hr : 0 < r) :
    let T : ℂ ≃ₜ ℂ := dilateHomeo (Rat.cast_pos.mpr hr)
    let U : ℂ ≃ₜ ℂ := Homeomorph.addRight (Complex.mk (x : ℝ) (y : ℝ))
    U '' (T '' unitRatAnnulusR32.toSet) = (centeredRatAnnulusR32 x y r hr).toSet := by
  dsimp
  change (fun w : ℂ => w + Complex.mk (x : ℝ) (y : ℝ)) ''
      ((fun w : ℂ => (r : ℝ) • w) '' unitRatAnnulusR32.toSet) =
      (centeredRatAnnulusR32 x y r hr).toSet
  rw [unitRatAnnulus_eq_closedAnnR32,
    image_smul_closedAnn (Rat.cast_pos.mpr hr), image_add_closedAnn,
    centeredRatAnnulus_eq_closedAnnR32]
  simp [mul_comm]

end SupercriticalLQGUniqueness.B2.DG20Lim
