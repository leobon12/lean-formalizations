import MatedCRTHarmonic.GMS4.Prop410Rooting

/-!
# Normalized Lebesgue mass of a small rooting disk

This file computes the deterministic point mass used when conditioning the uniformly sampled
rooting point in Proposition 4.10, Case 2. It reuses Mathlib's exact planar ball-volume formula
and the normalized rooting measure from `Prop410Rooting`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4.GMSA

/-- A radius-`r` disk inside the unit rooting disk has normalized Lebesgue mass `r ^ 2`. -/
theorem normalizedLebesgueOnRootingDisk_ball (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    normalizedLebesgueOnRootingDisk (Metric.ball (0 : ℂ) r) =
      ENNReal.ofReal (r ^ 2) := by
  rw [normalizedLebesgueOnRootingDisk, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_ball]
  simp only [rootingDisk]
  rw [inter_eq_left.2 (Metric.ball_subset_ball hr1), Complex.volume_ball]
  rw [ENNReal.ofReal_inv_of_pos Real.pi_pos, ← NNReal.coe_real_pi,
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow hr0]
  rw [mul_comm (ENNReal.ofReal r ^ 2) (NNReal.pi : ℝ≥0∞)]
  exact ENNReal.inv_mul_cancel_left
    (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero) ENNReal.coe_ne_top

/-- Power-scale form of `normalizedLebesgueOnRootingDisk_ball`: the radius `ε ^ ξ` has mass
`ε ^ (2 * ξ)` when it lies at a nonnegative power scale inside the unit disk. -/
theorem normalizedLebesgueOnRootingDisk_ball_rpow (ε ξ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hξ : 0 ≤ ξ) :
    normalizedLebesgueOnRootingDisk (Metric.ball (0 : ℂ) (ε ^ ξ)) =
      ENNReal.ofReal (ε ^ (2 * ξ)) := by
  rw [normalizedLebesgueOnRootingDisk_ball _
    (Real.rpow_nonneg hε0.le ξ) (Real.rpow_le_one hε0.le hε1 hξ)]
  congr 1
  rw [show (ε ^ ξ) ^ 2 = (ε ^ ξ) ^ (2 : ℝ) by norm_cast,
    ← Real.rpow_mul hε0.le]
  congr 1
  ring

end MatedCRTHarmonic.GMS4.GMSA

