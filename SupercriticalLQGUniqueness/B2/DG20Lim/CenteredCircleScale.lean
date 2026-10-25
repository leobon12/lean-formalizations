import SupercriticalLQGUniqueness.B2.DG20Lim.RationalAnnulusAffine

 

set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem centeredInnerCircle_zero_scale (r : ℚ) (hr : 0 < r) :
    (B2.Polylog.dilateHomeo (Rat.cast_pos.mpr hr)) ''
      unitInnerCircle.toSet = (centeredInnerCircle 0 0 r hr).toSet := by
  have h := centeredInnerCircle_affine 0 0 r hr
  simpa [Homeomorph.addRight,
    show Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) by rfl] using h

theorem centeredOuterCircle_zero_scale (r : ℚ) (hr : 0 < r) :
    (B2.Polylog.dilateHomeo (Rat.cast_pos.mpr hr)) ''
      unitOuterCircle.toSet = (centeredOuterCircle 0 0 r hr).toSet := by
  have h := centeredOuterCircle_affine 0 0 r hr
  simpa [Homeomorph.addRight,
    show Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) by rfl] using h

end SupercriticalLQGUniqueness.B2.DG20Lim
