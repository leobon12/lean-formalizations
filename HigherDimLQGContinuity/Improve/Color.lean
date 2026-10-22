import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Sec8.Colors

/-!
# Reusing the finite lattice palette for supplied sites

The Section 8 palette of `HigherDimLQGMetric` is coarser than the palette
required here, so one colour separates full radius-four inspections.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

/-- Distinct supplied-site centres with the same existing Section 8 colour
are at least ten site radii apart. -/
theorem q11_same_color_sep {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    {k l : Fin d → ℤ} (hne : k ≠ l)
    (hc : sec8Color d k = sec8Color d l) :
    10 * r ≤ ‖latPt ((1 / (20 * Real.sqrt d)) * r) k -
      latPt ((1 / (20 * Real.sqrt d)) * r) l‖ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  let R : ℝ := 5 * Real.sqrt d * r
  have hR : 0 < R := by dsimp [R]; positivity
  have hscale : R / (100 * d) = (1 / (20 * Real.sqrt d)) * r := by
    dsimp [R]
    have hsq : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt hd0.le
    field_simp
    nlinarith only [hsq]
  have hlarge := sec8_sameColor_dist hd hR hne hc
  rw [hscale] at hlarge
  have hten : 10 * r ≤ 10 * R := by
    have hroot1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
    dsimp [R]
    nlinarith only [hroot1, hr.le]
  exact hten.trans hlarge

end HigherDimLQGContinuity
