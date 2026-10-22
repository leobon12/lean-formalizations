import HigherDimLQGContinuity.Improve.PowerThreshold
import HigherDimLQGContinuity.Improve.GainParams

/-!
# A shared exponential scale for gain, error, and drift
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- After the mesh is below `v*cseed`, one fixed multiple of its depth is
small enough for the gain, local error, and the three-power drift budget. -/
theorem q11_gain_mesh_bounds {v cseed V Δ K0 U0 dsep B : ℝ}
    (hv : 0 < v) (hcseed : 0 < cseed) (hcseed1 : cseed ≤ 1)
    (hV : 1 ≤ V) (hΔ : Δ = Real.exp (-V))
    (hΔvc : Δ ≤ v * cseed)
    (hU0 : 1 ≤ U0) (hdsep : 0 < dsep)
    (hBv : 1 ≤ B)
    (hBg : K0 + 1 + max 0 (-Real.log (1 / (16 * U0))) ≤ B)
    (hBe : K0 + 1 +
      max 0 (-Real.log (min (1 / 4) (dsep / (8 * U0)))) ≤ B)
    (hBdr : 3 + max 0 (-Real.log (1 / 100)) ≤ B) :
    let e := Real.exp (-(B * V))
    0 < e ∧ e ≤ v ∧
      e ≤ q11GainDelta v cseed Δ K0 U0 / 16 ∧
      e ≤ q11Error v cseed Δ K0 U0 dsep ∧
      e ≤ Δ ^ (3 : ℕ) / 100 := by
  have hΔpos : 0 < Δ := by rw [hΔ]; positivity
  have hΔ1 : Δ ≤ 1 := by
    rw [hΔ, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hvc : 0 < v * cseed := mul_pos hv hcseed
  have hΔv : Δ ≤ v :=
    hΔvc.trans (mul_le_of_le_one_right hv.le hcseed1)
  have hε : 0 < min (1 / 4) (dsep / (8 * U0)) := by
    apply lt_min
    · norm_num
    · positivity
  have hpow : Δ ^ (K0 + 1) = Δ * Δ ^ K0 := by
    rw [Real.rpow_add hΔpos, Real.rpow_one]
    ring
  have hgainlo : Δ ^ (K0 + 1) / U0 ≤
      q11GainDelta v cseed Δ K0 U0 := by
    rw [hpow]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hΔvc (Real.rpow_nonneg hΔpos.le _))
      (by linarith : 0 ≤ U0)
  have herrlo : min (1 / 4) (dsep / (8 * U0)) * Δ ^ (K0 + 1) ≤
      q11Error v cseed Δ K0 U0 dsep := by
    rw [hpow]
    change _ ≤ min (1 / 4) (dsep / (8 * U0)) * (v * cseed * Δ ^ K0)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hΔvc (Real.rpow_nonneg hΔpos.le _)) hε.le
  have hvg : Real.exp (-(B * V)) ≤ Δ := by
    have hh := q11_exp_below_power hV one_pos
      (show 1 + max 0 (-Real.log (1 : ℝ)) ≤ B by simpa using hBv)
    simpa only [one_mul, hΔ, Real.rpow_one] using hh
  have hg : Real.exp (-(B * V)) ≤ Δ ^ (K0 + 1) / (16 * U0) := by
    have hh := q11_exp_below_power hV
      (show 0 < 1 / (16 * U0) by positivity) hBg
    have heq : (1 / (16 * U0)) * Δ ^ (K0 + 1) =
        Δ ^ (K0 + 1) / (16 * U0) := by ring
    simpa only [← hΔ, heq] using hh
  have he : Real.exp (-(B * V)) ≤
      min (1 / 4) (dsep / (8 * U0)) * Δ ^ (K0 + 1) := by
    simpa only [← hΔ] using q11_exp_below_power hV hε hBe
  have hdr : Real.exp (-(B * V)) ≤ Δ ^ (3 : ℕ) / 100 := by
    have hh := q11_exp_below_power hV (show 0 < 1 / (100 : ℝ) by norm_num) hBdr
    have heq : (1 / (100 : ℝ)) * Δ ^ (3 : ℝ) = Δ ^ (3 : ℕ) / 100 := by
      rw [Real.rpow_ofNat]
      ring
    simpa only [← hΔ, heq] using hh
  have hgain : Real.exp (-(B * V)) ≤
      q11GainDelta v cseed Δ K0 U0 / 16 := by
    have hh := div_le_div_of_nonneg_right hgainlo (by norm_num : (0 : ℝ) ≤ 16)
    have heq : (Δ ^ (K0 + 1) / U0) / 16 = Δ ^ (K0 + 1) / (16 * U0) := by ring
    rw [heq] at hh
    exact hg.trans hh
  exact ⟨Real.exp_pos _, hvg.trans hΔv, hgain, he.trans herrlo, hdr⟩

end HigherDimLQGContinuity
