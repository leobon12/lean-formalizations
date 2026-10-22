import HigherDimLQGContinuity.Core.Interfaces

/-!
# Gain and error scales in the improvement step
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

def q11GainDelta (v cseed Δ K0 U0 : ℝ) : ℝ :=
  v * cseed * Δ ^ K0 / U0

def q11Error (v cseed Δ K0 U0 dsep : ℝ) : ℝ :=
  min (1 / 4) (dsep / (8 * U0)) * (v * cseed * Δ ^ K0)

/-- The fixed error fraction fits the two halves of the rounding budget;
both gain and error lie below the improvement parameter. -/
theorem q11_gain_error_bounds {v cseed Δ K0 U0 dsep : ℝ}
    (hv : 0 < v) (hcseed : 0 < cseed) (hcseed1 : cseed ≤ 1)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hK0 : 0 ≤ K0)
    (hU0 : 1 ≤ U0) (hdsep : 0 < dsep) :
    0 < q11GainDelta v cseed Δ K0 U0 ∧
    q11GainDelta v cseed Δ K0 U0 ≤ v ∧
    0 < q11Error v cseed Δ K0 U0 dsep ∧
    q11Error v cseed Δ K0 U0 dsep ≤ v ∧
    2 * q11Error v cseed Δ K0 U0 dsep ≤
      7 / 16 * q11GainDelta v cseed Δ K0 U0 * dsep := by
  let z : ℝ := v * cseed * Δ ^ K0
  let cε : ℝ := min (1 / 4) (dsep / (8 * U0))
  have hU0pos : 0 < U0 := lt_of_lt_of_le one_pos hU0
  have hz : 0 < z := by dsimp [z]; positivity
  have hcε : 0 < cε := by dsimp [cε]; positivity
  have hcε1 : cε ≤ 1 := by dsimp [cε]; linarith [min_le_left (1 / 4 : ℝ) (dsep / (8 * U0))]
  have hcεd : cε ≤ dsep / (8 * U0) := min_le_right _ _
  have hΔpow : Δ ^ K0 ≤ 1 := Real.rpow_le_one hΔ.le hΔ1 hK0
  have hzv : z ≤ v := by
    dsimp [z]
    nlinarith [mul_nonneg hv.le hcseed.le, mul_nonneg hv.le (Real.rpow_nonneg hΔ.le K0)]
  have hεv : cε * z ≤ v := by
    nlinarith [mul_nonneg hcε.le hz.le]
  have hg : 0 < z / U0 := by positivity
  have hgv : z / U0 ≤ v := by
    have hdiv : z / U0 ≤ z := (div_le_iff₀ hU0pos).2 (by nlinarith only [hU0, hz.le])
    exact hdiv.trans hzv
  have hε : 0 < cε * z := mul_pos hcε hz
  have hsmall : 2 * (cε * z) ≤ 7 / 16 * (z / U0) * dsep := by
    have hmul := mul_le_mul_of_nonneg_right hcεd hz.le
    have hscaled := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)
    have heq : 2 * (dsep / (8 * U0) * z) = 1 / 4 * (z / U0) * dsep := by
      field_simp
      ring
    calc
      2 * (cε * z) ≤ 2 * (dsep / (8 * U0) * z) := hscaled
      _ = 1 / 4 * (z / U0) * dsep := heq
      _ ≤ 7 / 16 * (z / U0) * dsep := by
        nlinarith [mul_nonneg hg.le hdsep.le]
  change 0 < z / U0 ∧ z / U0 ≤ v ∧ 0 < cε * z ∧ cε * z ≤ v ∧
    2 * (cε * z) ≤ 7 / 16 * (z / U0) * dsep
  exact ⟨hg, hgv, hε, hεv, hsmall⟩

end HigherDimLQGContinuity
