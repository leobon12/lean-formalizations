import HigherDimLQGContinuity.Core.Interfaces

/-! The scalar step of equation (4.23), once the two metric comparisons are available. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- The global envelope and site reference comparisons turn into polynomial unit bounds. -/
theorem site_unit_window {S H A0 mc β σ s Δ : ℝ}
    (hH : 0 < H) (hA0 : 0 < A0) (hmc : 0 < mc)
    (hβ : 1 ≤ β) (hσ : 0 < σ) (_hσ1 : σ ≤ 1)
    (hΔ : 0 < Δ) (hΔq : Δ ≤ 1 / 4)
    (hslo : Δ ^ (2 : ℕ) ≤ s) (hshi : s ≤ Δ)
    (hΔlo : Δ ≤ 4 ^ β / (H * A0)) (hΔhi : Δ ≤ mc / H)
    (hlow : H⁻¹ * (4 * s) ^ β / A0 ≤ S)
    (hup : S ≤ H * (4 * s) ^ σ / mc) :
    Δ ^ (2 * β + 1) ≤ S ∧ S ≤ Δ ^ (-(2 * β + 1)) := by
  have hs : 0 < s := lt_of_lt_of_le (pow_pos hΔ _) hslo
  have hfour : 0 < (4 : ℝ) := by norm_num
  have hΔ1 : Δ ≤ 1 := by linarith
  have h4s : 4 * s ≤ 1 := by nlinarith only [hshi, hΔq]
  have h4s0 : 0 ≤ 4 * s := by positivity
  have hpowUpper : (4 * s) ^ σ ≤ 1 := Real.rpow_le_one h4s0 h4s hσ.le
  have hPowS : Δ ^ (2 * β) ≤ s ^ β := by
    have h := Real.rpow_le_rpow (sq_nonneg Δ) hslo (by linarith : 0 ≤ β)
    convert h using 1
    rw [show Δ ^ (2 : ℕ) = Δ ^ (2 : ℝ) by norm_cast,
      ← Real.rpow_mul hΔ.le]
  have hcoeff : Δ ≤ H⁻¹ * (4 : ℝ) ^ β / A0 := by
    convert hΔlo using 1
    field_simp
  have hpowFactor : (4 * s) ^ β = (4 : ℝ) ^ β * s ^ β := by
    rw [Real.mul_rpow hfour.le hs.le]
  have hlow' : (H⁻¹ * (4 : ℝ) ^ β / A0) * s ^ β ≤ S := by
    calc
      _ = H⁻¹ * (4 * s) ^ β / A0 := by rw [hpowFactor]; ring
      _ ≤ S := hlow
  have hcoeff0 : 0 ≤ H⁻¹ * (4 : ℝ) ^ β / A0 := by positivity
  have hpowS0 : 0 ≤ s ^ β := Real.rpow_nonneg hs.le _
  have hΔpow0 : 0 ≤ Δ ^ (2 * β) := Real.rpow_nonneg hΔ.le _
  have hlowFinal : Δ ^ (2 * β + 1) ≤ S := by
    have h₁ := mul_le_mul_of_nonneg_right hcoeff hpowS0
    have h₂ := mul_le_mul_of_nonneg_left hPowS hΔ.le
    rw [Real.rpow_add hΔ, Real.rpow_one]
    nlinarith only [h₁, h₂, hlow', hcoeff0, hΔpow0]
  have hupperConst : S ≤ H / mc := by
    have h := mul_le_mul_of_nonneg_left hpowUpper hH.le
    have h' := div_le_div_of_nonneg_right h hmc.le
    simpa only [mul_one] using hup.trans h'
  have hHmc : H / mc ≤ Δ⁻¹ := by
    have h' : H * Δ ≤ mc := by
      have h'' := (le_div_iff₀ hH).mp hΔhi
      nlinarith only [h'']
    have h'' : H / mc ≤ (1 : ℝ) / Δ :=
      (div_le_div_iff₀ hmc hΔ).2 (by simpa only [one_mul] using h')
    simpa only [one_div] using h''
  have hInv : Δ⁻¹ ≤ Δ ^ (-(2 * β + 1)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1
      (show -(2 * β + 1) ≤ -1 by linarith)
    simpa only [Real.rpow_neg_one] using h
  exact ⟨hlowFinal, hupperConst.trans (hHmc.trans hInv)⟩

end HigherDimLQGContinuity
