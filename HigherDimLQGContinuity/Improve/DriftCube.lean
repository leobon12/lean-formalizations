import HigherDimLQGContinuity.Improve.PowerThreshold

/-!
# Three spare mesh powers control the Cameron--Martin drift
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set

/-- A drift ceiling of `Δ³/100` pays for both the inverse lower endpoint
and the logarithm of the site-certificate parameter. -/
theorem q11_drift_of_cube {a ξ η θ P V Δ ts v : ℝ}
    (ha : 0 < a) (hξ : a ≤ ξ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hθlo : Real.exp (-P) ≤ θ)
    (hP : P ≤ V) (haV : a⁻¹ ≤ V)
    (hΔ : Δ = Real.exp (-V)) (hΔv : Δ ≤ v)
    (hts : 0 ≤ ts) (hts3 : ts ≤ Δ ^ (3 : ℕ) / 100)
    (hτ : |η - ξ| ≤ ts) :
    |η - ξ| * (ξ⁻¹ * Real.log θ⁻¹) ≤ v / 100 := by
  have hξpos : 0 < ξ := lt_of_lt_of_le ha hξ
  have hInv : ξ⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hξpos ha).2 hξ
  have hInv0 : 0 ≤ ξ⁻¹ := inv_nonneg.mpr hξpos.le
  have hlog : Real.log θ⁻¹ ≤ P := by
    have hh := Real.log_le_log (Real.exp_pos _) hθlo
    rw [Real.log_exp] at hh
    rw [Real.log_inv]
    linarith
  have hlog0 : 0 ≤ Real.log θ⁻¹ := by
    exact Real.log_nonneg ((one_le_inv₀ hθ).2 hθ1.le)
  have hVexp : V ≤ Real.exp V := by
    have hh := Real.add_one_le_exp V
    linarith
  have hM : ξ⁻¹ * Real.log θ⁻¹ ≤ (Real.exp V) ^ (2 : ℕ) := by
    have hfirst : ξ⁻¹ ≤ Real.exp V := hInv.trans (haV.trans hVexp)
    have hsecond : Real.log θ⁻¹ ≤ Real.exp V := hlog.trans (hP.trans hVexp)
    have hprod := mul_le_mul hfirst hsecond hlog0 (Real.exp_pos V).le
    nlinarith only [hprod]
  have hM0 : 0 ≤ ξ⁻¹ * Real.log θ⁻¹ := mul_nonneg hInv0 hlog0
  have hτ0 : 0 ≤ |η - ξ| := abs_nonneg _
  have hΔpos : 0 < Δ := by rw [hΔ]; positivity
  have hΔexp : Δ ^ (3 : ℕ) * (Real.exp V) ^ (2 : ℕ) = Δ := by
    rw [hΔ, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hbd : |η - ξ| * (ξ⁻¹ * Real.log θ⁻¹) ≤ Δ / 100 := by
    have hmul1 := mul_le_mul_of_nonneg_right hτ hM0
    have hmul2 := mul_le_mul_of_nonneg_left hM hts
    have hmul3 := mul_le_mul_of_nonneg_right hts3
      (by positivity : 0 ≤ (Real.exp V) ^ (2 : ℕ))
    have htsmall : (Δ ^ (3 : ℕ) / 100) * (Real.exp V) ^ (2 : ℕ) = Δ / 100 := by
      rw [div_mul_eq_mul_div, hΔexp]
    linarith only [hmul1, hmul2, hmul3, htsmall]
  linarith only [hbd, hΔv]

end HigherDimLQGContinuity
