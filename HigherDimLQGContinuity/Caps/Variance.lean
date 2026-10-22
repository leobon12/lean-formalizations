import HigherDimLQGContinuity.Caps.GridCount
import HigherDimLQGContinuity.Norm.PinGauss

/-!
# Variance bound on the inspected grid (packet P4)

The radius-`s₀` pinned sphere average has variance at most a constant times
`n` when the inspection window grows no faster than `exp (c₀ n)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory ProbabilityTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

private theorem p4_max_zero_log_norm_div_le {d : ℕ} {z : Rd d} {a W : ℝ}
    (ha : 1 ≤ a) (hW : 0 ≤ W) (hz : ‖z‖ ≤ W) :
    max 0 (Real.log (‖z‖ / a)) ≤ Real.log (1 + W) := by
  have hlogW : 0 ≤ Real.log (1 + W) := Real.log_nonneg (by linarith)
  apply max_le hlogW
  by_cases hz0 : ‖z‖ = 0
  · rw [hz0, zero_div, Real.log_zero]
    exact hlogW
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz0)
    have ha0 : 0 < a := by linarith
    have hdiv : ‖z‖ / a ≤ 1 + W := by
      calc
        ‖z‖ / a ≤ ‖z‖ := div_le_self (norm_nonneg z) ha
        _ ≤ W := hz
        _ ≤ 1 + W := by linarith
    exact Real.log_le_log (div_pos hzpos ha0) hdiv

/-- A variance bound uniform in both pin radii and all inspected pairs. -/
theorem p4_exists_grid_variance_bound {d : ℕ} (hd : 2 ≤ d) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {s s₀ : ℝ}, 1 ≤ s → s ≤ 10 → 1 ≤ s₀ → s₀ ≤ 10 →
      ∀ {n : ℕ} {W : ℝ}, 1 ≤ n → 0 ≤ W → Real.log (1 + W) ≤ c₀ * n →
      ∀ {r : ℝ}, 0 < r → Real.exp (-(n : ℝ)) ≤ r → r ≤ 1 →
      ∀ z : Rd d, ‖z‖ ≤ W →
        Var[fun g : DistRd d => sphereAvg g (s * r) z; pinLaw d s₀] ≤ C₁ * n := by
  obtain ⟨K, hK⟩ := exists_variance_sphereAvg_pinLaw_le hd
  let C₁ : ℝ := 1 + 2 * c₀ + max 0 (Real.log 10 + K)
  have hC₁ : 0 < C₁ := by dsimp [C₁]; nlinarith [le_max_left 0 (Real.log 10 + K)]
  refine ⟨C₁, hC₁, ?_⟩
  intro s s₀ hs hs10 hs₀ hs₀10 n W hn hW hWlog r hr hrlo hr1 z hz
  have hρ : 0 < s * r := mul_pos (by linarith) hr
  have hρlo : Real.exp (-(n : ℝ)) ≤ s * r := by nlinarith [mul_nonneg (sub_nonneg.mpr hs) hr.le]
  have hρhi : s * r ≤ 10 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (by linarith : 0 ≤ s)]
  have hlogρlo : -(n : ℝ) ≤ Real.log (s * r) := by
    have h := Real.log_le_log (Real.exp_pos _) hρlo
    simpa only [Real.log_exp] using h
  have hlogρhi : Real.log (s * r) ≤ Real.log 10 :=
    Real.log_le_log hρ hρhi
  have hlogs₀hi : Real.log s₀ ≤ Real.log 10 :=
    Real.log_le_log (by linarith) hs₀10
  have hlogs₀lo : 0 ≤ Real.log s₀ := Real.log_nonneg hs₀
  have hspatial₀ := p4_max_zero_log_norm_div_le hs₀ hW hz
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hKbound : Real.log 10 + K ≤ max 0 (Real.log 10 + K) := le_max_right _ _
  have hmaxnonneg : 0 ≤ max 0 (Real.log 10 + K) := le_max_left _ _
  have hmaxn : max 0 (Real.log 10 + K) ≤ max 0 (Real.log 10 + K) * n := by
    nlinarith [mul_nonneg hmaxnonneg (sub_nonneg.mpr hnR)]
  rcases le_total (s * r) s₀ with hle | hle
  · have hv := (hK (by linarith) hρ z).1 hle
    rw [Real.log_div (by linarith : s₀ ≠ 0) hρ.ne'] at hv
    dsimp [C₁]
    nlinarith only [hv, hlogs₀hi, hlogρlo, hspatial₀, hWlog, hnR,
      hKbound, hmaxn, hc₀, mul_nonneg hc₀ (sub_nonneg.mpr hnR)]
  · have hspatialρ := p4_max_zero_log_norm_div_le (hs₀.trans hle) hW hz
    have hv := (hK (by linarith) hρ z).2 hle
    rw [Real.log_div hρ.ne' (by linarith : s₀ ≠ 0)] at hv
    dsimp [C₁]
    nlinarith only [hv, hlogρhi, hlogs₀lo, hspatialρ, hWlog, hnR,
      hKbound, hmaxn, hc₀, mul_nonneg hc₀ (sub_nonneg.mpr hnR)]

end HigherDimLQGContinuity
