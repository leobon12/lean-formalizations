import HigherDimLQGMetric.Thm16.FixedRatioSlope
import HigherDimLQGMetric.Thm16.LogComparison

/-! A uniform fixed-scale ratio comparison identifies the power exponent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGMetric

theorem l9c_identify_power_exponent_fixed {a c : ℝ → ℝ}
    {lam K B α : ℝ}
    (ha : ∀ ε : ℝ, 0 < ε → 0 < a ε)
    (hc : ∀ r : ℝ, 0 < r → 0 < c r)
    (hK : 1 ≤ K) (hB : 0 < B)
    (hpow : ∀ r : ℝ, 0 < r →
      B⁻¹ * r ^ α ≤ c r ∧ c r ≤ B * r ^ α)
    (hfixed : ∀ r : ℝ, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      K⁻¹ * c r ≤ l9c_ratio a ε r ∧ l9c_ratio a ε r ≤ K * c r)
    (hA : Tendsto (fun ε => Real.log (a ε) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 lam)) :
    α = 1 - lam := by
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ r < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ r : ℝ in 𝓝 0, r < 1 from Iio_mem_nhds (by norm_num))]
      with r hr hr1
    exact ⟨hr, hr1⟩
  have hlogK : Tendsto (fun r : ℝ => Real.log K / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero
  have hLamLo : Tendsto (fun r : ℝ => (1 - lam) + Real.log K / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - lam)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hlogK
  have hLamHi : Tendsto (fun r : ℝ => (1 - lam) - Real.log K / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - lam)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hlogK
  have hbounds : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (1 - lam) + Real.log K / Real.log r ≤ Real.log (c r) / Real.log r ∧
      Real.log (c r) / Real.log r ≤ (1 - lam) - Real.log K / Real.log r := by
    filter_upwards [hsmall] with r hr
    obtain ⟨hlo,hhi⟩ := l9c_log_c_of_fixed_ratio ha hc hK hA hfixed hr.1 hr.2
    have hlog : Real.log r < 0 := Real.log_neg hr.1 hr.2
    have h1 := div_le_div_of_nonpos_of_le hlog.le hlo
    have h2 := div_le_div_of_nonpos_of_le hlog.le hhi
    have ht : ((1 - lam) * Real.log r) / Real.log r = 1 - lam := by
      exact mul_div_cancel_right₀ _ hlog.ne
    rw [ht] at h1 h2
    have hsub : (Real.log (c r) - Real.log K) / Real.log r =
        Real.log (c r) / Real.log r - Real.log K / Real.log r := by ring
    have hadd : (Real.log (c r) + Real.log K) / Real.log r =
        Real.log (c r) / Real.log r + Real.log K / Real.log r := by ring
    rw [hsub] at h1
    rw [hadd] at h2
    constructor <;> nlinarith [h1, h2]
  have hfixedLim : Tendsto (fun r : ℝ => Real.log (c r) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - lam)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hLamLo hLamHi
      (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
  have hpowLim : Tendsto (fun r : ℝ => Real.log (r ^ α) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 α) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hsmall] with r hr
    rw [Real.log_rpow hr.1]
    exact (mul_div_cancel_right₀ α (Real.log_neg hr.1 hr.2).ne).symm
  have hcLim : Tendsto (fun r : ℝ => Real.log (c r) / Real.log r)
      (𝓝[>] (0 : ℝ)) (𝓝 α) := by
    apply l9c_exponent_of_comparable (inv_pos.mpr hB)
      (by filter_upwards [hsmall] with r hr
          exact ⟨hc r hr.1, Real.rpow_pos_of_pos hr.1 α⟩)
      (by filter_upwards [hsmall] with r hr
          exact hpow r hr.1) hpowLim
  exact tendsto_nhds_unique hcLim hfixedLim

end HigherDimLQGMetric
