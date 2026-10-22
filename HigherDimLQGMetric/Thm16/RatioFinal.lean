import HigherDimLQGMetric.Thm16.ApproxMul
import HigherDimLQGMetric.Thm16.WeakNorm
import HigherDimLQGMetric.Thm16.RatioAlgebra
import HigherDimLQGMetric.Thm16.FixedRatioExponent
import HigherDimLQGMetric.Thm16.ScaleTransfer
import HigherDimLQGMetric.Frozen.DistExp

/-! The deterministic conclusion of Theorem 1.6 after its ratio estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l9c_powerSharp_of_ratio {d : ℕ} (hd : 3 ≤ d)
    {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c)
    {a : ℝ → ℝ}
    (ha : ∀ ε : ℝ, 0 < ε → 0 < a ε)
    (hA : Tendsto (fun ε => Real.log (a ε) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - ξ * distExp d ξ)))
    {K : ℝ} (hK : 1 ≤ K)
    (hfixed : ∀ r : ℝ, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      K⁻¹ * c r ≤ l9c_ratio a ε r ∧ l9c_ratio a ε r ≤ K * c r) :
    (∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 < r →
        C⁻¹ * r ^ (ξ * distExp d ξ) ≤ c r ∧
          c r ≤ C * r ^ (ξ * distExp d ξ)) ∧
      IsSharpWeakExpMetric d ξ (distExp d ξ) D := by
  have hmul := l9c_approxMul_of_ratio ha hD.c_pos hK hfixed
  obtain ⟨B, hB, hloc⟩ := weakNormalizer_locBdd hd hD
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  obtain ⟨α, B', hB', hpow⟩ := powerLaw_of_approxMul hD.c_pos
    (one_le_pow₀ hK) hmul ⟨B, hB, hloc⟩
  let C : ℝ := max 1 B'
  have hC : 1 ≤ C := le_max_left _ _
  have hBC : B' ≤ C := le_max_right _ _
  have hpowC (r : ℝ) (hr : 0 < r) :
      C⁻¹ * r ^ α ≤ c r ∧ c r ≤ C * r ^ α := by
    obtain ⟨hl, hu⟩ := hpow r hr
    have hp : 0 ≤ r ^ α := (Real.rpow_pos_of_pos hr _).le
    exact ⟨(mul_le_mul_of_nonneg_right (inv_anti₀ hB' hBC) hp).trans hl,
      hu.trans (mul_le_mul_of_nonneg_right hBC hp)⟩
  have hα : α = ξ * distExp d ξ := by
    have h := l9c_identify_power_exponent_fixed ha hD.c_pos hK
      (lt_of_lt_of_le zero_lt_one hC)
      hpowC hfixed hA
    linarith
  subst α
  have hbounds := hpowC
  exact ⟨⟨C, hC, hbounds⟩,
    l9c_sharpWeak_of_powerBounds hD hC hbounds⟩

end HigherDimLQGMetric
