import HigherDimLQGMetric.Thm16.RatioProb
import HigherDimLQGMetric.Thm16.RatioFinal

/-! The probabilistic comparison and deterministic power-law conclusion meet here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l9c_theorem16_of_aEps_exponent {d : ℕ} (hd : 3 ≤ d)
    {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    (hprop42 : Prop42Shape)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hA : ∀ (κ : Rd d → ℝ), HigherDimLFPP.IsLFPPKernel κ →
      Tendsto (fun ε => Real.log (aEps κ ξ ε) / Real.log ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 - ξ * distExp d ξ)))
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) :
    (∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 < r →
        C⁻¹ * r ^ (ξ * distExp d ξ) ≤ c r ∧
          c r ≤ C * r ^ (ξ * distExp d ξ)) ∧
      IsSharpWeakExpMetric d ξ (distExp d ξ) D := by
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  obtain ⟨K, hK, hratio⟩ :=
    l9c_fixed_ratio_compare hd hξ hsub hκ hD hprop42 hB2 hL6a
  exact l9c_powerSharp_of_ratio hd hD
    (fun ε hε => l6a_aEps_pos (by omega : 2 ≤ d) κ hκ ξ hε)
    (hA κ hκ) hK hratio

end HigherDimLQGMetric
