import HigherDimLQGMetric.Thm16.Exponent
import HigherDimLQGMetric.Thm16.FromExponent
import HigherDimLQGMetric.Core.MainInputs

/-! [1] Theorem 1.6: every weak metric assignment has the sharp normalizer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem theorem16 {d : ℕ} (hd : 3 ≤ d)
    {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    (hprop42 : Prop42Shape)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) :
    (∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 < r →
        C⁻¹ * r ^ (ξ * distExp d ξ) ≤ c r ∧
          c r ≤ C * r ^ (ξ * distExp d ξ)) ∧
      IsSharpWeakExpMetric d ξ (distExp d ξ) D := by
  apply l9c_theorem16_of_aEps_exponent hd hξ hsub hprop42 hB2 hL6a
  · intro κ hκ
    exact aEps_exponent hd hξ hsub hB2 hL6a hκ
  · exact hD

theorem theorem16Shape_of (hprop42 : Prop42Shape)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ) :
    Theorem16Shape := by
  intro d hd ξ hξ hsub D c hD
  exact theorem16 hd hξ hsub hprop42 hB2 hL6a hD

end HigherDimLQGMetric
