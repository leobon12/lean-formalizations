import HigherDimLQGMetric.Thm16.RatioProbLower

/-! The fixed-scale comparison has a constant independent of the scale. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l9c_fixed_ratio_compare {d : ℕ} (hd : 3 ≤ d)
    {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c)
    (hprop42 : Prop42Shape)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ r : ℝ, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      K⁻¹ * c r ≤ l9c_ratio (aEps κ ξ) ε r ∧
        l9c_ratio (aEps κ ξ) ε r ≤ K * c r := by
  obtain ⟨Ku, hKu, hu⟩ := l9c_fixed_ratio_upper hd hξ hsub hκ hD
    hprop42 hB2 hL6a
  obtain ⟨Kl, hKl, hl⟩ := l9c_fixed_ratio_lower hd hξ hsub hκ hD
    hprop42 hB2 hL6a
  let K : ℝ := max 1 (max Ku Kl)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKuK : Ku ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKlK : Kl ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  intro r hr
  filter_upwards [hu r hr, hl r hr, self_mem_nhdsWithin] with ε hu' hl' hε
  have hd2 : 2 ≤ d := by omega
  have haε : 0 < aEps κ ξ ε := l6a_aEps_pos hd2 κ hκ ξ hε
  have hδ : 0 < ε / r := div_pos hε hr
  have haδ : 0 < aEps κ ξ (ε / r) := l6a_aEps_pos hd2 κ hκ ξ hδ
  have hratio : 0 < l9c_ratio (aEps κ ξ) ε r := by
    unfold l9c_ratio
    exact div_pos (mul_pos hr haδ) haε
  have hclo : c r ≤ K * l9c_ratio (aEps κ ξ) ε r :=
    hl'.trans (mul_le_mul_of_nonneg_right hKlK hratio.le)
  constructor
  · have hh := (div_le_iff₀ hKpos).2 (by
      simpa only [mul_comm] using hclo)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  · exact hu'.trans (mul_le_mul_of_nonneg_right hKuK (hD.c_pos r hr).le)

end HigherDimLQGMetric
