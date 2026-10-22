import HigherDimLQGMetric.DGZ.NondegNear

/-! Spatially separated finite zero-set codes are independent under a joint limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

def nd_domainSeparated (rGrid : ℝ)
    (i₁ i₂ : nd_DomainIndex d rGrid) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ nd_domain rGrid i₁,
    ∀ w ∈ nd_domain rGrid i₂, δ ≤ ‖z - w‖

theorem nd_selectedEq_indep_of_domainSeparated
    {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r₁ r₂ : ℝ) (hrGrid : 0 < rGrid) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ))
    (i₁ i₂ : nd_DomainIndex d rGrid)
    (hsub₁ : lsph (0 : Rd d) r₁ ⊆ nd_domain rGrid i₁)
    (hsub₂ : lsph (0 : Rd d) r₂ ⊆ nd_domain rGrid i₂)
    (hsep : nd_domainSeparated rGrid i₁ i₂) :
    (μ : Measure (nd_Joint d rGrid))
      (nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2 ∩
        nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2) =
      (μ : Measure (nd_Joint d rGrid))
        (nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2) *
      (μ : Measure (nd_Joint d rGrid))
        (nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2) := by
  obtain ⟨δ, hδ, hgap⟩ := hsep
  obtain ⟨ρ, hρ0, hρ⟩ := h.kernel.exists_radius
  have hpow : Tendsto (fun m : ℕ => 2 * ρ * ((2 : ℝ)⁻¹ ^ m)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul (2 * ρ)
  obtain ⟨m, hm⟩ := (hpow.eventually (eventually_lt_nhds hδ)).exists
  apply nd_selectedEq_indep_of_tendsto h hH hq0 hq1 rGrid r₁ r₂
    hrGrid hr₁ hr₂ ns hns hlim i₁ i₂ hsub₁ hsub₂ m ρ hρ
  intro z hz w hw
  exact hm.trans_le (hgap z hz w hw)

end HigherDimLQGMetric.DGZ
