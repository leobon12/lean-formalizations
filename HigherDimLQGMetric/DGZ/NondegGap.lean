import HigherDimLQGMetric.DGZ.NondegSeparated

/-! Compact disjoint zero sets force a positive gap between fine cubical domains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_exists_positive_gap_of_disjoint_compact
    {E₁ E₂ : Set (Rd d)} (h₁ : IsCompact E₁) (h₂ : IsCompact E₂)
    (hdisj : Disjoint E₁ E₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E₁, ∀ y ∈ E₂, δ ≤ ‖x - y‖ := by
  obtain ⟨δ, hδ, hgap⟩ := Metric.exists_pos_forall_lt_edist h₁ h₂.isClosed hdisj
  refine ⟨(δ : ℝ), NNReal.coe_pos.mpr hδ, ?_⟩
  intro x hx y hy
  have he : ENNReal.ofReal (δ : ℝ) < ENNReal.ofReal (dist x y) := by
    simpa only [ENNReal.ofReal_coe_nnreal, edist_dist] using hgap x hx y hy
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (NNReal.coe_nonneg δ)).mp he).le

theorem nd_domainSeparated_of_selected_of_gap
    {rGrid r₁ r₂ δ : ℝ} (hrGrid : 0 < rGrid)
    {s : nd_Joint d rGrid}
    (hgap : ∀ x ∈ nd_zeroSet r₁ s, ∀ y ∈ nd_zeroSet r₂ s, δ ≤ ‖x - y‖)
    (i₁ i₂ : nd_DomainIndex d rGrid)
    (hj : i₁.1.1 = i₂.1.1)
    (hsmall : 2 * (Real.sqrt d * (4 * nd_gridRadius rGrid i₁.1.1)) < δ)
    (hsel₁ : s ∈ nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2)
    (hsel₂ : s ∈ nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2) :
    nd_domainSeparated rGrid i₁ i₂ := by
  let ε := Real.sqrt d * (4 * nd_gridRadius rGrid i₁.1.1)
  refine ⟨δ - 2 * ε, by dsimp [ε]; linarith, ?_⟩
  intro z hz w hw
  obtain ⟨x, hx, hzx⟩ := nd_near_zero_of_mem_domain hrGrid i₁ s hsel₁ hz
  obtain ⟨y, hy, hwy⟩ := nd_near_zero_of_mem_domain hrGrid i₂ s hsel₂ hw
  have hwy' : ‖w - y‖ ≤ ε := by simpa only [ε, ← hj] using hwy
  have htri : ‖x - y‖ ≤ ‖x - z‖ + ‖z - w‖ + ‖w - y‖ := by
    calc
      ‖x - y‖ = ‖(x - z) + (z - w) + (w - y)‖ := by congr 1; abel
      _ ≤ ‖(x - z) + (z - w)‖ + ‖w - y‖ := norm_add_le _ _
      _ ≤ ‖x - z‖ + ‖z - w‖ + ‖w - y‖ := by
        gcongr
        exact norm_add_le _ _
  rw [norm_sub_rev x z] at htri
  have hgap' := hgap x hx y hy
  dsimp [ε] at *
  linarith

end HigherDimLQGMetric.DGZ
