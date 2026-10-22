import HigherDimLQGMetric.DGZ.NondegIndex

/-! Positive crossing separates the two selected domains at fine mesh. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_gridRadius_tendsto_zero {rGrid : ℝ} :
    Tendsto (fun j : ℕ => nd_gridRadius rGrid j) atTop (𝓝 0) := by
  unfold nd_gridRadius
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul rGrid

theorem nd_eventually_selectedDomainsSeparated
    {rGrid r : ℝ} (hd : 0 < d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid)
    (hb₁ : s ∈ nd_boundedZeroEvent rGrid r)
    (hb₂ : s ∈ nd_boundedZeroEvent rGrid (2 * r))
    (hcross : 0 < nd_crossPhi 0 (2 * r) r s.1) :
    ∀ᶠ j : ℕ in atTop,
      ∀ i₁ i₂ : nd_DomainIndex d rGrid,
        i₁.1.1 = j → i₂.1.1 = j →
        s ∈ nd_selectedEq rGrid r i₁.1.1 i₁.1.2 →
        s ∈ nd_selectedEq rGrid (2 * r) i₂.1.1 i₂.1.2 →
        nd_domainSeparated rGrid i₁ i₂ := by
  have hE₁ne : (nd_zeroSet r s).Nonempty := by
    obtain ⟨x, hx⟩ := lsph_nonempty hd 0 hr.le
    exact ⟨x, nd_sphere_subset_zeroSet r hs hx⟩
  have hE₂ne : (nd_zeroSet (2 * r) s).Nonempty := by
    obtain ⟨x, hx⟩ := lsph_nonempty hd 0 (by linarith : 0 ≤ 2 * r)
    exact ⟨x, nd_sphere_subset_zeroSet (2 * r) hs hx⟩
  obtain ⟨δ, hδ, hgap⟩ := nd_exists_positive_gap_of_disjoint_compact
    (nd_zeroSet_isCompact_of_event hb₁) (nd_zeroSet_isCompact_of_event hb₂)
    ((nd_cross_pos_iff_disjoint_zeroSets hr hd hs).1 hcross)
  have hlim : Tendsto
      (fun j : ℕ => 2 * (Real.sqrt d * (4 * nd_gridRadius rGrid j)))
      atTop (𝓝 0) := by
    have heq : (fun j : ℕ => 2 * (Real.sqrt d * (4 * nd_gridRadius rGrid j))) =
        (fun j : ℕ => (8 * Real.sqrt d) * nd_gridRadius rGrid j) := by
      funext j
      ring
    rw [heq]
    simpa using (nd_gridRadius_tendsto_zero (rGrid := rGrid)).const_mul
      (8 * Real.sqrt d)
  filter_upwards [hlim.eventually (eventually_lt_nhds hδ)] with j hj
  intro i₁ i₂ hj₁ hj₂ hsel₁ hsel₂
  apply nd_domainSeparated_of_selected_of_gap hrGrid hgap i₁ i₂
    (hj₁.trans hj₂.symm)
  · simpa only [hj₁] using hj
  · exact hsel₁
  · exact hsel₂

end HigherDimLQGMetric.DGZ
