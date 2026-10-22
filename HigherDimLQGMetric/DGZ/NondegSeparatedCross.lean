import HigherDimLQGMetric.DGZ.NondegEventuallyGap

/-! Separation of selected domains implies a positive crossing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_zeroSet_subset_domain_of_selected
    {rGrid r : ℝ} (hrGrid : 0 < rGrid)
    (i : nd_DomainIndex d rGrid) (s : nd_Joint d rGrid)
    (hsel : s ∈ nd_selectedEq rGrid r i.1.1 i.1.2) :
    nd_zeroSet r s ⊆ nd_domain rGrid i := by
  rw [← nd_thickening_eq_domain_of_selectedEq rGrid r i s hsel]
  exact nd_zeroSet_subset_thickening hrGrid r i.1.1 s

theorem nd_shell_subset_domain_of_selected
    {rGrid r : ℝ} (hrGrid : 0 < rGrid)
    (i : nd_DomainIndex d rGrid) (s : nd_Joint d rGrid)
    (hs : s ∈ nd_pseudoSet rGrid)
    (hsel : s ∈ nd_selectedEq rGrid r i.1.1 i.1.2) :
    lsph (0 : Rd d) r ⊆ nd_domain rGrid i :=
  (nd_sphere_subset_zeroSet r hs).trans
    (nd_zeroSet_subset_domain_of_selected hrGrid i s hsel)

theorem nd_cross_pos_of_selectedSeparated
    {rGrid r : ℝ} (hd : 0 < d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid)
    (i₁ i₂ : nd_DomainIndex d rGrid)
    (hsel₁ : s ∈ nd_selectedEq rGrid r i₁.1.1 i₁.1.2)
    (hsel₂ : s ∈ nd_selectedEq rGrid (2 * r) i₂.1.1 i₂.1.2)
    (hsep : nd_domainSeparated rGrid i₁ i₂) :
    0 < nd_crossPhi 0 (2 * r) r s.1 := by
  obtain ⟨δ, hδ, hsep⟩ := hsep
  have hE₁ := nd_zeroSet_subset_domain_of_selected hrGrid i₁ s hsel₁
  have hE₂ := nd_zeroSet_subset_domain_of_selected hrGrid i₂ s hsel₂
  apply (nd_cross_pos_iff_disjoint_zeroSets hr hd hs).2
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have h := hsep x (hE₁ hx₁) x (hE₂ hx₂)
  simp only [sub_self, norm_zero] at h
  exact (not_le_of_gt hδ) h

end HigherDimLQGMetric.DGZ
