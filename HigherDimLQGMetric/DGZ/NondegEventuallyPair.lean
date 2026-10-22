import HigherDimLQGMetric.DGZ.NondegSepMembership

/-! A positive crossing eventually appears in every separated-code event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_eventually_mem_sepPairEvent
    {rGrid r : ℝ} (hd : 0 < d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid)
    (hb₁ : s ∈ nd_boundedZeroEvent rGrid r)
    (hb₂ : s ∈ nd_boundedZeroEvent rGrid (2 * r))
    (hidx₁ : ∀ j : ℕ, ∃ i : nd_DomainIndex d rGrid,
      i.1.1 = j ∧ s ∈ nd_selectedEq rGrid r i.1.1 i.1.2)
    (hidx₂ : ∀ j : ℕ, ∃ i : nd_DomainIndex d rGrid,
      i.1.1 = j ∧ s ∈ nd_selectedEq rGrid (2 * r) i.1.1 i.1.2)
    (hcross : s ∈ nd_positiveCrossEvent rGrid r) :
    ∀ᶠ j : ℕ in atTop, s ∈ nd_sepPairEvent rGrid r j := by
  have hgap := nd_eventually_selectedDomainsSeparated hd hrGrid hr s hs
    hb₁ hb₂ hcross
  filter_upwards [hgap] with j hj
  obtain ⟨i₁, hj₁, hsel₁⟩ := hidx₁ j
  obtain ⟨i₂, hj₂, hsel₂⟩ := hidx₂ j
  exact nd_mem_sepPairEvent_of_selected hrGrid j s hs i₁ i₂
    hj₁ hj₂ hsel₁ hsel₂ (hj i₁ i₂ hj₁ hj₂ hsel₁ hsel₂)

end HigherDimLQGMetric.DGZ
