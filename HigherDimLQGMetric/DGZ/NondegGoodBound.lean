import HigherDimLQGMetric.DGZ.NondegPairMeasure

/-! Each one-domain good-code sum is bounded by the crossing probability. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_tsum_goodCode_first_le_cross
    {rGrid r : ℝ} (hd : 0 < d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (j : ℕ) (μ : Measure (nd_Joint d rGrid))
    (hpseudo : ∀ᵐ s ∂μ, s ∈ nd_pseudoSet rGrid) :
    (∑' i : nd_GoodIndex (d := d) rGrid r (2 * r) j,
      μ (nd_goodCodeEvent rGrid r (2 * r) j i)) ≤
      μ (nd_positiveCrossEvent rGrid r) := by
  apply nd_tsum_goodCodeEvent_le rGrid r (2 * r) j μ
    (nd_positiveCrossEvent rGrid r) (nd_pseudoSet rGrid) hpseudo
  intro s hs i hcode
  exact nd_cross_pos_of_selected_avoids_shell hd hrGrid hr s hs i.1
    hcode i.2.2.2

theorem nd_tsum_goodCode_second_le_cross
    {rGrid r : ℝ} (hd : 0 < d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (j : ℕ) (μ : Measure (nd_Joint d rGrid))
    (hpseudo : ∀ᵐ s ∂μ, s ∈ nd_pseudoSet rGrid) :
    (∑' i : nd_GoodIndex (d := d) rGrid (2 * r) r j,
      μ (nd_goodCodeEvent rGrid (2 * r) r j i)) ≤
      μ (nd_positiveCrossEvent rGrid r) := by
  apply nd_tsum_goodCodeEvent_le rGrid (2 * r) r j μ
    (nd_positiveCrossEvent rGrid r) (nd_pseudoSet rGrid) hpseudo
  intro s hs i hcode
  exact nd_cross_pos_of_selected_rev_avoids_shell hd hrGrid hr s hs i.1
    hcode i.2.2.2

end HigherDimLQGMetric.DGZ
