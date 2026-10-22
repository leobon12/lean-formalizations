import HigherDimLQGMetric.DGZ.NondegGap
import HigherDimLQGMetric.DGZ.NondegConnectedAE

/-! The bounded connected random cubical thickening has an indexed finite code. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_selectedIndex_unique {rGrid r : ℝ}
    (i₁ i₂ : nd_DomainIndex d rGrid) (s : nd_Joint d rGrid)
    (hj : i₁.1.1 = i₂.1.1)
    (hsel₁ : s ∈ nd_selectedEq rGrid r i₁.1.1 i₁.1.2)
    (hsel₂ : s ∈ nd_selectedEq rGrid r i₂.1.1 i₂.1.2) : i₁ = i₂ := by
  have hS : i₁.1.2 = i₂.1.2 := by
    apply Finset.ext
    intro z
    exact (hsel₁ z).symm.trans (by simpa only [hj] using hsel₂ z)
  exact Subtype.ext (Prod.ext hj hS)

theorem nd_exists_selectedIndex_of_bounded_connected
    {rGrid r : ℝ} (hrGrid : 0 < rGrid) (j : ℕ) (s : nd_Joint d rGrid)
    (hbounded : s ∈ nd_boundedZeroEvent rGrid r)
    (hconnected : IsConnected (nd_thickening rGrid r j s)) :
    ∃ i : nd_DomainIndex d rGrid,
      i.1.1 = j ∧ s ∈ nd_selectedEq rGrid r i.1.1 i.1.2 := by
  let S : Finset (Zd d) :=
    (nd_selectedCell_finite hrGrid r j s (nd_zeroSet_isBounded_of_event hbounded)).toFinset
  have hsel : s ∈ nd_selectedEq rGrid r j S := by
    intro z
    simp only [S, Set.Finite.mem_toFinset]
    rfl
  have hconn : IsConnected (nd_boxUnion rGrid j S) := by
    rw [← nd_thickening_eq_boxUnion_of_selected rGrid r j s S hsel]
    exact hconnected
  exact ⟨⟨(j, S), hconn⟩, rfl, hsel⟩

theorem nd_ae_exists_selectedIndex_of_tendsto
    {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (ns : ℕ → ℕ)
    {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ))
    (hbounded : ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
      s ∈ nd_boundedZeroEvent rGrid r) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
      ∀ j : ℕ, ∃ i : nd_DomainIndex d rGrid,
        i.1.1 = j ∧ s ∈ nd_selectedEq rGrid r i.1.1 i.1.2 := by
  apply ae_all_iff.mpr
  intro j
  have hconn := nd_ae_isConnected_thickening_of_tendsto h hH hq0 hq1
    rGrid r hrGrid hr j ns hlim hbounded
  filter_upwards [hbounded, hconn] with s hsB hsC
  exact nd_exists_selectedIndex_of_bounded_connected hrGrid j s hsB hsC

end HigherDimLQGMetric.DGZ
