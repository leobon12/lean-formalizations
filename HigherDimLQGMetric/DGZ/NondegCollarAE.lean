import HigherDimLQGMetric.DGZ.NondegCollarLevelChoice

/-! Simultaneous collar relations for all countably many indexed domains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_ae_collarForAll_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r) (ns : ℕ → ℕ)
    {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ)) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
      ∀ i : nd_DomainIndex d rGrid,
        lsph (0 : Rd d) r ⊆ nd_domain rGrid i →
        ∃ c : ℝ, 0 < c ∧ c < nd_gridRadius rGrid i.1.1 ∧
          s ∈ nd_collarSet rGrid i (nd_interiorDist i) c
            (frontier (nd_domain rGrid i)) (nd_shellInDomain r i) := by
  apply ae_all_iff.mpr
  intro i
  by_cases hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i
  · have hd : 0 < d := by have := h.dim; omega
    obtain ⟨c, hc, hcρ, hcA⟩ := nd_exists_shellCollarLevel hd hrGrid hr i hsub
    have hg : Continuous (nd_interiorDist i) := nd_continuous_interiorDist i
    have hgU : ∀ z, z ∉ nd_domain rGrid i → nd_interiorDist i z ≤ 0 := by
      intro z hz
      exact le_of_eq (nd_interiorDist_eq_zero_of_not_mem i hz)
    have hFcomp : IsCompact (frontier (nd_domain rGrid i)) :=
      nd_isCompact_frontier_domain rGrid i
    have hAne : (nd_shellInDomain r i).Nonempty :=
      nd_shellInDomain_nonempty hd hr.le i hsub
    have hFne : (frontier (nd_domain rGrid i)).Nonempty :=
      nd_frontier_domain_nonempty hd rGrid i
        ⟨hAne.some.1, hAne.some.2⟩
    have hAcomp : IsCompact (nd_shellInDomain r i) :=
      nd_isCompact_shellInDomain r i hsub
    have hgF : ∀ z ∈ frontier (nd_domain rGrid i), nd_interiorDist i z ≤ c := by
      intro z hz
      rw [nd_interiorDist_frontier_zero i hz]
      exact hc.le
    have hgA : ∀ z ∈ ((↑) '' nd_shellInDomain r i : Set (Rd d)),
        c ≤ nd_interiorDist i z := by
      rintro z ⟨x, hx, rfl⟩
      exact hcA x hx
    have hae := nd_ae_collarSet_of_tendsto h hH hq0 hq1 rGrid ns hlim i
      hg hc hgU hFcomp hFne hAcomp hAne hgF hgA
    filter_upwards [hae] with s hs _
    exact ⟨c, hc, hcρ, hs⟩
  · exact Filter.Eventually.of_forall fun _s hsub' => False.elim (hsub hsub')

end HigherDimLQGMetric.DGZ
