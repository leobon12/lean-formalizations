import HigherDimLQGMetric.DGZ.NondegConnected

/-! Almost-sure connectedness of the random thickening under a joint limit law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_ae_exitForAll_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hr : 0 < r) (ns : ℕ → ℕ)
    {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ)) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
      ∀ i : nd_DomainIndex d rGrid,
        lsph (0 : Rd d) r ⊆ nd_domain rGrid i →
        ∀ x : Rd d, x ∉ nd_domain rGrid i →
          nd_setInf (frontier (nd_domain rGrid i)) (lsph 0 r) s.1 ≤
            nd_pointSetInf (lsph 0 r) s.1 x := by
  apply ae_all_iff.mpr
  intro i
  by_cases hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i
  · let A : Set (nd_domain rGrid i) := {y | y.1 ∈ lsph (0 : Rd d) r}
    have hAimage : ((↑) '' A : Set (Rd d)) = lsph (0 : Rd d) r := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨⟨y, hsub hy⟩, hy, rfl⟩
    have hAcompact : IsCompact A := by
      rw [Subtype.isCompact_iff, hAimage]
      exact tn_isCompact_lsph 0 r
    have hAne : A.Nonempty := by
      obtain ⟨y, hy⟩ := lsph_nonempty (by have := h.dim; omega : 0 < d) 0 hr.le
      exact ⟨⟨y, hsub hy⟩, hy⟩
    have hae := nd_ae_allOutsideExitSet_of_tendsto h hH hq0 hq1
      rGrid ns hlim i hAcompact hAne
    filter_upwards [hae] with s hs _ x hx
    have hxrel := Set.mem_iInter.mp hs ⟨x, hx⟩
    change s ∈ nd_outsideExitSet rGrid i A x at hxrel
    simpa only [nd_outsideExitSet, Set.mem_ofPred_eq, hAimage,
      ← nd_pointSetInf_eq_setInf] using hxrel
  · exact Filter.Eventually.of_forall fun _s hsub' => False.elim (hsub hsub')

theorem nd_ae_isConnected_thickening_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r) (j : ℕ) (ns : ℕ → ℕ)
    {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ))
    (hbounded : ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
      s ∈ nd_boundedZeroEvent rGrid r) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
      IsConnected (nd_thickening rGrid r j s) := by
  have hpseudo := nd_ae_pseudoSet_of_tendsto h hH hq0 hq1 rGrid ns hlim
  have hexit := nd_ae_exitForAll_of_tendsto h hH hq0 hq1 rGrid r hr ns hlim
  filter_upwards [hpseudo, hbounded, hexit] with s hs hbound hexit'
  let S : Finset (Zd d) :=
    (nd_selectedCell_finite hrGrid r j s (nd_zeroSet_isBounded_of_event hbound)).toFinset
  have hsel : s ∈ nd_selectedEq rGrid r j S := by
    intro z
    simp only [S, Set.Finite.mem_toFinset]
    rfl
  exact nd_isConnected_thickening_of_exit (by have := h.dim; omega : 2 ≤ d)
    hrGrid hr j s hs S hsel hexit'

end HigherDimLQGMetric.DGZ
