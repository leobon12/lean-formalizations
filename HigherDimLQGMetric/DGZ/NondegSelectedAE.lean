import HigherDimLQGMetric.DGZ.NondegLocalZeroCompare
import HigherDimLQGMetric.DGZ.NondegCollarAE

/-! Under a joint limit law, a finite global zero-set code equals its local code. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_ae_selectedEq_iff_localSelectedEq_of_tendsto
    {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r) (ns : ℕ → ℕ)
    {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i) (m : ℕ) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
      (s ∈ nd_selectedEq rGrid r i.1.1 i.1.2 ↔
        s ∈ nd_localSelectedEq i (nd_shellInDomain r i) m i.1.1 i.1.2) := by
  have hd : 0 < d := by have := h.dim; omega
  have hAcomp := nd_isCompact_shellInDomain r i hsub
  have hAne := nd_shellInDomain_nonempty hd hr.le i hsub
  have hpseudo := nd_ae_pseudoSet_of_tendsto h hH hq0 hq1 rGrid ns hlim
  have hLE := nd_ae_globalLE_of_tendsto h hH hq0 hq1 rGrid ns hlim i
  have hNN0 := nd_ae_nonnegLocalSet_of_tendsto h hH hq0 hq1 rGrid ns hlim i 0
  have hNNm := nd_ae_nonnegLocalSet_of_tendsto h hH hq0 hq1 rGrid ns hlim i m
  have hdiag := nd_ae_localDiagSet_of_tendsto hH q rGrid ns hlim i 0
  have hinside := nd_ae_allInsideExitSet_of_tendsto h hH hq0 hq1
    rGrid ns hlim i hAcomp hAne
  have houtside := nd_ae_allOutsideExitSet_of_tendsto h hH hq0 hq1
    rGrid ns hlim i hAcomp hAne
  have hcomp := nd_ae_finiteCompSet_of_tendsto h hH hq0 hq1
    rGrid ns hlim i m
  have hcollar := nd_ae_collarForAll_of_tendsto h hH hq0 hq1
    rGrid r hrGrid hr ns hlim
  filter_upwards [hpseudo, hLE, hNN0, hNNm, hdiag, hinside, houtside,
    hcomp, hcollar] with s hs hsLE hsNN0 hsNNm hsdiag hsinside
      hsoutside hscomp hscollar
  obtain ⟨c, hc, hcρ, hsC⟩ := hscollar i hsub
  constructor
  · intro hsel
    have hloc := nd_mem_localSelectedEq_of_globalSelectedEq hd hrGrid hr i s
      hs hsLE hsNN0 hsinside hsel
    exact (nd_localSelectedEq_iff_of_finiteCompSet hd hr.le i hsub m i.1.1 i.1.2
      s hscomp hsNN0 hsNNm).1 hloc
  · intro hloc
    have hloc0 := (nd_localSelectedEq_iff_of_finiteCompSet hd hr.le i hsub
      m i.1.1 i.1.2 s hscomp hsNN0 hsNNm).2 hloc
    exact nd_mem_globalSelectedEq_of_localSelectedEq hd hrGrid hr i hsub s
      hs hsLE hsNN0 hsdiag hsinside hsoutside hc hcρ hsC hloc0

end HigherDimLQGMetric.DGZ
