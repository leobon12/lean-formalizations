import HigherDimLQGMetric.DGZ.NondegSelectedAE
import HigherDimLQGMetric.DGZ.NondegIndep

/-! Factorization of separated finite zero-set codes under a joint limit law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_selectedEq_indep_of_tendsto
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
    (m : ℕ) (ρ : ℝ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0)
    (hsep : ∀ z ∈ nd_domain rGrid i₁, ∀ w ∈ nd_domain rGrid i₂,
      2 * ρ * ((2 : ℝ)⁻¹ ^ m) < ‖z - w‖) :
    (μ : Measure (nd_Joint d rGrid))
      (nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2 ∩
        nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2) =
      (μ : Measure (nd_Joint d rGrid))
        (nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2) *
      (μ : Measure (nd_Joint d rGrid))
        (nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2) := by
  let A₁ := nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2
  let A₂ := nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2
  let B₁ := nd_localSelectedEqC i₁ (nd_shellInDomain r₁ i₁) m i₁.1.1 i₁.1.2
  let B₂ := nd_localSelectedEqC i₂ (nd_shellInDomain r₂ i₂) m i₂.1.1 i₂.1.2
  let f₁ : nd_Joint d rGrid → C(nd_domain rGrid i₁ × nd_domain rGrid i₁, ℝ) :=
    fun s => s.2 (i₁, m)
  let f₂ : nd_Joint d rGrid → C(nd_domain rGrid i₂ × nd_domain rGrid i₂, ℝ) :=
    fun s => s.2 (i₂, m)
  have hB₁ : MeasurableSet B₁ :=
    nd_measurableSet_localSelectedEqC i₁ (nd_isCompact_shellInDomain r₁ i₁ hsub₁)
      m i₁.1.1 i₁.1.2
  have hB₂ : MeasurableSet B₂ :=
    nd_measurableSet_localSelectedEqC i₂ (nd_isCompact_shellInDomain r₂ i₂ hsub₂)
      m i₂.1.1 i₂.1.2
  have heq₁ : A₁ =ᵐ[(μ : Measure (nd_Joint d rGrid))] f₁ ⁻¹' B₁ := by
    filter_upwards [nd_ae_selectedEq_iff_localSelectedEq_of_tendsto
      h hH hq0 hq1 rGrid r₁ hrGrid hr₁ ns hlim i₁ hsub₁ m] with s hs
    exact propext hs
  have heq₂ : A₂ =ᵐ[(μ : Measure (nd_Joint d rGrid))] f₂ ⁻¹' B₂ := by
    filter_upwards [nd_ae_selectedEq_iff_localSelectedEq_of_tendsto
      h hH hq0 hq1 rGrid r₂ hrGrid hr₂ ns hlim i₂ hsub₂ m] with s hs
    exact propext hs
  have hind := nd_indepFun_jointLimit h hH q rGrid ns hns hlim m i₁ i₂ ρ hρ hsep
  calc
    (μ : Measure (nd_Joint d rGrid)) (A₁ ∩ A₂) =
        (μ : Measure (nd_Joint d rGrid)) ((f₁ ⁻¹' B₁) ∩ (f₂ ⁻¹' B₂)) :=
      measure_congr (heq₁.inter heq₂)
    _ = (μ : Measure (nd_Joint d rGrid)) (f₁ ⁻¹' B₁) *
          (μ : Measure (nd_Joint d rGrid)) (f₂ ⁻¹' B₂) :=
      hind.measure_inter_preimage_eq_mul B₁ B₂ hB₁ hB₂
    _ = (μ : Measure (nd_Joint d rGrid)) A₁ *
          (μ : Measure (nd_Joint d rGrid)) A₂ := by
      rw [measure_congr heq₁, measure_congr heq₂]

end HigherDimLQGMetric.DGZ
