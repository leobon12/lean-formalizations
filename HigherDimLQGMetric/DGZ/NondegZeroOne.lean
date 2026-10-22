import HigherDimLQGMetric.DGZ.NondegZeroOneCore

/-! DGZ Lemma 6.9: a subsequential normalized crossing has probability zero or one. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_zeroOne_limitLaw {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧
      ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∀ rGrid r : ℝ, 0 < rGrid → 0 < r →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        ∀ hH : IsDyadicRealization κ P W H,
        ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
        ∀ μ : ProbabilityMeasure (nd_Joint d rGrid),
          Tendsto
            (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
            atTop (𝓝 μ) →
          (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) = 0 ∨
            (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) = 1 := by
  obtain ⟨q₂, hq₂0, hq₂1, hbound⟩ := nd_ae_boundedZeroEvent_of_tendsto h
  refine ⟨q₂, hq₂0, hq₂1, ?_⟩
  intro q hq hq1 rGrid r hrGrid hr Ω _ P W H hH ns hns μ hlim
  have hb₁ := hbound q hq hq1 rGrid r hr Ω P W H hH ns μ hlim
  have hb₂ := hbound q hq hq1 rGrid (2 * r)
    (mul_pos (by norm_num) hr) Ω P W H hH ns μ hlim
  exact nd_zeroOne_limitLaw_of_bounded h hH (hq₂0.trans_le hq) hq1
    rGrid r hrGrid hr ns hns hlim hb₁ hb₂

end HigherDimLQGMetric.DGZ
