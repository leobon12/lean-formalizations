import HigherDimLQGMetric.DGZ.NondegGoodBound

/-! Factorization for separated good codes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_goodCode_factor_of_separated
    {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ)) (j : ℕ)
    (i : nd_GoodIndex (d := d) rGrid r (2 * r) j)
    (k : nd_GoodIndex (d := d) rGrid (2 * r) r j)
    (hsep : nd_domainSeparated rGrid i.1 k.1) :
    (μ : Measure (nd_Joint d rGrid))
      (nd_goodCodeEvent rGrid r (2 * r) j i ∩
        nd_goodCodeEvent rGrid (2 * r) r j k) =
      (μ : Measure (nd_Joint d rGrid))
        (nd_goodCodeEvent rGrid r (2 * r) j i) *
      (μ : Measure (nd_Joint d rGrid))
        (nd_goodCodeEvent rGrid (2 * r) r j k) := by
  exact nd_selectedEq_indep_of_domainSeparated h hH hq0 hq1
    rGrid r (2 * r) hrGrid hr (mul_pos (by norm_num) hr)
    ns hns hlim i.1 k.1 i.2.2.1 k.2.2.1 hsep

end HigherDimLQGMetric.DGZ
