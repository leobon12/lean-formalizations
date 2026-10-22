import HigherDimLQGMetric.LfppTight.MedianSmall
import HigherDimLQGMetric.LfppTight.SphereMeanVariance

/-! A7(4): comparison of LFPP medians at small cutoffs, with no scalar-tail premise. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open HigherDimLFPP (Rd WN)

namespace HigherDimLQGMetric

theorem l6a_median_comparison_small_final (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q β : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : WN d → Ω' → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P' W)
    (G : ℝ → Rd d → Ω' → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1,
      HigherDimLFPP.IsBandVersion P' W κ ε 1 (G ε)) :
    ∃ m M ε₀ : ℝ, 0 < m ∧ 0 ≤ M ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        m ^ 2 * DGZ.aHat P' G ξ ε ≤ aEps κ ξ ε ∧
        aEps κ ξ ε ≤ M ^ 2 * DGZ.aHat P' G ξ ε := by
  obtain ⟨L, _, htail⟩ := l6a_uniform_sphereMean_tail hDGZ.dim κ hDGZ.kernel P h hh
  exact l6a_median_comparison_small hL1e hDGZ hAdapter hβ0 hβ
    P h hh P' W hW G hG htail

end HigherDimLQGMetric
