import HigherDimLQGMetric.LfppTight.PureClosureProper
import HigherDimLQGMetric.LfppTight.PureTight

/-! The full tight-family statement for a normalized whole-space LGF. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_pure_tightFamily (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    TightFamily P (fun ε ω => toCMapRd
      ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) (Ioo (0 : ℝ) 1) := by
  refine ⟨?_, l6a_pure_normalized_tight hL1e hDGZ hAdapter P h hh, ?_⟩
  · intro ε hε
    exact l6a_aemeasurable_raw_metric hDGZ.dim κ hDGZ.kernel ξ hε.1 P h hh
  · intro μ hμ
    exact l6a_pure_closure_good hL1e hDGZ hAdapter P h hh μ hμ

end HigherDimLQGMetric
