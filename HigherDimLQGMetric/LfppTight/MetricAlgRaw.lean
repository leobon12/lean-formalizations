import HigherDimLQGMetric.LfppTight.MetricSepTail
import HigherDimLQGMetric.LfppTight.ClosureTail

/-! Algebraic metric identities of normalized LFPP and their closed limit event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_normMetric_mem_alg {d : ℕ} (ξ a : ℝ) (ha : 0 < a)
    (φ : Rd d → ℝ) (hφ : Continuous φ) :
    DGZ.normMetricC ξ φ a ∈ metricAlgSet_select := by
  refine ⟨fun x => ?_, fun x y => ?_, fun x y z => ?_⟩
  · rw [DGZ.normMetricC_apply hφ, DGZ.lfppMetric_self, mul_zero]
  · rw [DGZ.normMetricC_apply hφ, DGZ.normMetricC_apply hφ,
      DGZ.lfppMetric_comm]
  · rw [DGZ.normMetricC_apply hφ, DGZ.normMetricC_apply hφ,
      DGZ.normMetricC_apply hφ, ← mul_add]
    exact mul_le_mul_of_nonneg_left (DGZ.lfppMetric_triangle hφ x y z)
      (inv_pos.mpr ha).le

theorem l6a_ae_raw_mem_alg {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) ∈
      metricAlgSet_select := by
  have hae : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε
  filter_upwards [l10a_ae_continuous_convMollify hd κ hκ P h hh hε]
    with ω hc
  change DGZ.normMetricC ξ (convMollify κ ε (h ω)) (aEps κ ξ ε) ∈
    metricAlgSet_select
  exact l6a_normMetric_mem_alg ξ (aEps κ ξ ε) hae _ hc

end HigherDimLQGMetric
