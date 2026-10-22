import HigherDimLQGMetric.LfppTight.UnitCross
import HigherDimLQGMetric.LfppTight.CrossMeas
import HigherDimLQGMetric.LfppTight.MedianPos
import HigherDimLQGMetric.Weak.DetLFPPMetric
import HigherDimLQGMetric.DGZ.Continuity

/-! Unit-scale crossing for LFPP from tightness and positive metric limits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_cross_norm_iff_raw {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) (v : DistRd d)
    (hfield : Continuous fun z => convMollify κ ε v z)
    (b c : ℝ) :
    (supPairs (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v))
        (ball (0 : Rd d) b) ≤
      ENNReal.ofReal c * infPairs
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v))
        (sphere 0 b) (sphere 0 1)) ↔
    (supPairs (lfppDist κ ξ ε v) (ball (0 : Rd d) b) ≤
      ENNReal.ofReal c * infPairs (lfppDist κ ξ ε v)
        (sphere 0 b) (sphere 0 1)) := by
  have ha : 0 < (aEps κ ξ ε)⁻¹ :=
    inv_pos.mpr (l6a_aEps_pos hd κ hκ ξ hε)
  have hdist : Continuous (lfppDist κ ξ ε v) := by
    change Continuous (fun p : Rd d × Rd d =>
      DGZ.lfppMetric ξ (convMollify κ ε v) p.1 p.2)
    exact DGZ.continuous_lfppMetric hfield ξ
  have heq : toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v) =
      (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v := by
    apply funext
    intro q
    rw [toCMapRd_apply_of_continuous (hdist.const_smul _)]
  rw [heq]
  have hsmul : ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v) =
      fun p => (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε v p := rfl
  rw [hsmul]
  exact l6a_cross_iff_mul (lfppDist κ ξ ε v)
    (ball 0 b) (sphere 0 b) (sphere 0 1) (c := c) ha

theorem l6a_unitCross_lfpp_of_tightFamily {d : ℕ}
    (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (hT : TightFamily P
      (fun ε ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))
      (Ioo (0 : ℝ) 1))
    {p C : ℝ} (hp : p < 1) (hC : 0 < C) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 4 ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal p ≤ P {ω |
        supPairs (lfppDist κ ξ ε (h ω)) (ball (0 : Rd d) b) ≤
          ENNReal.ofReal C⁻¹ * infPairs (lfppDist κ ξ ε (h ω))
            (sphere 0 b) (sphere 0 1)} := by
  obtain ⟨b, hb, hb4, hU⟩ :=
    l6a_unitCross_of_tightOver (l6a_tightFamily_to_tightOver hT) hp hC
  refine ⟨b, hb, hb4, ?_⟩
  intro ε hε
  have hc := l10a_ae_continuous_convMollify hd κ hκ P h hh hε.1
  have hevent : P {ω |
      supPairs (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))
        (ball (0 : Rd d) b) ≤
      ENNReal.ofReal C⁻¹ * infPairs
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))
        (sphere 0 b) (sphere 0 1)} =
    P {ω | supPairs (lfppDist κ ξ ε (h ω)) (ball 0 b) ≤
      ENNReal.ofReal C⁻¹ * infPairs (lfppDist κ ξ ε (h ω))
        (sphere 0 b) (sphere 0 1)} := by
    apply measure_congr
    filter_upwards [hc] with ω hfield
    exact propext (l6a_cross_norm_iff_raw hd κ hκ ξ hε.1
      (h ω) hfield b C⁻¹)
  rw [←hevent]
  exact hU ε hε

end HigherDimLQGMetric
