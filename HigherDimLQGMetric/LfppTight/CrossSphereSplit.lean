import HigherDimLQGMetric.LfppTight.MedianBridge
import HigherDimLQGMetric.LfppTight.MetricIdent
import HigherDimLQGMetric.LfppTight.CrossCompare

/-! A global sphere-mean factor cancels from every crossing event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_cross_sphereMean_iff {d : ℕ}
    (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d)
    (hc : Continuous fun z => convMollify κ ε h z)
    (A B C : Set (Rd d)) (c : ℝ) :
    (supPairs (lfppDist κ ξ ε h) A ≤
      ENNReal.ofReal c * infPairs (lfppDist κ ξ ε h) B C) ↔
    (supPairs (l6a_metricOfFieldC ξ 1
      (l6a_toFieldCMap (convMollifyNorm κ ε h))) A ≤
      ENNReal.ofReal c * infPairs
        (l6a_metricOfFieldC ξ 1
          (l6a_toFieldCMap (convMollifyNorm κ ε h))) B C) := by
  let Z : Rd d → ℝ := convMollifyNorm κ ε h
  have hZ : Continuous Z := hc.sub continuous_const
  have hcont : l6a_toFieldCMap Z = (⟨Z, hZ⟩ : C(Rd d, ℝ)) :=
    dite_eq_left hZ
  have hmetric : (l6a_metricOfFieldC ξ 1 (l6a_toFieldCMap Z) :
      Rd d × Rd d → ℝ) =
      fun p => HigherDimLFPP.lfppDistOn ξ Z univ p.1 p.2 := by
    funext p
    rw [hcont]
    have hm := l6a_metricOfFieldC_eq_normMetricC ξ 1
      (⟨Z, hZ⟩ : C(Rd d, ℝ))
    simp only [inv_one] at hm
    rw [hm]
    change (DGZ.normMetricC ξ Z 1) p = _
    rw [DGZ.normMetricC_apply hZ]
    simp only [inv_one, one_mul]
    rfl
  rw [hmetric]
  have hsplit : (lfppDist κ ξ ε h : Rd d × Rd d → ℝ) =
      fun p => Real.exp (ξ * l6a_convSphereMean κ ε h) *
        HigherDimLFPP.lfppDistOn ξ Z univ p.1 p.2 := by
    funext p
    exact l6a_lfppDist_sphereMean_split κ ξ ε h p
  rw [hsplit]
  exact l6a_cross_iff_mul
    (fun p : Rd d × Rd d => HigherDimLFPP.lfppDistOn ξ Z univ p.1 p.2)
    A B C (Real.exp_pos _)

end HigherDimLQGMetric
