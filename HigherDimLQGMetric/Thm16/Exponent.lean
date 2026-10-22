import HigherDimLQGMetric.Thm16.MedianCompare
import HigherDimLQGMetric.Thm16.MedianExponent
import HigherDimLQGMetric.KernelIndep.KernelIndep
import HigherDimLFPP.Field.WhiteNoise

/-! The convolution LFPP median has the canonical distance exponent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem aEps_exponent {d : ℕ} (hd : 3 ≤ d)
    {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Tendsto (fun ε => Real.log (aEps κ ξ ε) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - ξ * distExp d ξ)) := by
  obtain ⟨W, hW⟩ := HigherDimLFPP.exists_isWhiteNoise d
  let P : Measure (ℕ → ℝ) := LQGDimension.ExistAsm.stdP
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  obtain ⟨G, hG⟩ := exists_bandVersion_family hκ hW
  obtain ⟨m, M, ε₀, hm, _hM, hε₀, hcomp⟩ :=
    l9c_aEps_aHat_compare hd hκ hξ hsub hB2 hL6a P W hW G hG
  exact l9c_aEps_exponent_of_median_bounds hd hξ hsub hκ hB2
    P W hW G hG hm hε₀ hcomp

end HigherDimLQGMetric
