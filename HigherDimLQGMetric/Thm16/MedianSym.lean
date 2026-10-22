import HigherDimLQGMetric.LfppTight.SphereMeanGaussian
import GaussianLQG.Assembly.MainCoord.Limits

/-! A centered Gaussian scalar lies on each side of zero with probability at least one half. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l9c_sphereMean_half_sides {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ≥0∞)⁻¹ ≤ P {ω | l6a_convSphereMean κ ε (h ω) ≤ 0} ∧
      (2 : ℝ≥0∞)⁻¹ ≤ P {ω | 0 ≤ l6a_convSphereMean κ ε (h ω)} := by
  obtain ⟨hG, hmean⟩ := l6a_hasGaussianLaw_sphereMean hd κ hκ P h hh hε
  have hmed : LQGMetric.IsMedian (P.map (fun ω => l6a_convSphereMean κ ε (h ω))) 0 := by
    rw [hG.map_eq_gaussianReal, hmean]
    exact GaussianLQG.isMedian_gaussianReal 0 _
  exact (LQGMetric.isMedian_map_iff hG.aemeasurable).1 hmed

end HigherDimLQGMetric
