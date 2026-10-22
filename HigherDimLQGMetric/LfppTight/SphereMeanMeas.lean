import HigherDimLQGMetric.LfppTight.SphereMeanCont
import HigherDimLQGMetric.ConvField.MeanTest
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Measurability of the convolved sphere mean through compact test approximants. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_aemeasurable_sphereMean {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) :
    AEMeasurable (fun ω => l6a_convSphereMean κ ε (h ω)) P := by
  let X : ℕ → Ω → ℝ := fun n ω => h ω (l2b_meanTruncTest hd hκ hε n)
  have hXm (n : ℕ) : AEMeasurable (X n) P := by
    exact ((measurable_distOn_apply (l2b_meanTruncTest hd hκ hε n)).comp
      hh.1.measurable).aemeasurable
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => X n ω) atTop
        (𝓝 (l6a_convSphereMean κ ε (h ω))) := by
    filter_upwards [l2b_ae_tendsto_sphereMean_convTrunc d hd κ hκ P h hh]
      with ω hw
    simpa only [X, l6a_convSphereMean,
      l2b_meanTruncTest_pair hd hκ hε] using hw ε hε
  exact aemeasurable_of_tendsto_metrizable_ae atTop hXm hlim

end HigherDimLQGMetric
