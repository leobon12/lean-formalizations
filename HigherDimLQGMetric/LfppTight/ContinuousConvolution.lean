import HigherDimLQGMetric.ConvField.ContBound
import Mathlib.Analysis.Convolution

/-!
# Continuous convolution of a bounded perturbation

The convolution kernel is integrable and a bounded continuous function has a
continuous convolution with it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped Convolution

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_continuous_conv_of_bddCont {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (f : C(Rd d, ℝ))
    {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    Continuous (fun z => ∫ w : Rd d, convKernelEps κ ε (z - w) * f w) := by
  have hfbd : BddAbove (Set.range fun z : Rd d => ‖f z‖) := by
    refine ⟨M, ?_⟩
    rintro y ⟨z, rfl⟩
    simpa only [Real.norm_eq_abs] using hM z
  have hc : Continuous (⇑f ⋆ convKernelEps κ ε) :=
    hfbd.continuous_convolution_left_of_integrable
      (ContinuousLinearMap.lsmul ℝ ℝ) f.continuous
      (integrable_convKernelEps hd hκ hε)
  convert hc using 1
  ext z
  simp only [convolution_def]
  apply integral_congr_ae
  filter_upwards with w
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  ring

end HigherDimLQGMetric
