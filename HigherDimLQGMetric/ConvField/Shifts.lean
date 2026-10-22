import HigherDimLQGMetric.ConvField.Spec
import HigherDimLQGMetric.ConvField.Affine

/-! Constant, bounded-continuous, and translation identities for the convolution field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l2b_ae_convMollify_addConst (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d, ∀ c : ℝ,
      convMollify κ ε (addConst (h ω) c) z = convMollify κ ε (h ω) z + c := by
  filter_upwards [l2b_ae_convMollify_tendsto d hd κ hκ P h hh] with ω hω
  intro ε hε z c
  exact l2b_convMollify_addConst_of_tendsto hd hκ hε (hω ε hε z)

theorem l2b_ae_convMollify_addFun (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      ∀ f : C(Rd d, ℝ), ∀ M : ℝ, (∀ w, |f w| ≤ M) →
      convMollify κ ε (addFun (h ω) f) z = convMollify κ ε (h ω) z +
        ∫ w : Rd d, convKernelEps κ ε (z - w) * f w := by
  filter_upwards [l2b_ae_convMollify_tendsto d hd κ hκ P h hh] with ω hω
  intro ε hε z f M hM
  exact l2b_convMollify_addFun_of_tendsto hd hκ hε (hω ε hε z) f M hM

theorem l2b_convMollify_translate (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ε : ℝ) (g : DistRd d) (w z : Rd d) :
    convMollify κ ε (affineComp 1 w g) z = convMollify κ ε g (z + w) :=
  l2b_convMollify_comp_translate hd hκ ε g w z

end HigherDimLQGMetric
