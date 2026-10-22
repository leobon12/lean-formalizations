import HigherDimLQGMetric.ConvField.CenteredDensity

/-! Gaussianity of the centered convolution field, obtained from the compact test process. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l2b_measurable_pairCenteredKernel (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistRd d) (hh : Measurable h)
    {ε : ℝ} (hε : 0 < ε) (x : Rd d) :
    Measurable fun ω => l2b_pairCenteredKernel hd hκ hε x (h ω) := by
  have hm (n : ℕ) : StronglyMeasurable fun ω : Ω =>
      h ω (l2b_centeredTruncTest hd hκ hε x n).1 :=
    ((measurable_distOn_apply _).comp hh).stronglyMeasurable
  exact (StronglyMeasurable.limUnder (l := atTop) hm).measurable

theorem l2b_isGaussianProcess_pairCenteredKernel (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) :
    IsGaussianProcess
      (fun (x : Rd d) (ω : Ω) => l2b_pairCenteredKernel hd hκ hε x (h ω)) P := by
  let Yn : ℕ → Rd d → Ω → ℝ := fun n x ω =>
    h ω (l2b_centeredTruncTest hd hκ hε x n).1
  let Y : Rd d → Ω → ℝ := fun x ω =>
    l2b_pairCenteredKernel hd hκ hε x (h ω)
  have hG (n : ℕ) : IsGaussianProcess (Yn n) P :=
    hh.1.gaussian.comp_right (fun x => l2b_centeredTruncTest hd hκ hε x n)
  have hC (n : ℕ) (x : Rd d) : ∫ ω, Yn n x ω ∂P = 0 :=
    hh.1.centered (l2b_centeredTruncTest hd hκ hε x n)
  have hm (x : Rd d) : Measurable (Y x) :=
    l2b_measurable_pairCenteredKernel d hd κ hκ h hh.1.measurable hε x
  have hlim (x : Rd d) : ∀ᵐ ω ∂P,
      Tendsto (fun n => Yn n x ω) atTop (𝓝 (Y x ω)) := by
    filter_upwards [l2b_ae_centeredTrunc_tendsto d hd κ hκ P h hh,
      l2b_ae_pairCenteredKernel_eq_convMollifyNorm d hd κ hκ P h hh]
      with ω hω hp
    have ht := hω ε hε x
    rwa [← hp ε hε x] at ht
  exact LQGMetric.CircleAvgIndep.isGaussianProcess_of_ae_tendsto hG hC hm hlim

theorem l2b_tendsto_centeredKernel_covariance (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) (x y : Rd d) :
    Tendsto (fun n : ℕ => logCovRd
      (l2b_centeredTruncTest hd hκ hε x n).1
      (l2b_centeredTruncTest hd hκ hε y n).1) atTop
      (𝓝 cov[(fun ω => l2b_pairCenteredKernel hd hκ hε x (h ω)),
        (fun ω => l2b_pairCenteredKernel hd hκ hε y (h ω)); P]) := by
  let Yn : ℕ → Rd d → Ω → ℝ := fun n z ω =>
    h ω (l2b_centeredTruncTest hd hκ hε z n).1
  let Y : Rd d → Ω → ℝ := fun z ω =>
    l2b_pairCenteredKernel hd hκ hε z (h ω)
  have hG (n : ℕ) : IsGaussianProcess (Yn n) P :=
    hh.1.gaussian.comp_right (fun z => l2b_centeredTruncTest hd hκ hε z n)
  have hC (n : ℕ) (z : Rd d) : ∫ ω, Yn n z ω ∂P = 0 :=
    hh.1.centered (l2b_centeredTruncTest hd hκ hε z n)
  have hm (z : Rd d) : Measurable (Y z) :=
    l2b_measurable_pairCenteredKernel d hd κ hκ h hh.1.measurable hε z
  have hlim (z : Rd d) : ∀ᵐ ω ∂P,
      Tendsto (fun n => Yn n z ω) atTop (𝓝 (Y z ω)) := by
    filter_upwards [l2b_ae_centeredTrunc_tendsto d hd κ hκ P h hh,
      l2b_ae_pairCenteredKernel_eq_convMollifyNorm d hd κ hκ P h hh]
      with ω hω hp
    have ht := hω ε hε z
    rwa [← hp ε hε z] at ht
  have ht := LQGMetric.CircleAvgIndep.tendsto_covariance_of_ae_tendsto
    hG hC hm hlim x y
  simpa only [hh.1.covariance_eq, Yn, Y] using ht

end HigherDimLQGMetric
