import HigherDimLQGMetric.ConvField.Joint

/-! Almost-sure joint continuity of the convolution field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l2b_ae_convMollify_continuousOn (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ContinuousOn
      (fun p : ℝ × Rd d => convMollify κ p.1 (h ω) p.2) (Ioi 0 ×ˢ univ) := by
  filter_upwards [l2b_radial d hd κ hκ P h hh,
    hh.1.ae_continuousOn_sphereAvg hd, l2b_ae_growth_all hd hh]
    with ω hrad hcont hgrowth
  have hlog : ContinuousOn (fun p : ℝ × Rd d => Real.log p.1) (Ioi 0 ×ˢ univ) :=
    Real.continuousOn_log.comp continuous_fst.continuousOn (fun p hp => hp.1.ne')
  have hmap : ContinuousOn (fun p : ℝ × Rd d => (Real.log p.1, p.2))
      (Ioi 0 ×ˢ univ) := hlog.prodMk continuous_snd.continuousOn
  have hright : ContinuousOn (fun p : ℝ × Rd d =>
      (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          convKernelEps κ p.1 (r • e₁ d) * sphereAvg (h ω) r p.2)
      (Ioi 0 ×ˢ univ) := by
    have hc := l2b_continuous_radial_integral hd hκ (h ω) hcont.2 hgrowth
    have hc' : ContinuousOn (fun p : ℝ × Rd d =>
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          convKernelEps κ p.1 (r • e₁ d) * sphereAvg (h ω) r p.2)
        (Ioi 0 ×ˢ univ) := by
      have hcomp := hc.comp_continuousOn hmap
      exact hcomp.congr (by
        intro p hp
        simp only [Function.comp_apply]
        rw [Real.exp_log hp.1])
    exact continuousOn_const.mul hc'
  refine hright.congr ?_
  intro p hp
  exact hrad p.1 hp.1 p.2

end HigherDimLQGMetric
