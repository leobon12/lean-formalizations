/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocKernel
import InteractingSLE.Spec.Restart.MarkovChart
import InteractingSLE.Spec.Sec7.Lemma72CChart
import InteractingSLE.Spec.Coupling.WFSLeafFreezeLocal
import InteractingSLE.Spec.Sec5.Aux61MeanIdChart
import InteractingSLE.Spec.Sec5.Aux61ULocCore
import InteractingSLE.Spec.Supplement.GW3LawEvery
import InteractingSLE.Spec.Supplement.GW3LawJointUnion
import InteractingSLE.Foundations.Complex.DerivLog
import InteractingSLE.WangWu.ReverseContactLocal

/-!
# Gaussian kernels read through conformal charts

Packet PROVE-GW4-CLOC, step 2 (deterministic in the measure). If, under a probability measure `Q`, the conditional
characteristic functional of a field `h` given `𝓜` is the Gaussian kernel `rangeKerCF (M ω) (V ω)` of a mean `M` and
an open set `V`, then the field read through a conformal chart `c` (`Chart.chartTransport`, with sign `σ = ±1`) has the
Gaussian kernel of the transported mean and of the chart pre-image `chartPre c V`
(`ae_condExp_cexp_chartTransport`), provided `V ∖ dom c` is open (the covariance of `V` restricted to tests carried
by `dom c` is the covariance of `V ∩ dom c`, `MarkovChart.zeroGFFTestCov_pushTest_chartPre`). The transported mean is
harmonic on the pre-image (`isHarmonicDistOn_chartTransport_pm`). The lift of a component chart of an open component
is harmonic (`harmonicOnNhd_lift_of_isComponentChart`: it is the imaginary part of a continuous, hence holomorphic,
logarithm of the derivative).

Then a Gaussian kernel with a harmonic mean gives the history-marked avoidance criterion of the complement of the
domain with all conditioning information as marks (`WFS.isHistoryAvoidanceLocal_of_retainedKernel`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW4Fix.CLoc

open LocalSets WholeField Restart.MarkovChart

/-! ### The lift of a component chart is harmonic -/

section Lift

variable {R L C : Set ℂ} {c : Chart}

theorem deriv_ne_zero_of_isComponentChart (hc : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    {z : ℂ} (hz : z ∈ C) : deriv c.1 z ≠ 0 := by
  have hconf := GW3Law.isConformal_of_isComponentChart hc hCo hCH
  set w := c.1 z with hw_def
  have hwH : w ∈ H := hc.2.1 hz
  have hzw : c.2.1 w = z := hc.2.2.2.1.1 hz
  have hd₁ : DifferentiableAt ℂ c.1 (c.2.1 w) := by
    rw [hzw]; exact (hc.1 z hz).differentiableAt (hCo.mem_nhds hz)
  have hd₂ : DifferentiableAt ℂ c.2.1 w := (hconf.1 w hwH).differentiableAt (QuantumZipper.isOpen_H.mem_nhds hwH)
  have hev : (fun v => c.1 (c.2.1 v)) =ᶠ[𝓝 w] fun v => v :=
    Filter.eventuallyEq_of_mem (QuantumZipper.isOpen_H.mem_nhds hwH) fun v hv => hconf.2.2 v hv
  have hchain : deriv (fun v => c.1 (c.2.1 v)) w = deriv c.1 (c.2.1 w) * deriv c.2.1 w :=
    deriv_comp w hd₁ hd₂
  rw [hev.deriv_eq, deriv_id'', hzw] at hchain
  intro h0
  rw [h0, zero_mul] at hchain
  exact one_ne_zero hchain

/-- **The lift of a component chart of an open component in `ℍ` is harmonic on the component.** -/
theorem harmonicOnNhd_lift_of_isComponentChart (hc : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H) :
    InnerProductSpace.HarmonicOnNhd c.2.2 C := by
  have hd : DifferentiableOn ℂ (deriv c.1) C := hc.1.deriv hCo
  set Lg : ℂ → ℂ := fun z => (Real.log ‖deriv c.1 z‖ : ℂ) + (c.2.2 z : ℂ) * Complex.I with hLg
  have hne := fun z (hz : z ∈ C) => deriv_ne_zero_of_isComponentChart hc hCo hCH hz
  have hLc : ContinuousOn Lg C := by
    refine ContinuousOn.add ?_ ?_
    · refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact (continuous_norm.comp_continuousOn hd.continuousOn).log fun z hz => norm_ne_zero_iff.2 (hne z hz)
    · exact (Complex.continuous_ofReal.comp_continuousOn hc.2.2.2.2.2.1).mul continuousOn_const
  have hexp : ∀ z ∈ C, Complex.exp (Lg z) = deriv c.1 z := by
    intro z hz
    rw [hLg, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.2 (hne z hz))]
    exact (hc.2.2.2.2.2.2 z hz).symm
  have hLd : DifferentiableOn ℂ Lg C := differentiableOn_of_continuousOn_of_exp_eq hCo hLc hd hexp
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => (Lg z).im) C := fun z hz =>
    (hLd.analyticAt (hCo.mem_nhds hz)).harmonicAt_im
  refine Sec5.Aux61MeanId.harmonicOnNhd_of_eqOn hCo hharm fun z _ => ?_
  simp [hLg]

theorem coe_dom_of_isComponentChart (hc : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H) :
    (c.dom : Set ℂ) = C := by
  rw [(GW3Law.isConformal_of_isComponentChart hc hCo hCH).coe_dom, GW3Joint.image_inv_eq_of_isComponentChart hc]

end Lift

/-! ### One chart step for a Gaussian kernel -/

section OneChart

variable {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

omit [IsProbabilityMeasure Q] in
/-- **One chart step.** The Gaussian kernel of `h` on `V` gives the Gaussian kernel of the chart field
`chartTransport c σ a k h` (`σ = ±1`) on `chartPre c V`, with the transported mean. -/
theorem ae_condExp_cexp_chartTransport {c : Chart} (hc : c.IsConformal) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (a k : ℝ) {h : Ω → DistOn upperHalfPlaneOpens}
    {M : Ω → DistOn upperHalfPlaneOpens} {V : Ω → Set ℂ}
    (hV : ∀ᵐ ω ∂Q, IsOpen (V ω) ∧ IsOpen (V ω \ c.dom))
    (hker : ∀ φ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜] =ᵐ[Q] fun ω => rangeKerCF (M ω) (V ω) φ)
    (ψ : TestOn upperHalfPlaneOpens) :
    Q[fun ω => Complex.exp (Complex.I * (Chart.chartTransport hc σ a k (h ω) ψ : ℂ)) | 𝓜] =ᵐ[Q]
      fun ω => rangeKerCF (Chart.chartTransport hc σ a k (M ω)) (chartPre c (V ω)) ψ := by
  set d : ℝ := a * Chart.oneDist ψ + k * Chart.liftDist c ψ with hd
  set φ : TestOn upperHalfPlaneOpens := σ • Chart.pushTest hc ψ with hφ
  have happ : ∀ T : DistOn upperHalfPlaneOpens, Chart.chartTransport hc σ a k T ψ = T φ + d := fun T => by
    rw [Chart.chartTransport_apply', hφ, map_smul, smul_eq_mul, hd]
    ring
  have hsplit : (fun ω => Complex.exp (Complex.I * (Chart.chartTransport hc σ a k (h ω) ψ : ℂ))) =
      Complex.exp (Complex.I * (d : ℂ)) • fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) := by
    funext ω
    rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, happ]
    push_cast
    ring_nf
  have hcov : ∀ ω, IsOpen (V ω) → IsOpen (V ω \ c.dom) →
      zeroGFFTestCov (V ω) φ φ = zeroGFFTestCov (chartPre c (V ω)) ψ ψ := fun ω h1 h2 => by
    rcases hσ with rfl | rfl
    · rw [hφ, one_smul]
      exact zeroGFFTestCov_pushTest_chartPre hc h1 h2 ψ ψ
    · rw [hφ, neg_one_smul, FunLike.coe_neg, WangWu.zeroGFFTestCov_neg_neg]
      exact zeroGFFTestCov_pushTest_chartPre hc h1 h2 ψ ψ
  rw [hsplit]
  filter_upwards [condExp_smul (Complex.exp (Complex.I * (d : ℂ)))
    (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) 𝓜 (μ := Q), hker φ, hV] with ω h1 h2 ⟨hV1, hV2⟩
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, rangeKerCF, rangeKerCF, ← Complex.exp_add, happ, hcov ω hV1 hV2]
  congr 1
  push_cast
  ring

/-- The chart transport of a distribution harmonic on the image of `O` is harmonic on `O`, for either sign. -/
theorem isHarmonicDistOn_chartTransport_pm {c : Chart} (hc : c.IsConformal) (hliftc : ContinuousOn c.2.2 c.dom)
    (hlift : InnerProductSpace.HarmonicOnNhd c.2.2 c.dom) {O : Set ℂ} (hOo : IsOpen O) (hO : O ⊆ H)
    {M : DistOn upperHalfPlaneOpens} (hM : IsHarmonicDistOn M (c.2.1 '' O)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (a k : ℝ) : IsHarmonicDistOn (Chart.chartTransport hc σ a k M) O := by
  rcases hσ with rfl | rfl
  · exact Sec7.Lemma72C.isHarmonicDistOn_chartTransport hc hliftc hlift hOo hO hM a k
  · have he : Chart.chartTransport hc (-1) a k M = Chart.chartTransport hc 1 a k (-M) := by
      ext ψ
      rw [Chart.chartTransport_apply', Chart.chartTransport_apply', neg_apply]
      ring
    have hIo : IsOpen (c.2.1 '' O) := hc.isOpen_image_of_subset hOo hO
    have hneg : IsHarmonicDistOn (-M) (c.2.1 '' O) := by
      have h0 : IsHarmonicDistOn (0 : DistOn upperHalfPlaneOpens) (c.2.1 '' O) :=
        ⟨0, InnerProductSpace.harmonicOnNhd_const (0 : ℝ), fun φ _ => by simp⟩
      have := LocalSets.IsHarmonicDistOn.sub' hIo h0 hM
      rwa [zero_sub] at this
    rw [he]
    exact Sec7.Lemma72C.isHarmonicDistOn_chartTransport hc hliftc hlift hOo hO hneg a k

end OneChart

end InteractingSLE.Theorem14.GW4Fix.CLoc
