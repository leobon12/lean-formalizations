/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2XkKer

/-!
# A union's kernel, harmonic mean and locality through a launch chart (any measure)

Packet PROVE-GW2-GEOM2, round 14 (D49), for the base of Claim(k) at a root `x`. The chart-transport half of round 11's
`GW2Xk.ae_launch_kernelX`, for any conformal chart `cL` and any probability measure `Q`: a kernel identity of a set
family `B` for the field `h` transports to the launch image `cL.1 '' (B ∩ cL.dom)` for the transported field, centred
by any harmonic `u'`, together with the harmonicity of the transported mean and the locality of the image.

* **`launch_kernel_of`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW2Kx

open GW2Omx LocalSets WholeField GW2TipSystem GW2Sdi GW4Fix GW4Fix.CLoc GW2Rd GW2Xk Restart.MarkovChart

/-- **A union's kernel through a launch chart.** -/
theorem launch_kernel_of {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {κ : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {cL : Chart} (hconf : cL.IsConformal)
    (hliftc : ContinuousOn cL.2.2 cL.dom) (hlift : InnerProductSpace.HarmonicOnNhd cL.2.2 cL.dom)
    (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}) {B : Ω → Set ℂ} (hB𝓜 : Measurable[𝓜.1, hittingSigma] B)
    (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω)) (hV : ∀ᵐ ω ∂Q, IsOpen ((H \ B ω) \ cL.dom))
    {M : Ω → DistOn upperHalfPlaneOpens} (hMh : ∀ᵐ ω ∂Q, IsHarmonicDistOn (M ω) (H \ B ω))
    (hk₀ : ∀ φ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜.1] =ᵐ[Q] fun ω => rangeKerCF (M ω) (H \ B ω) φ)
    {u' : ℂ → ℝ} (hu' : InnerProductSpace.HarmonicOnNhd u' H) :
    (∀ᵐ ω ∂Q, IsHarmonicDistOn (Chart.chartTransport hconf 1 0 (chiC κ) (M ω) - smoothDist upperHalfPlaneOpens u')
      (H \ cL.1 '' (B ω ∩ (cL.dom : Set ℂ)))) ∧
    (∀ ψ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (centredField
          (fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω)) u' ω ψ : ℂ)) | 𝓜.1]
        =ᵐ[Q] fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC κ) (M ω) - smoothDist upperHalfPlaneOpens u')
          (H \ cL.1 '' (B ω ∩ (cL.dom : Set ℂ))) ψ) ∧
    IsHistoryAvoidanceLocal 𝓜.1 (fun ω => cL.1 '' (B ω ∩ (cL.dom : Set ℂ)))
      (centredField (fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω)) u') Q := by
  have hV' : ∀ᵐ ω ∂Q, IsOpen (H \ B ω) ∧ IsOpen ((H \ B ω) \ cL.dom) :=
    hV.mono fun ω h => ⟨(hBc ω).2, h⟩
  have hk₁ : ∀ ψ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (Chart.chartTransport hconf 1 0 (chiC κ) (h ω) ψ : ℂ)) | 𝓜.1]
        =ᵐ[Q] fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC κ) (M ω))
          (chartPre cL (H \ B ω)) ψ :=
    fun ψ => ae_condExp_cexp_chartTransport (𝓜 := 𝓜.1) (Q := Q) hconf (Or.inl rfl) 0 (chiC κ) hV' hk₀ ψ
  set S : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens u' with hSdef
  have hU : (fun ω => cL.1 '' (B ω ∩ (cL.dom : Set ℂ))) = fun ω => H \ chartPre cL (H \ B ω) := by
    funext ω
    exact launchUnion_eq hconf _
  have hk₃ : ∀ ψ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (centredField
          (fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω)) u' ω ψ : ℂ)) | 𝓜.1] =ᵐ[Q]
        fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC κ) (M ω) - S)
          (H \ (H \ chartPre cL (H \ B ω))) ψ := by
    intro ψ
    have hsplit : (fun ω => Complex.exp (Complex.I * (centredField
        (fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω)) u' ω ψ : ℂ))) =
        Complex.exp (-(Complex.I * (S ψ : ℂ))) •
          fun ω => Complex.exp (Complex.I * (Chart.chartTransport hconf 1 0 (chiC κ) (h ω) ψ : ℂ)) := by
      funext ω
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
      simp only [centredField, sub_apply, hSdef]
      push_cast
      ring_nf
    rw [hsplit]
    filter_upwards [condExp_smul (Complex.exp (-(Complex.I * (S ψ : ℂ))))
      (fun ω => Complex.exp (Complex.I * (Chart.chartTransport hconf 1 0 (chiC κ) (h ω) ψ : ℂ))) 𝓜.1
      (μ := Q), hk₁ ψ] with ω h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, sdiff_sdiff_cancel_left (chartPre_subset_H _ _), rangeKerCF,
      rangeKerCF, ← Complex.exp_add, sub_apply]
    congr 1
    push_cast
    ring
  have hM₂h : ∀ᵐ ω ∂Q, IsHarmonicDistOn (Chart.chartTransport hconf 1 0 (chiC κ) (M ω) - S)
      (H \ (H \ chartPre cL (H \ B ω))) := by
    filter_upwards [hMh] with ω hω
    rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
    have hVo : IsOpen (H \ B ω) := (hBc ω).2
    have hM1 : IsHarmonicDistOn (Chart.chartTransport hconf 1 0 (chiC κ) (M ω)) (chartPre cL (H \ B ω)) := by
      refine isHarmonicDistOn_chartTransport_pm hconf hliftc hlift (isOpen_chartPre hconf hVo)
        (chartPre_subset_H _ _) ?_ (Or.inl rfl) 0 (chiC κ)
      rw [image_chartPre hconf]
      exact IsHarmonicDistOn.mono hω inter_subset_left
    exact LocalSets.IsHarmonicDistOn.sub' (isOpen_chartPre hconf hVo) hM1
      (IsHarmonicDistOn.mono (isHarmonicDistOn_smoothDist hu') (chartPre_subset_H _ _))
  have hXm : Measurable fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω) :=
    (Chart.measurable_chartTransport hconf _ _ _).comp hhm
  have hloc' := WFS.isHistoryAvoidanceLocal_of_retainedKernel 𝓜.2 (measurable_centredField hXm u')
    (measurable_launch hconf hB𝓜)
    (Eventually.of_forall fun ω => ⟨sdiff_subset, by
      rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
      exact isOpen_chartPre hconf (hBc ω).2⟩) hM₂h hk₃
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hM₂h] with ω hω
    rw [launchUnion_eq hconf (B ω)]
    exact hω
  · intro ψ
    refine (hk₃ ψ).trans (Eventually.of_forall fun ω => ?_)
    show rangeKerCF _ (H \ (H \ chartPre cL (H \ B ω))) ψ = rangeKerCF _ (H \ cL.1 '' (B ω ∩ (cL.dom : Set ℂ))) ψ
    rw [launchUnion_eq hconf (B ω)]
  · rw [hU]
    exact hloc'

end InteractingSLE.Theorem14.GW2Kx
