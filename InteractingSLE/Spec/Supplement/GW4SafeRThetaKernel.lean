/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRThetaInversion
import InteractingSLE.Spec.Coupling.WFSLeafFreezeMean

/-! # GW4: identifying the transported union mean from its actual kernel -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart.MarkovChart WFS
open Sec6.Prop65 Sec7.FlatClockProof
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- A retained Gaussian kernel identifies every version of the local-set
mean as a whole distribution, on one probability-one event. -/
theorem ae_localSetMean_eq_of_retainedKernel {Ω : Type*}
    {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h M g : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h Q) {A : Ω → Set ℂ}
    (h𝓜 : 𝓜 ≤ mΩ) (hA : Measurable[𝓜, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hMm : Measurable[𝓜] M)
    (hloc : IsHistoryAvoidanceLocal 𝓜 A h Q)
    (hker : ∀ φ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜] =ᵐ[Q]
        fun ω => rangeKerCF (M ω) (H \ A ω) φ)
    (hg : IsLocalSetMean A h Q g) : g =ᵐ[Q] M := by
  have hAm : Measurable[mΩ, hittingSigma] A := hA.mono h𝓜 le_rfl
  have he := fun j : ℕ × ℕ =>
    (ae_localSetMean_eq_condExp_history hh hAm h𝓜 hloc
      (Eventually.of_forall hAc) hg (LQGMetric.distGen upperHalfPlaneOpens j)).trans
      (WFS.ae_condExp_germ_history_eq_of_retainedKernel hh h𝓜 hA hAc hMm hloc hker _)
  filter_upwards [ae_all_iff.2 he] with ω hω
  exact LQGMetric.injective_distOn_pairings upperHalfPlaneOpens (funext hω)

/-- The union kernel itself, after the component chart, source inversion
and subtraction of the prescribed background. The mean is explicit. -/
theorem ae_condExp_cexp_componentUnion {Ω : Type*}
    {𝓜 : MeasurableSpace Ω} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {R L C : Set ℂ} {c : Chart} (hch : IsComponentChart R L C c)
    (hCo : IsOpen C) (hCH : C ⊆ H) {κ : ℝ} (hκ : 0 < κ)
    {h hC M : Ω → DistOn upperHalfPlaneOpens}
    (htr : ∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hC ω))
    (u : ℂ → ℝ) {A : Ω → Set ℂ}
    (hAo : ∀ ω, IsOpen (H \ A ω))
    (hAC : ∀ᵐ ω ∂Q, IsOpen ((H \ A ω) \ C))
    (hker : ∀ φ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜] =ᵐ[Q]
        fun ω => rangeKerCF (M ω) (H \ A ω) φ) :
    let hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
    ∀ φ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I *
        (centredField (fun ω => GW4Rel.invField κ (hC ω)) u ω φ : ℂ)) | 𝓜] =ᵐ[Q]
      fun ω => rangeKerCF (GW4Rel.invField κ
        (Chart.chartTransport hc 1 0 (chiC κ) (M ω)) - smoothDist upperHalfPlaneOpens u)
          (H \ CLoc.chartSet c (A ω)) φ := by
  let hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
  have hLc : LocallyIntegrableOn (fun w => c.2.2 (c.2.1 w)) H :=
    Chart.locallyIntegrableOn_of_continuousOn
      (hch.2.2.2.2.2.1.comp hc.1.continuousOn hch.2.2.1)
  have hLI := Chart.locallyIntegrableOn_of_continuousOn
    CLoc.continuousOn_lift_inv_infinitySourceChart
  have hhC : hC = fun ω => Chart.chartTransport hc 1 0 (chiC κ) (h ω) :=
    funext fun ω => (htr ω).eq_chartTransport hc hLc
  have hInv : ∀ f : DistOn upperHalfPlaneOpens, GW4Rel.invField κ f =
      Chart.chartTransport Chart.isConformal_infinitySourceChart (-1)
        (-(Real.pi * chiC κ)) (chiC (16 / κ)) f :=
    fun f => (isChartTransport_invField hκ f).eq_chartTransport _ hLI
  let M₁ := fun ω => Chart.chartTransport hc 1 0 (chiC κ) (M ω)
  have hk₁ : ∀ ψ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (hC ω ψ : ℂ)) | 𝓜] =ᵐ[Q]
        fun ω => rangeKerCF (M₁ ω) (chartPre c (H \ A ω)) ψ := by
    intro ψ
    rw [hhC]
    refine CLoc.ae_condExp_cexp_chartTransport hc (Or.inl rfl) 0 (chiC κ) ?_ hker ψ
    filter_upwards [hAC] with ω hω
    exact ⟨hAo ω, (CLoc.coe_dom_of_isComponentChart hch hCo hCH).symm ▸ hω⟩
  have hk₂ : ∀ ψ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (GW4Rel.invField κ (hC ω) ψ : ℂ)) | 𝓜] =ᵐ[Q]
        fun ω => rangeKerCF (GW4Rel.invField κ (M₁ ω))
          (chartPre infinitySourceChart (chartPre c (H \ A ω))) ψ := by
    intro ψ
    simp_rw [hInv]
    refine CLoc.ae_condExp_cexp_chartTransport Chart.isConformal_infinitySourceChart
      (Or.inr rfl) (-(Real.pi * chiC κ)) (chiC (16 / κ)) ?_ hk₁ ψ
    exact Eventually.of_forall fun ω => ⟨isOpen_chartPre hc (hAo ω), by
      rw [Sec7.StripSysField.coe_dom_infinitySourceChart,
        Set.sdiff_eq_empty.2 (chartPre_subset_H _ _)]
      exact isOpen_empty⟩
  change ∀ ψ : TestOn upperHalfPlaneOpens, _
  intro ψ
  let S := smoothDist upperHalfPlaneOpens u
  have hsplit : (fun ω => Complex.exp (Complex.I *
      (centredField (fun ω => GW4Rel.invField κ (hC ω)) u ω ψ : ℂ))) =
      Complex.exp (-(Complex.I * (S ψ : ℂ))) •
        fun ω => Complex.exp (Complex.I * (GW4Rel.invField κ (hC ω) ψ : ℂ)) := by
    funext ω
    rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
    simp only [centredField, sub_apply, S]
    push_cast
    ring_nf
  rw [hsplit]
  filter_upwards [condExp_smul (Complex.exp (-(Complex.I * (S ψ : ℂ))))
    (fun ω => Complex.exp (Complex.I * (GW4Rel.invField κ (hC ω) ψ : ℂ))) 𝓜 (μ := Q),
    hk₂ ψ] with ω h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, CLoc.H_diff_chartSet,
    rangeKerCF, rangeKerCF, ← Complex.exp_add, sub_apply]
  congr 1
  push_cast
  ring

end InteractingSLE.Theorem14.GW4Fix
