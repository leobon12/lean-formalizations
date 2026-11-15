/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRThetaKernel
import InteractingSLE.Spec.Supplement.GW4SafeRThetaSet
import InteractingSLE.Spec.Supplement.GW4SafeRThetaVersions

/-! # GW4: the actual union kernel determines every live safe-hull mean -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart CLoc GW4Rel Sec5.GlueCond Sec5.Cond44Ref Supp8.RelSafe
open Restart.MarkovChart
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- The actual conditioned union kernel gives the transported mean of
the safe hull on its live event. This identifies arbitrary versions,
rather than selecting a special version and assuming its formula. -/
theorem ae_safeHull_mean_eq_componentUnion {Ω : Type*}
    {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] (h𝓜 : 𝓜 ≤ mΩ)
    {F : Frame} (hF : F.IsOk) {R L : Set ℂ} (hCm : F.C ∈ betweenComponents R L)
    (hch : IsComponentChart R L F.C F.c)
    {κ : ℝ} (hκ : 0 < κ)
    (hCo : IsOpen F.C) {h hC : Ω → DistOn upperHalfPlaneOpens}
    (hhm : Measurable h)
    (htr : ∀ ω, IsChartTransport F.c 1 0 (chiC κ) (h ω) (hC ω))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hX : IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField (fun ω => invField κ (hC ω)) u) Q)
    {A : Ω → Set ℂ} {M : Ω → DistOn upperHalfPlaneOpens}
    (hAm : Measurable[𝓜, hittingSigma] A) (hMm : Measurable[𝓜] M)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hMh : ∀ᵐ ω ∂Q, IsHarmonicDistOn (M ω) (H \ A ω))
    (hker : ∀ φ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜] =ᵐ[Q]
        fun ω => rangeKerCF (M ω) (H \ A ω) φ)
    {S : Ω → Set ℂ} {W Wd Rv : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {t : ℝ≥0}
    (hcf𝓜 : MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t) ≤ 𝓜)
    (hA : ∀ᵐ ω ∂Q, A ω = relClosureH (S ω ∪ cfHullQ t (cfHistory W ζ ω)))
    (hS : ∀ᵐ ω ∂Q, S ω = (R ∪ L) ∩ H)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂Q, ω ∈ GT)
    (hVW : ∀ᵐ ω ∂Q, ∀ r, Wd r ω = W r ω) (hζ : ∀ᵐ ω ∂Q, ζ ω = ⊤)
    (hver : IsGW4RelVersionR Q Wd F.c F.C Rv V)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (safeHull F Wd GT Rv V t)
      (centredField (fun ω => invField κ (hC ω)) u) Q g) :
    let hc := GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo
      (CLoc.subset_H_of_mem_betweenComponents hF.2.1)
    ∀ᵐ ω ∂Q, lineClock F Wd GT V t ω < V ω →
      g ω = invField κ (Chart.chartTransport hc 1 0 (chiC κ) (M ω)) -
        smoothDist upperHalfPlaneOpens u := by
  have hCH := CLoc.subset_H_of_mem_betweenComponents hF.2.1
  let hc := GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH
  let X := centredField (fun ω => invField κ (hC ω)) u
  let A' := fun ω => chartSet F.c (A ω)
  let T := fun ω => invField κ (Chart.chartTransport hc 1 0 (chiC κ) (M ω)) -
    smoothDist upperHalfPlaneOpens u
  have hAC : ∀ᵐ ω ∂Q, IsOpen ((H \ A ω) \ F.C) := by
    filter_upwards [hA, hS] with ω hAω hSω
    refine isOpen_diff_of_mem_betweenComponents hCm hCo ?_ (hAc ω).2
    intro z hz
    rw [hAω]
    refine ⟨hz.2, subset_closure ⟨Or.inl ?_, hz.2⟩⟩
    rwa [hSω]
  have hAl := isHistoryAvoidanceLocal_chartSet h𝓜 hF.2.2.2.1 hCo hCH hκ
    hhm htr hu hAm hMm hAc hMh hAC hker
  have hA'm := (measurable_chartSet hc hAm).mono h𝓜 le_rfl
  have hA'c : ∀ ω, A' ω ⊆ H ∧ IsOpen (H \ A' ω) := fun ω =>
    ⟨chartSet_subset_H _ _, by
      rw [H_diff_chartSet]
      exact isOpen_chartPre Chart.isConformal_infinitySourceChart
        (isOpen_chartPre hc (hAc ω).2)⟩
  have hA'loc : IsLocalSet A' X Q :=
    ((isLocalSet_tfae hX hA'm (Eventually.of_forall hA'c)).out 1 4).1 hAl.isAvoidanceLocal
  obtain ⟨gA, hgA⟩ := IsLocalSet.exists_isLocalSetMean hX hA'm hA'loc
  have hTm : Measurable[𝓜] T :=
    (measurable_sub_dist _).comp ((measurable_invField κ).comp
      ((Chart.measurable_chartTransport hc _ _ _).comp hMm))
  have hT := ae_localSetMean_eq_of_retainedKernel hX h𝓜 (measurable_chartSet hc hAm)
    hA'c hTm hAl (ae_condExp_cexp_componentUnion hF.2.2.2.1 hCo hCH hκ htr u
      (fun ω => (hAc ω).2) hAC hker) hgA
  have hGood : ∀ᵐ ω ∂Q, ζ ω = ⊤ ∧ Continuous (fun r => W r ω) ∧ ∀ r, Wd r ω = W r ω := by
    filter_upwards [hζ, hVW, hGTae] with ω hζω hVWω hω
    refine ⟨hζω, ?_, hVWω⟩
    simpa only [← hVWω] using (hGT ω hω).1
  have hMarks := physFilt_le_aeSigma hWm hcf𝓜 hGood
  have hAlP := RetAux79.isHistoryAvoidanceLocal_of_le_aeSigma hMarks hAl
  have hSC : ∀ᵐ ω ∂Q, Disjoint (S ω) F.C := hS.mono fun ω hω => by
    rw [hω]
    exact (disjoint_of_mem_betweenComponents hCm).mono_left inter_subset_left
  have hBl := isHistoryAvoidanceLocal_safeHull_of_kernel h𝓜 hCm hch hCo hκ
    hhm htr hu hAm hMm hAc hMh hker hcf𝓜 hA hS hF rfl rfl hGT hWm hGTm hGTae hVW hζ hver
  have hEq := ae_localSetMean_eq_on ((physFilt Frame.measurable_gw4Rec hWm Q).le t)
    (nullSets_le_physFilt Frame.measurable_gw4Rec hWm Q t) hX hA'm
    ((Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver t).mono
      ((physFilt Frame.measurable_gw4Rec hWm Q).le t) le_rfl)
    hA'c (fun ω => ⟨safeHull_subset_H F Wd GT Rv V t ω,
      Frame.isOpen_H_diff_safeHull hver t ω⟩) hAlP hBl
    (measurableSet_componentLine_live hF hGT hWm hGTm hGTae hver t)
    (ae_chartSet_eq_safeHull hF hGT hGTae hVW hζ hver t hA hSC) hgA hg
  filter_upwards [hT, hEq] with ω hTω hEqω hLive
  exact (hEqω hLive).symm.trans hTω

end InteractingSLE.Theorem14.GW4Fix
