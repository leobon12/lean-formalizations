/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaUnion
import InteractingSLE.Spec.Supplement.GW4SafeRThetaMean
import InteractingSLE.Spec.Supplement.GW4SafeRThetaCompare
import InteractingSLE.Spec.Supplement.GW4CLocWire

/-! # GW4: retain the original local-mean law in component transport -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField WalkLaw GW4Traverse GW4Rel Sec5.GlueCond Sec5.Cond44Ref
open Supp8.RelSafe CLoc Sec7.StripSysField
open Restart Restart.DomainMarkov.K2

/-- In the original GW4 coupling, every version of every selected live
component mean is the prescribed transport of the actual ambient union
mean. Theorems 1.2--1.3 supply the union kernels; there is no new
mean-transport hypothesis. The index family may be all rational times. -/
theorem exists_component_union_mean_transport_with_mean
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {ι : Type*} [Countable ι] (τ : ι → ℝ≥0)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b J P h spec (E spec))
    (hreg : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b J P spec (E spec)) :
    ∃ (u₀ : ℂ → ℝ) (A : ℝ≥0 → Ω → Set ℂ) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens),
      IsBoundedHarmonicExtension b J u₀ ∧
      (∀ t, IsLocalSetMean (A t) (centredField h u₀) P
        (fun ω => M t ω - smoothDist upperHalfPlaneOpens u₀)) ∧
      (∀ t ω, A t ω ⊆ H ∧ IsOpen (H \ A t ω)) ∧
      (∀ t, Measurable[mΩ, hittingSigma] (A t)) ∧
      (∀ t, ∀ᵐ ω ∂P, A t ω = relClosureH
        (walkUnionSet κ b J E ω ∪ cfHullQ t (cfHistory W ζ ω))) ∧
      (∀ t, ∀ᵐ ω ∂P, IsHarmonicDistOn (M t ω) (H \ A t ω)) ∧
      let wR := boundaryWalkSpec b J (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b J (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b J wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b J wL (fun k => E wL k ω₀)
        let ν := condExpKernel P (jointPast κ b J E) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → DistOn upperHalfPlaneOpens),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hC ω)) →
        ∀ c₀ : BoundaryWord,
          IsGFFWithBoundaryData ν (fun ω => invField κ (hC ω)) c₀.fn c₀.jumps →
        ∀ (F : Frame) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω),
          F.IsOk → F.C = C → F.c = c →
          (∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) →
        ∀ hWm : ∀ r, Measurable (Wd r), MeasurableSet GT → (∀ᵐ ω ∂ν, ω ∈ GT) →
          (∀ᵐ ω ∂ν, ∀ r, Wd r ω = W r ω) →
        ∀ (Rv : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞),
          IsGW4RelVersionR ν Wd F.c F.C Rv V →
        ∀ (u : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
          ComponentLineLocality c₀ F ν (fun ω => invField κ (hC ω)) Wd GT Rv V hWm u ℋ B →
        ∀ (p : ι) (g : Ω → DistOn upperHalfPlaneOpens),
          IsLocalSetMean (B (τ p)) (centredField (fun ω => invField κ (hC ω)) u) ν g →
          ∃ hc : F.c.IsConformal,
          ∀ᵐ ω ∂ν, lineClock F Wd GT V (τ p) ω < V ω →
            g ω = invField κ (Chart.chartTransport hc 1 0 (chiC κ) (M (τ p) ω)) -
              smoothDist upperHalfPlaneOpens u := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨A, M, 𝓜, -, hcf𝓜, hAm, hMm, hAc, hA, hMh, hOrigMean, hker⟩ :=
    exists_original_mean_condExpKernel_kernel_at h12p h13 τ hκ hκ4 hb hh hcf hζ hE hreg hu₀
  have hpR := GW1X.isBoundaryContinuedProgram_walkR b J
  have hpL := GW1X.isBoundaryContinuedProgram_walkL b J
  have hjm : jointPast κ b J E ≤ mΩ := sup_le ((hE _ hpR).2.1 _) ((hE _ hpL).2.1 _)
  have hRw := GW4Reg.ae_ae_physSet_eq (hreg _ hpR) hjm le_sup_left
  have hLw := GW4Reg.ae_ae_physSet_eq (hreg _ hpL) hjm le_sup_right
  have hAν := ae_all_iff.2 fun p : ι => KernelTower.ae_ae_condExpKernel_of_ae hjm (hA (τ p))
  have hMν := ae_all_iff.2 fun p : ι => KernelTower.ae_ae_condExpKernel_of_ae hjm (hMh (τ p))
  have hζν := KernelTower.ae_ae_condExpKernel_of_ae hjm hζ
  refine ⟨u₀, A, M, hu₀, hOrigMean, hAc, fun t => (hAm t).mono (𝓜 t).2 le_rfl, hA, hMh, ?_⟩
  intro wR wL
  filter_upwards [hker, hRw, hLw, hAν, hMν, hζν] with ω₀ hkω hRω hLω hAω hMω hζω
  intro R L ν C hCm c hC hch htr c₀ hX F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver
    u ℋ B hloc p g hg
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨ω₁, hω₁⟩ := hGTae.exists
  have hCo : IsOpen C := hFC ▸ Frame.isOpen_C hF (hGT ω₁ hω₁)
  have hS : ∀ᵐ ω ∂ν, walkUnionSet κ b J E ω = (R ∪ L) ∩ H := by
    filter_upwards [hRω, hLω] with ω h1 h2
    show WalkLaw.walkSet κ b J wR (E wR) ω ∪ WalkLaw.walkSet κ b J wL (E wL) ω = (R ∪ L) ∩ H
    simp only [WalkLaw.walkSet]
    rw [h1, h2]
    exact (union_inter_distrib_right _ _ _).symm
  subst C
  subst c
  have hZero := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hloc.1
  have hSafeL := isHistoryAvoidanceLocal_safeHull_of_kernel (𝓜 (τ p)).2 hCm hch hCo hκ
    hh.1 htr hloc.1.1 (hAm _) (hMm _) (hAc _) (hMω p) (hkω p) (hcf𝓜 _) (hAω p) hS
    hF rfl rfl hGT hWm hGTm hGTae hVW hζω hver
  have hSafeM := (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver (τ p)).mono
    ((physFilt Frame.measurable_gw4Rec hWm ν).le _) le_rfl
  have hSafeC : ∀ ω, safeHull F Wd GT Rv V (τ p) ω ⊆ H ∧
      IsOpen (H \ safeHull F Wd GT Rv V (τ p) ω) := fun ω =>
    ⟨safeHull_subset_H F Wd GT Rv V (τ p) ω,
    Frame.isOpen_H_diff_safeHull hver (τ p) ω⟩
  have hSafeLocal : IsLocalSet (safeHull F Wd GT Rv V (τ p))
      (centredField (fun ω => invField κ (hC ω)) u) ν :=
    ((isLocalSet_tfae hZero hSafeM (Eventually.of_forall hSafeC)).out 1 4).1 hSafeL.isAvoidanceLocal
  obtain ⟨gSafe, hgSafe⟩ := IsLocalSet.exists_isLocalSetMean hZero hSafeM hSafeLocal
  have hGiven := ae_component_mean_eq_safeHull hF hX hGT hGTm hGTae hver hloc (τ p) g gSafe hg hgSafe
  have hMean := ae_safeHull_mean_eq_componentUnion (𝓜 (τ p)).2 hF hCm hch hκ hCo
    hh.1 htr hloc.1.1 hZero (hAm _) (hMm _) (hAc _) (hMω p) (hkω p)
    (hcf𝓜 _) (hAω p) hS hGT hWm hGTm hGTae hVW hζω hver hgSafe
  refine ⟨GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo
    (CLoc.subset_H_of_mem_betweenComponents hF.2.1), ?_⟩
  filter_upwards [hGiven, hMean] with ω hGivenω hMeanω hLive
  exact (hGivenω hLive).trans (hMeanω hLive)

end InteractingSLE.Theorem14.GW4Fix
