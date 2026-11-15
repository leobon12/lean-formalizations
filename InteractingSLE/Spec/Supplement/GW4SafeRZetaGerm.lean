/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaLaw

/-!
# GW4: zero mean increments at the actual earlier-reference collars

Instantiate the conditioned reference-law consumer with the canonical
harmonic representatives. This is simultaneous in all incident real
accesses and all certified half-discs at the two physical lines.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Supp8.RelSafe LocalSets WholeField Restart Sec7.R5Enl Sec7.PocketStopSide
  Sec7.Aux119Heights

/-- Every actual old reference collar has zero local-set-mean increment,
without an assumed reference law or an assumed boundary mean. -/
theorem ae_component_reference_zero_germ {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
    {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hF : F.IsOk) (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    {s t : ℝ≥0} (hst : s ≤ t)
    (gOld gNow : Ω → DistOn upperHalfPlaneOpens)
    (hgOld : IsLocalSetMean (safeHull F Wd GT R V s) (centredField X u₀) ν gOld)
    (hgNow : IsLocalSetMean (safeHull F Wd GT R V t) (centredField X u₀) ν gNow) :
    ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω → ∀ ξ x r : ℝ, 0 < r →
      (componentLineChart F Wd GT R V s ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
        ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) →
      Tendsto (fun z => (componentLineChart F Wd GT R V s ω).1
          ((componentLineChart F Wd GT R V t ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun z => harmRep (gNow ω) (H \ safeHull F Wd GT R V t ω)
            ((componentLineChart F Wd GT R V t ω).2.1 z) -
          harmRep (gOld ω) (H \ safeHull F Wd GT R V s ω)
            ((componentLineChart F Wd GT R V t ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have hC : ∀ u ω, (componentLineChart F Wd GT R V u ω).IsConformal := by
    intro u ω
    have hW : Continuous (MartChar.wpath R ω) := (hver.1.1.2.1 ω).comp continuous_real_toNNReal
    have hW0 : MartChar.wpath R ω 0 = 0 := by
      simpa only [MartChar.wpath, Real.toNNReal_zero] using hver.1.1.2.2.1 ω
    exact Chart.isConformal_id.loewner hW hW0
      (lineClock F Wd GT V u ω).toNNReal.coe_nonneg
  have hD : ∀ u ω, lineClock F Wd GT V u ω < V ω →
      ((componentLineChart F Wd GT R V u ω).dom : Set ℂ) = H \ safeHull F Wd GT R V u ω :=
    fun u ω hω => (componentLineChart_domain (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)).trans
      (H_diff_safeHull_of_lt F Wd GT R V u ω hω).symm
  have hLive : ∀ ω, lineClock F Wd GT V t ω < V ω → lineClock F Wd GT V s ω < V ω :=
    fun ω hω => (Frame.monotone_min_physClockG hF hGT (V := V) ω hst).trans_lt hω
  have hSub : ∀ ω ∈ {ω | lineClock F Wd GT V t ω < V ω},
      ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) ⊆
        (componentLineChart F Wd GT R V s ω).dom := by
    intro ω hω
    rw [hD t ω hω, hD s ω (hLive ω hω)]
    exact fun z hz => ⟨hz.1, fun hs => hz.2 (safeHull_mono hF hGT ω hst hs)⟩
  have hGerm := ae_physical_germ_of_old_chart_increment_law_on
    (fun ω _ => hC s ω) (fun ω _ => hC t ω) hSub
    (component_reference_increment_law hF hX hGT hGTm hGTae hver hloc hst gOld gNow hgOld hgNow)
  filter_upwards [hGerm, hgOld.2.1, hgNow.2.1] with ω hGermω hOldω hNowω hω
  obtain ⟨hvOld, hrepOld⟩ := harmRep_spec hOldω
  obtain ⟨hvNow, hrepNow⟩ := harmRep_spec hNowω
  have hDs := hD s ω (hLive ω hω)
  have hDt := hD t ω hω
  apply hGermω hω _ _
  · rwa [hDs]
  · intro φ hφ
    exact hrepOld φ (by rwa [← hDs])
  · rwa [hDt]
  · intro φ hφ
    exact hrepNow φ (by rwa [← hDt])

end InteractingSLE.Theorem14.GW4Fix
