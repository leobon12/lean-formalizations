/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeREtaVersions

/-! # GW4: reference laws for every given local-set-mean version

The canonical conditioned law and zero germ transfer to the original B
means by the proved live-event equality of distributions. No reference
kernel, mean version or mean-comparison premise is added.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart Sec7.PocketStopSide Sec7.Aux119Heights Sec7.R5Enl

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω} [IsProbabilityMeasure ν]
  {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
  {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
  {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
  (hF : F.IsOk) (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
  (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω))
  (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
  (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
  (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)

include hF hX hGT hGTm hGTae hver hloc

/-- The conditioned reference increment law holds for arbitrary versions
of the means of the given B sets. -/
theorem component_reference_increment_law_of_mean {s t : ℝ≥0} (hst : s ≤ t)
    (gOld gNow : Ω → DistOn upperHalfPlaneOpens)
    (hgOld : IsLocalSetMean (B s) (centredField X u₀) ν gOld)
    (hgNow : IsLocalSetMean (B t) (centredField X u₀) ν gNow) :
    HasOldChartIncrementLawOn ν {ω | lineClock F Wd GT V t ω < V ω}
      (componentLineChart F Wd GT R V s) (componentLineChart F Wd GT R V t) gOld gNow := by
  have hZero := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hloc.1
  have hExists : ∀ u : ℝ≥0, ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (safeHull F Wd GT R V u) (centredField X u₀) ν g := by
    intro u
    have hAm := (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver u).mono
      ((Supp8.RelSafe.physFilt Frame.measurable_gw4Rec hWm ν).le _) le_rfl
    exact (isGermConditionalLaw_iff (A := safeHull F Wd GT R V u)
      (h := centredField X u₀) (P := ν)).1
      ((component_safeHull_locality hF hGT hGTm hGTae hver hloc u).isAvoidanceLocal.isGermConditionalLaw
        hZero hAm (Eventually.of_forall fun ω =>
          ⟨safeHull_subset_H F Wd GT R V u ω, Frame.isOpen_H_diff_safeHull hver u ω⟩))
  obtain ⟨a, ha⟩ := hExists s
  obtain ⟨b, hb⟩ := hExists t
  have hLaw := component_reference_increment_law hF hX hGT hGTm hGTae hver hloc hst a b ha hb
  have hOld := ae_component_mean_eq_safeHull hF hX hGT hGTm hGTae hver hloc s gOld a hgOld ha
  have hNow := ae_component_mean_eq_safeHull hF hX hGT hGTm hGTae hver hloc t gNow b hgNow hb
  apply hLaw.congr_on
  filter_upwards [hOld, hNow] with ω hOldω hNowω hLive
  have hLiveOld := (Frame.monotone_min_physClockG hF hGT (V := V) ω hst).trans_lt hLive
  exact ⟨rfl, rfl, (hOldω hLiveOld).symm, (hNowω hLive).symm⟩

/-- Every certified incident collar has zero mean increment for the given
B means, simultaneously in all its coordinates and radii. -/
theorem ae_component_reference_zero_germ_of_mean {s t : ℝ≥0} (hst : s ≤ t)
    (gOld gNow : Ω → DistOn upperHalfPlaneOpens)
    (hgOld : IsLocalSetMean (B s) (centredField X u₀) ν gOld)
    (hgNow : IsLocalSetMean (B t) (centredField X u₀) ν gNow) :
    ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω → ∀ ξ x r : ℝ, 0 < r →
      (componentLineChart F Wd GT R V s ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
        ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) →
      Tendsto (fun z => (componentLineChart F Wd GT R V s ω).1
          ((componentLineChart F Wd GT R V t ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun z => harmRep (gNow ω) (H \ B t ω)
            ((componentLineChart F Wd GT R V t ω).2.1 z) -
          harmRep (gOld ω) (H \ B s ω)
            ((componentLineChart F Wd GT R V t ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have hC : ∀ u ω, (componentLineChart F Wd GT R V u ω).IsConformal := by
    intro u ω
    have hW : Continuous (MartChar.wpath R ω) := (hver.1.1.2.1 ω).comp continuous_real_toNNReal
    have hW0 : MartChar.wpath R ω 0 = 0 := by
      simpa only [MartChar.wpath, Real.toNNReal_zero] using hver.1.1.2.2.1 ω
    exact Chart.isConformal_id.loewner hW hW0 (lineClock F Wd GT V u ω).toNNReal.coe_nonneg
  have hLive : ∀ ω, lineClock F Wd GT V t ω < V ω → lineClock F Wd GT V s ω < V ω :=
    fun ω hω => (Frame.monotone_min_physClockG hF hGT (V := V) ω hst).trans_lt hω
  have hD : ∀ u ω, lineClock F Wd GT V u ω < V ω →
      ((componentLineChart F Wd GT R V u ω).dom : Set ℂ) = H \ safeHull F Wd GT R V u ω :=
    fun u ω hω => (componentLineChart_domain (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)).trans
      (H_diff_safeHull_of_lt F Wd GT R V u ω hω).symm
  have hSub : ∀ ω ∈ {ω | lineClock F Wd GT V t ω < V ω},
      ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) ⊆
        (componentLineChart F Wd GT R V s ω).dom := by
    intro ω hω
    rw [hD t ω hω, hD s ω (hLive ω hω)]
    exact fun z hz => ⟨hz.1, fun hs => hz.2 (safeHull_mono hF hGT ω hst hs)⟩
  have hGerm := ae_physical_germ_of_old_chart_increment_law_on
    (fun ω _ => hC s ω) (fun ω _ => hC t ω) hSub
    (component_reference_increment_law_of_mean hF hX hGT hGTm hGTae hver hloc hst
      gOld gNow hgOld hgNow)
  filter_upwards [hGerm, hgOld.2.1, hgNow.2.1, hloc.2.2.2.2.2.2 s, hloc.2.2.2.2.2.2 t]
    with ω hGermω hOldω hNowω hShapeS hShapeT hω
  obtain ⟨hvOld, hrepOld⟩ := harmRep_spec hOldω
  obtain ⟨hvNow, hrepNow⟩ := harmRep_spec hNowω
  have hDs := (componentLineChart_domain (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)).trans
    (hShapeS (hLive ω hω)).symm
  have hDt := (componentLineChart_domain (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)).trans
    (hShapeT hω).symm
  apply hGermω hω _ _
  · rwa [hDs]
  · intro φ hφ
    exact hrepOld φ (by rwa [← hDs])
  · rwa [hDt]
  · intro φ hφ
    exact hrepNow φ (by rwa [← hDt])

end InteractingSLE.Theorem14.GW4Fix
