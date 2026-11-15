/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRGermLine

/-!
# GW4: the actual initial reference law

The initial chart is the identity and its centred mean is zero. Its residual
is the actual initial zero-boundary GFF. Thus component locality directly
supplies this reference increment law, including off the live event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw LocalSets WholeField MartChar Sec7.PocketStopSide

/-- Pulling a distribution through the literal initial chart changes no test. -/
theorem pullField_initial_eq (hc : Chart.id.IsConformal)
    (T : DistOn upperHalfPlaneOpens) : Chart.pullField hc T = T := by
  ext φ
  rw [Chart.pullField_apply]
  congr 1
  ext z
  rw [Chart.coe_pushTest]
  have hdom : (Chart.id.dom : Set ℂ) = H := by
    rw [hc.coe_dom]
    exact image_id _
  rw [hdom]
  change H.indicator (fun w => ‖deriv (id : ℂ → ℂ) w‖ ^ 2 * φ w) z = φ z
  simp only [deriv_id, norm_one, one_pow, one_mul]
  by_cases hz : z ∈ H
  · exact indicator_of_mem hz _
  · rw [indicator_of_notMem hz]
    exact (image_eq_zero_of_notMem_tsupport
      (fun h => hz (Coupling.tsupport_subset_H φ h))).symm

/-- The literal random line chart has the actual relative hull complement
as domain, at every outcome and every physical line. -/
theorem componentLineChart_domain {Ω : Type*} {F : Frame}
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    {t : ℝ≥0} {ω : Ω} (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) :
    ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) =
      H \ fwdHull (wpath R ω) (lineClock F Wd GT V t ω).toNNReal := by
  have hW : Continuous (wpath R ω) := hRc.comp continuous_real_toNNReal
  have hW0 : wpath R ω 0 = 0 := by simpa only [wpath, Real.toNNReal_zero] using hR0
  rw [componentLineChart, dom_own_stage_as_initial_inverse_image
    Chart.isConformal_id hW hW0 (lineClock F Wd GT V t ω).toNNReal.coe_nonneg]
  exact image_id _

/-- Component locality proves the initial-chart increment law for every
version of the current mean. There is no reference-law hypothesis. -/
theorem component_initial_increment_law {Ω : Type*} [MeasurableSpace Ω]
    {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
    {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω))
    (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean (B t) (centredField X u₀) ν g) :
    HasOldChartIncrementLaw ν {ω | lineClock F Wd GT V t ω < V ω}
      (fun _ => Chart.id) (componentLineChart F Wd GT R V t) (fun _ => 0) g := by
  obtain ⟨hu₀, -, -, hBm, hBc, -, hShape⟩ := hloc
  refine ⟨B t, centredField X u₀, g,
    isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hu₀,
    hBm t, Eventually.of_forall (hBc t), hg, ?_⟩
  filter_upwards [hShape t] with ω hs hlt
  refine ⟨?_, fun hc => ?_⟩
  · simp only [oldChartAddedSet, mem_ofPred_eq, hlt, ↓reduceIte]
    have hD : ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) = H \ B t ω :=
      (componentLineChart_domain (hRc ω) (hR0 ω)).trans (hs hlt).symm
    change B t ω = H \ {z | z ∈ H ∧ z ∈ (componentLineChart F Wd GT R V t ω).dom}
    ext z
    have hsub := (hBc t ω).1
    have hDz : z ∈ (componentLineChart F Wd GT R V t ω).dom ↔ z ∈ H \ B t ω :=
      Set.ext_iff.mp hD z
    simp only [Set.mem_sdiff, mem_ofPred_eq]
    rw [hDz]
    simp only [Set.mem_sdiff]
    constructor
    · intro hz
      exact ⟨hsub hz, fun h => h.2.2 hz⟩
    · rintro ⟨hzH, hz⟩
      by_contra hzB
      exact hz ⟨hzH, hzH, hzB⟩
  · rw [sub_zero, pullField_initial_eq hc]

/-- Locality constructs an actual current mean together with its initial
reference law at every physical line. -/
theorem exists_component_initial_reference {Ω : Type*} [MeasurableSpace Ω]
    {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
    {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω)) (t : ℝ≥0) :
    ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (B t) (centredField X u₀) ν g ∧
      HasOldChartIncrementLaw ν {ω | lineClock F Wd GT V t ω < V ω}
        (fun _ => Chart.id) (componentLineChart F Wd GT R V t) (fun _ => 0) g := by
  have hLaw := component_initial_increment_law hX hloc hR0 hRc t
  obtain ⟨hu₀, -, -, hBm, hBc, hBloc, -⟩ := hloc
  have hZero := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hu₀
  obtain ⟨g, hg⟩ := (isGermConditionalLaw_iff (A := B t)
    (h := centredField X u₀) (P := ν)).1
      ((hBloc t).isAvoidanceLocal.isGermConditionalLaw hZero (hBm t)
        (Eventually.of_forall (hBc t)))
  exact ⟨g, hg, hLaw g hg⟩

end InteractingSLE.Theorem14.GW4Fix
