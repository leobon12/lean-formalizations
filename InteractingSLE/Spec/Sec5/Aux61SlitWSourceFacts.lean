/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceGeometry
import InteractingSLE.Spec.Sec5.Aux61GRecBoundary

/-! # The MARKS facts of the concrete physical source data -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61Asm Aux61FibData Aux61GInst Aux61ChLoc Aux61ULoc LawUnique GlueCond
open WangWu Cond44Ref CfRegQ CrossCond.Theta Coupling WholeField LocalSets
universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}
  {κ θ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {Bm : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {η : Ω → ℝ≥0 → ℂ} {Ω₂ : Type u} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k]
  {μ : Measure (Ω × HistorySpace 0 0)} [IsProbabilityMeasure μ]

/-- Assemble the facts of the explicit source construction. The two MARKS
measurability inputs and the physical restart/initial-data inputs remain
named. Locality and nesting are proved from the actual coupling. -/
theorem source_marksFacts
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR Bm ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hθ : CfThetaBounds κ θ ρL ρR xL xR)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hμ : μ = glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))
    (F : SourceRestartData Ω nL nR) (s : ℝ≥0)
    (hR : SourceRestartFacts F s W VL VR ζ (μ := μ) κ) :
    let D := sourceMarksData F s W VL VR ζ κ h ρL ρR xL xR η μ
    (∀ i q, (Aux61FibK.codeFiltration.{u} q).comap (fun p => ULift.up.{u} (D.code i p)) ≤ D.baseMarks i q) →
    (∀ i q, Measurable[D.baseMarks i q, hittingSigma] (D.baseSets i q)) →
    (∀ i q, ∀ᵐ p ∂μ, unionAt (fun p => cfHullQ s p.2)
      (fun t p => Sec7.PocketStopWallsFin.regHull W ζ t p.1)
      (fun p => capacityRule (F.chart i) (F.start i) q
        (stopRec s p.2, killedHistory W VL VR ζ p.1)) p ⊆ D.baseSets i q p) →
    (∀ i (q : ℝ≥0), 0 < q → ∀ᵐ p ∂μ, D.Z i p ∈ D.B i → (q : ℝ≥0∞) < (D.code i p).life →
      GluedSlitFacts (D.data i).κ (D.code i p) q (D.physicalDriver i q p) (D.physicalPath i q p)
        (D.start i q p) (D.duration i q p) (D.chart i p) (D.domain i q p) (D.chartPath i q p) (D.chartLife i q p)
        (fun j => D.time j i q p) (fun j => D.patches j i q p) (D.baseSets i q p)
        (fun j => D.mean j i q p) (fun j => D.physicalMean j i q p)) →
    (∀ i (q : ℝ≥0), 0 < q → ∀ᵐ p ∂μ, D.Z i p ∈ D.B i → (q : ℝ≥0∞) < (D.code i p).life →
      ∀ j, D.time j i q p < D.start i q p + D.duration i q p → p ∈ D.comparisonEvent j i q) →
    (∀ i, ∃ g : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0 (D.sigma i 0) g ∧
        Nonempty (Aux61GCont.InitialWindowData (Ω × HistorySpace 0 0)
          (μ.restrict (D.Z i ⁻¹' D.B i)) (D.data i) g)) →
    MarksFacts μ D := by
  intro D hcode hsets hcontains hglued hcomparison hinitial
  have hX := hC.2.2.2.1
  have hZ : ∀ i, Measurable (D.Z i) := fun i =>
    measurable_up.comp (measurable_sourceRecord F s W VL VR ζ hX i)
  have hB : ∀ i, MeasurableSet (D.B i) := fun i => measurable_down (hR.selected_measurable i)
  have hbase : ∀ i q, D.baseMarks i q ≤ (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) :=
    fun _ _ => nullMarks_le
  have hmono : ∀ i q, D.baseMarks i 0 ≤ D.baseMarks i q := by
    intro i q
    apply nullMarks_mono
    have he : capacityRule (F.chart i) (F.start i) 0 = fun _ => (F.start i : ℝ≥0∞) :=
      funext (capacityRule_zero _ _)
    change ruleMarks stopRec (capacityRule (F.chart i) (F.start i) 0) _ _ ≤ _
    rw [he]
    exact initial_ruleMarks_le (F.chart i) (F.start i) q _ _
  have hloc : ∀ i q, IsHistoryAvoidanceLocal (D.baseMarks i q) (D.baseSets i q) D.cfield μ := by
    intro i q
    have hraw := isHistoryAvoidanceLocal_unionAt_rule_cfGlueT hC hκ hζ hθ hcf hlaw hk
      (Impl.isBoundedHarmonicExtension_forceExt κ (Ito.weightWord ρL ρR) xL xR) s
      (measurable_capacityRule (hR.chart_measurable i) (F.start i) q)
      (isGalmarinoRule_capacityRule (F.chart i) (F.start i) q)
    rw [← hμ] at hraw
    exact Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set hraw.nullMarks (hsets i q) (hcontains i q)
  refine {
    measurable_Z := hZ
    measurable_B := hB
    spec := hR.spec
    open_window := hR.open_window
    zero_window := hR.zero_window
    landing := hR.landing
    injective_path := hR.injective_path
    continuous_lift := hR.continuous_lift
    harmonic_lift := hR.harmonic_lift
    measurable_field := hC.2.1.comp measurable_fst
    data_window := fun _ => rfl
    data_clearance := hR.clearance
    reference := hR.reference
    physical_stop := hR.physical_stop
    harmonic_originalMean :=
      (Impl.isBoundedHarmonicExtension_forceExt κ (Ito.weightWord ρL ρR) xL xR).1
    zero_field := ?_
    baseMarks_le := hbase
    baseMarks_mono := hmono
    Z_le := fun i => (sourceHistory_marks F s W VL VR ζ hR hX i 0).comap_le
    code_le := hcode
    event_measurable := fun i => sourceEvent_marks F s W VL VR ζ hR i 0
    chart_measurable := fun i => sourceChart_marks F s W VL VR ζ hR hX i 0
    baseSets_marks := hsets
    baseSets_closed := sourceSets_closed F s W VL VR ζ κ h hR.spec
    baseSets_mono := sourceSets_mono F s W VL VR ζ κ h
    locality := hloc
    geometry := fun i q => Eventually.of_forall fun p hp hq =>
      sourceSets_geometry F s W VL VR ζ κ h hR.spec i q p ⟨hp, hq⟩
    initial_boundary := ?_
    glued := hglued
    comparison_cover := hcomparison }
  · change LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : Ω × HistorySpace 0 0 =>
        centredField h (Impl.forceExt κ (Ito.weightWord ρL ρR) xL xR) p.1) μ
    rw [hμ]
    exact isZeroBoundaryGFF_glued hC
      (Impl.isBoundedHarmonicExtension_forceExt κ (Ito.weightWord ρL ρR) xL xR) k
      ((measurable_cfFieldT κ θ).comp hC.2.1)
  · intro i
    obtain ⟨g, hg, ⟨Di⟩⟩ := hinitial i
    exact Aux61GRec.initial_boundary_of_gauss_initialData D i (hB i) hg Di

end InteractingSLE.Sec5.Aux61SlitW
