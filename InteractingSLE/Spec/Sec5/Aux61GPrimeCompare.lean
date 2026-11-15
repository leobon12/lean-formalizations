/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GAlignContain
import InteractingSLE.Spec.Sec5.Aux61GPrimeInitial

/-! # Physical component comparisons for the source initial mean

This interface records smaller local sets, larger marked comparison unions,
and their accessible boundary germs. Only the component reached by the
inverse chart has to avoid the additional set; other accesses at the
same physical boundary point may meet it. It contains no initial Gaussian law,
initial boundary assertion, or identity for the unknown initial mean.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GPrime
open Aux61SlitW Aux61SlitW.SourceSetting Aux61Marks Aux61ChLoc Aux61FibData
open Aux61ULoc Aux61GInst LawUnique GlueCond LocalSets WholeField Aux61GAlign
open InteractingSLE.Theorem14.SB.FinRel
universe u

/-- The remaining physical comparison mathematics at zero capacity. In
particular `cover` concerns the known smaller physical means, not the
unknown Gaussian mean whose boundary values will be proved. -/
structure ZeroComparisons {X : Type u} [mX : MeasurableSpace X] {μ : Measure X}
    (D : MarksData μ) (i : D.ι) where
  index : Type
  [countable : Countable index]
  patch : index → X → Set ℂ
  patchMean : index → X → DistOn upperHalfPlaneOpens
  physicalMean : index → X → ℂ → ℝ
  union : index → X → Set ℂ
  unionMarks : index → MeasurableSpace X
  event : index → Set X
  patch_measurable : ∀ j, Measurable[mX, hittingSigma] (patch j)
  patch_closed : ∀ j, ∀ᵐ x ∂μ, patch j x ⊆ H ∧ IsOpen (H \ patch j x)
  patch_unbounded : ∀ j, ∀ᵐ x ∂μ, ∀ z ∈ lowerUnion (patch j x),
    ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (patch j x)) z)
  patch_mean : ∀ j, IsLocalSetMean (patch j) D.cfield μ (patchMean j)
  physical_harmonic : ∀ j, ∀ᵐ x ∂μ,
    InnerProductSpace.HarmonicOnNhd (physicalMean j x) (H \ patch j x)
  represents : ∀ j, ∀ᵐ x ∂μ, ∀ φ : TestOn upperHalfPlaneOpens,
    tsupport φ ⊆ H \ patch j x →
      patchMean j x φ = ∫ z, (physicalMean j x z - D.originalMean z) * φ z
  union_marks_le : ∀ j, unionMarks j ≤ mX
  union_measurable : ∀ j, Measurable[unionMarks j, hittingSigma] (union j)
  union_closed : ∀ j x, union j x ⊆ H ∧ IsOpen (H \ union j x)
  union_local : ∀ j, IsHistoryAvoidanceLocal (unionMarks j) (union j) D.cfield μ
  marks_le : ∀ j, D.baseMarks i 0 ≤ unionMarks j
  set_recorded : ∀ j, Measurable[unionMarks j, hittingSigma] (D.baseSets i 0)
  set_subset : ∀ j x, D.baseSets i 0 x ∩ H ⊆ union j x
  patch_recorded : ∀ j, Measurable[unionMarks j, hittingSigma] (patch j)
  patch_subset : ∀ j x, patch j x ∩ H ⊆ union j x
  event_measurable : ∀ j, MeasurableSet[D.baseMarks i 0] (event j)
  union_eq : ∀ j, ∀ᵐ x ∂μ, x ∈ event j → union j x = D.baseSets i 0 x
  cover : ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → ∀ b ∈ (D.data i).O₀,
    ∃ (j : index) (z₀ : ℂ), x ∈ event j ∧
      z₀ ∈ patch j x ∪ {z : ℂ | z.im = 0} ∧
      (∃ r > 0, ∀ᶠ z in 𝓝[H] (b : ℂ),
        (D.chart i x).2.1 z ∈ freeNear (D.baseSets i 0 x) (patch j x) z₀ r) ∧
      Tendsto (D.chart i x).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
      Tendsto (fun z => physicalMean j x ((D.chart i x).2.1 z) + D.scale +
        D.constant * (D.chart i x).2.2 ((D.chart i x).2.1 z) - Aux61GlueK.refMean0 (D.data i) z)
        (𝓝[H] (b : ℂ)) (𝓝 0)

attribute [instance] ZeroComparisons.countable

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
    (μ := S.μ) S.κ)
include hR

/-- Physical union comparisons and accessible reference germs identify the
boundary of every actual source initial Gaussian mean on its record law.
The chart is made the identity off its restart event only inside the proof. -/
theorem source_initialBoundary_of_comparisons (i : F.ι)
    (hsets : Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      ((S.marksData F).baseSets i 0))
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)))
    (C : ZeroComparisons (S.marksData F) i)
    {g : S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hG : @IsChartGaussAt (S.Ω × HistorySpace 0 0) _
      ((S.marksData F).β i) ((S.marksData F).mβ i)
      S.μ ((S.marksData F).Z i) ((S.marksData F).B i)
      ((S.marksData F).code i) 0 ((S.marksData F).sigma i 0) g) :
    (S.marksData F).InitialBoundary i g := by
  let D := S.marksData F
  let : MeasurableSpace (D.β i) := D.mβ i
  let : Countable C.index := C.countable
  have hX := S.own.coupling.2.2.2.1
  have hE := sourceEvent_marks F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life hR i 0
  have hc := sourceChart_marks F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life hR hX i 0
  have hcm := @IsMeasChart.chartOf (S.Ω × HistorySpace 0 0) (D.baseMarks i 0)
    (D.event i) hE (D.chart i) hc
  have hconf := isConformal_chartOf (hR.spec i).conf
  have hG' := hG
  rw [Aux61GRec.sigma_zero_eq_marks (S.marksData F) i] at hG'
  change IsChartGaussAt S.μ (D.Z i) (D.B i) (D.code i) 0
    (D.baseMarks i 0 ⊔ germSigma
      (liveSet (liveEv (D.Z i) (D.B i) (D.code i) 0) (D.baseSets i 0)) D.cfield) g at hG'
  rw [sup_comm] at hG'
  apply initialBoundary_of_zero_component_comparisons
    (measurable_down (hR.selected_measurable i))
    (measurable_accessExitCode (hR.spec i) (hR.open_window i) (hR.zero_window i)
      (hR.landing i) (hR.injective_path i) (hR.continuous_lift i)
      (S.own.coupling.2.1.comp measurable_fst))
    (S.own.coupling.2.1.comp measurable_fst)
    (Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR).1
    (source_zero_field S F) hconf D.scale D.constant
    (fun _ _ hq => accessExitCode_field_eq (hR.spec i).conf (mem_exitEv_of_lt_accessLife hq))
    nullMarks_le
    (sourceHistory_marks F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life hR hX i 0).comap_le
    (source_zero_code_marks S F hR i)
    (@IsMeasChart.dom _ (D.baseMarks i 0) _ hcm)
    (@IsMeasChart.fwd _ (D.baseMarks i 0) _ hcm)
    (@IsMeasChart.lift _ (D.baseMarks i 0) _ hcm)
    (continuousOn_lift_chartOf (hR.continuous_lift i))
    (harmonicOnNhd_lift_chartOf (hR.harmonic_lift i))
    (hsets.mono nullMarks_le le_rfl)
    (sourceSets_closed F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField hR.spec i 0)
    (source_initial_locality S F hR i hsets (source_initial_contains S F hR i hretained))
    ?_ C.patch_measurable C.patch_closed C.patch_unbounded C.patch_mean C.physical_harmonic
    C.represents C.union_marks_le
    (fun j => (C.union_measurable j).mono (C.union_marks_le j) le_rfl) C.union_closed C.union_local
    C.marks_le C.set_recorded C.set_subset C.patch_recorded C.patch_subset C.event_measurable C.union_eq
    hG' (D.data i) ?_ ?_
  · exact Eventually.of_forall fun p hp hq => by
      rw [chartOf_of_mem (mem_exitEv_of_lt_accessLife hq).1.1]
      exact sourceSets_geometry F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
        S.κ S.ownField hR.spec i 0 p ⟨hp, hq⟩
  · filter_upwards [source_zero_alive_iff S F hR i] with p hp hB
    exact hp.2 hB
  · filter_upwards [C.cover, hR.physical_stop i] with p hp hs hB
    rw [chartOf_of_mem (hs hB).1]
    exact hp hB

end InteractingSLE.Sec5.Aux61GPrime
