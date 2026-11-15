/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GPrimeCompare
import InteractingSLE.Spec.Sec5.Aux61GAlignCutoffs

/-! # Source correction and cutoffs from component boundary comparisons

The source restart family has precisely the `SourceRestartData` type used
by the assembler. The existing Gaussian constructor and measurable cutoff
selection apply once the component comparison proves its record boundary.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GPrime
open Aux61SlitW Aux61SlitW.SourceSetting Aux61Marks Aux61ChLoc Aux61GCont
open LawUnique GlueCond Aux61GAlign
universe u

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
    (μ := S.μ) S.κ)
include hR

/-- The concrete source's initial Gaussian law, record boundary values,
and measurable correction/cutoff data from physical comparison inputs.
This discharges the existential initial-data input without assuming it. -/
theorem exists_source_initial_data_comp (i : F.ι)
    (hsets : Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      ((S.marksData F).baseSets i 0))
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)))
    (C : ZeroComparisons (S.marksData F) i) :
    ∃ g : S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      @IsChartGaussAt (S.Ω × HistorySpace 0 0) _
        ((S.marksData F).β i) ((S.marksData F).mβ i)
        S.μ ((S.marksData F).Z i) ((S.marksData F).B i)
        ((S.marksData F).code i) 0 ((S.marksData F).sigma i 0) g ∧
      (S.marksData F).InitialBoundary i g ∧
      Nonempty (InitialWindowData (S.Ω × HistorySpace 0 0)
        (S.μ.restrict ((S.marksData F).Z i ⁻¹' (S.marksData F).B i)) (F.data i) g) := by
  obtain ⟨g, hG⟩ := exists_source_initialGauss_of_retained S F hR i hsets hretained
  have hbd := source_initialBoundary_of_comparisons S F hR i hsets hretained C hG
  refine ⟨g, hG, hbd, nonempty_initialWindowData_of_record_boundary (S.marksData F) i
    (measurable_down (hR.selected_measurable i)) hG ?_ hbd⟩
  filter_upwards [source_zero_alive_iff S F hR i] with p hp hB
  exact hp.2 hB

end InteractingSLE.Sec5.Aux61GPrime
