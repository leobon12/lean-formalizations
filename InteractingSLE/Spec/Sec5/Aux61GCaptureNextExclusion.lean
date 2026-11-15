/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextMarks
import InteractingSLE.Spec.Sec5.Aux61GAlignCapture

/-! # Exclude the source event from pointwise capture by the actual records

The source MARKS facts and physical wiring are constructed before applying
the countable completed-capture theorem. The only capture input is an
almost-sure existential index depending on the realized future.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GCaptureNext
open Aux61SlitW Aux61SlitW.SourceSetting Aux61Marks Aux61ChLoc Aux61ULoc
open Aux61FibData Aux61GInst LawUnique GlueCond
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ)
  (hgeo : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (F.start i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
  (hpath : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ v : ℝ≥0, 0 < v →
    (v : ℝ≥0∞) < F.contact i p → F.path i p v = S.path p.1 (F.start i + v))

include hR hgeo hpath

/-- Source-window exclusion with component comparisons and pointwise
completed capture. No history-cover or all-index completion input remains. -/
theorem ae_not_source_of_pointwise_capture
    (hcode : ∀ i q, (Aux61FibK.codeFiltration.{u} q).comap
      (fun p => ULift.up.{u} ((S.marksData F).code i p)) ≤ (S.marksData F).baseMarks i q)
    (hsets : ∀ i q, Measurable[(S.marksData F).baseMarks i q, hittingSigma]
      ((S.marksData F).baseSets i q))
    (C : ∀ i, Aux61GPrime.ZeroComparisons (S.marksData F) i)
    (hneg : Aux61Cov.R5NegStatement.{u})
    (hcaptured_cover : ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture (S.marksData F) i p) :
    ∀ᵐ p ∂S.μ, ¬ S.windowEvent p := by
  have hF := marksFacts_of_component_comparisons S F hR hgeo hpath hcode hsets C
  exact Aux61GAlign.ae_not_source_of_completed_capture S F hF hR.chart_measurable hR.kappa
    (regular_contains S F hR hgeo hpath) hneg hcaptured_cover

end InteractingSLE.Sec5.Aux61GCaptureNext
