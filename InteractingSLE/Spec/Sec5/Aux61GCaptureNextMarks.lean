/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextGlued
import InteractingSLE.Spec.Sec5.Aux61GPrimeCutoffs

/-! # Actual source MARKS facts from component comparisons, before capture

Initial Gaussian data, their record-law boundary values, the harmonic
correction and its cutoff are constructed from the component comparisons.
No history cover or all-selected-record future completion is an input.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
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

/-- All MARKS facts for the actual source, with component initial boundary
comparison and without any future-capture input. -/
theorem marksFacts_of_component_comparisons
    (hcode : ∀ i q, (Aux61FibK.codeFiltration.{u} q).comap
      (fun p => ULift.up.{u} ((S.marksData F).code i p)) ≤ (S.marksData F).baseMarks i q)
    (hsets : ∀ i q, Measurable[(S.marksData F).baseMarks i q, hittingSigma]
      ((S.marksData F).baseSets i q))
    (C : ∀ i, Aux61GPrime.ZeroComparisons (S.marksData F) i) :
    MarksFacts S.μ (S.marksData F) := by
  apply source_marksFacts S.own.coupling S.κ_pos S.own_infinite S.theta_bounds
    S.counterflow S.theta_field_law S.kernel_law S.theta_measure F (rationalTime S.s)
    hR hcode hsets (regular_contains S F hR hgeo hpath)
    (glued_facts S F hR hgeo hpath) (comparison_cover S F hR hpath)
  intro i
  have hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)) := by
    filter_upwards [hgeo i] with p hp he
    exact (hp he).retained
  obtain ⟨g, hg, -, hinit⟩ := Aux61GPrime.exists_source_initial_data_comp
    S F hR i (hsets i 0) hretained (C i)
  exact ⟨g, hg, hinit⟩

end InteractingSLE.Sec5.Aux61GCaptureNext
