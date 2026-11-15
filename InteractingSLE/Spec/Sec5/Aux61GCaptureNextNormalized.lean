/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextRestart
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextExclusion

/-! # Pointwise capture for the actual fully normalized R1 cut source

The restart geometry, code marks, set measurability and initial data are
proved for this precise source. Its remaining comparison and capture inputs
are physical component comparisons and pointwise completed capture.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GCaptureNext
open Aux61SlitW Aux61Asm2 Aux61SlitWX Aux61FibData Aux61Marks Aux61ULoc LawUnique
open GlueCond
universe u
variable {S : SourceSetting.{u}} (D : R1Restart S) (h : D.HasChart) (R : ReaderFacts D)
include R

/-- All MARKS facts for the normalized cut source. Its initial mean and
cutoffs come from the actual physical component comparisons. -/
theorem normalized_marksFacts (hTip : OwnTipForwardLimit S)
    (V : WindowData D h) (hExit : PhysicalExit D h)
    (C : ∀ i, Aux61GPrime.ZeroComparisons (S.marksData (cutSource S (source D h))) i) :
    MarksFacts S.μ (S.marksData (cutSource S (source D h))) := by
  have hR := normalized_cut_restart D h R hTip V hExit
  have hTa := normalized_contact_rule D h R
  have hTam := fun i => measurable_contactRule
    (measurable_infDist_retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
    (rationalTime (D.q i))
  have hTaG := fun i => isGalmarinoRule_contactRule
    (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (rationalTime (D.q i))
  apply marksFacts_of_component_comparisons S (cutSource S (source D h)) hR
    (fun i => ?_) (fun i => ?_)
    (code_marks_cut_of hR hTam hTaG hTa) (sets_marks_cut_of hR hTam hTaG hTa) C
  · filter_upwards [R.ae_geometry h i] with p hp he
    exact hp he.1
  · filter_upwards [path_version_withRecordPath S (source D h) i] with p hp he
    exact hp he.1

/-- Exclude the actual source window using only pointwise countable
capture for the normalized cut family. The former every-index capture
premise and the separate history-cover premise are absent. -/
theorem ae_not_normalized_of_pointwise_capture (hTip : OwnTipForwardLimit S)
    (V : WindowData D h) (hExit : PhysicalExit D h)
    (C : ∀ i, Aux61GPrime.ZeroComparisons (S.marksData (cutSource S (source D h))) i)
    (hneg : Aux61Cov.R5NegStatement.{u})
    (hcaptured_cover : ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture (S.marksData (cutSource S (source D h))) i p) :
    ∀ᵐ p ∂S.μ, ¬ S.windowEvent p := by
  have hR := normalized_cut_restart D h R hTip V hExit
  have hgeo : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (cutSource S (source D h)).event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1)
        (fun t => S.path p.1 t.toNNReal) (cfHullQ (rationalTime S.s) p.2)
        ((cutSource S (source D h)).start i)
        (sourceChart (cutSource S (source D h)) (rationalTime S.s)
          S.own.W S.own.VL S.own.VR S.life i p) := fun i => by
    filter_upwards [R.ae_geometry h i] with p hp he
    exact hp he.1
  have hpath : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (cutSource S (source D h)).event i →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < (cutSource S (source D h)).contact i p →
        (cutSource S (source D h)).path i p v =
          S.path p.1 ((cutSource S (source D h)).start i + v) := fun i => by
    filter_upwards [path_version_withRecordPath S (source D h) i] with p hp he
    exact hp he.1
  exact Aux61GAlign.ae_not_source_of_completed_capture S (cutSource S (source D h))
    (normalized_marksFacts D h R hTip V hExit C) hR.chart_measurable hR.kappa
    (regular_contains S (cutSource S (source D h)) hR hgeo hpath) hneg hcaptured_cover

end InteractingSLE.Sec5.Aux61GCaptureNext
