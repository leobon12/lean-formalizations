/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWZInverse
import InteractingSLE.Spec.Sec5.Aux61SlitWZHistory
import InteractingSLE.Spec.Sec5.Aux61SlitWZModel

/-! # Fill the exact `ChoiceInputs` using the proved slit fields

The restart geometry, physical-stop field and good-record conjunct of
history coverage are constructed. The remaining input types refer to the
literal family and retain the original comparison and completion quantifiers.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWZ
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Asm2 Aux61FibData Aux61GInst Aux61ULoc LawUnique
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The exact consumer record with the slit-wiring fields proved.
The caller supplies the remaining original-index window fields, the actual
chosen chart's geometry, uniform seed windows, finite buffer, comparison,
selection coverage and the unchanged every-selected-index completion. -/
theorem choiceInputs_of_chart_geometry
    (selected_measurable : ∀ i, MeasurableSet (C.selected i))
    (open_window : ∀ i, IsOpen (C.data i).V)
    (zero_window : ∀ i, (0 : ℂ) ∈ (C.data i).V)
    (clearance : ∀ i, (C.data i).ℓ = clr (C.data i).V)
    (kappa : ∀ i, (C.data i).κ = S.κ)
    (reference : ∀ i, Aux61Cov.RefWin (C.data i).κ (C.data i).bR (C.data i).JR
      (Ioo (C.left i) (C.right i)))
    (chart_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (GlueCond.cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (windows : SeedWindows C)
    (finite_buffer : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      ∀ z ∈ closure (C.toR1Restart.data i).buffer ∩ Hbar,
        boundedInverse (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) z ≠ 1)
    (comparisons : ∀ i, Nonempty
      (Aux61GAlign.ZeroComparisons (S.marksData (cutSource S (withRecordPath S C.fam))) i))
    (selected_cover : ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, C.q i = S.t ∧ C.record i p ∈ C.selected i)
    (completed_window : ∀ i, ∀ᵐ p ∂S.μ,
      sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ C.toR1Restart.selected i →
      S.windowEvent p → C.fam.contact i p < ⊤ ∧
      (∀ v : ℝ≥0, (v : ℝ≥0∞) < C.fam.contact i p →
        inPath (C.fam.event i) (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
          ((withRecordPath S C.fam).path i) (C.fam.contact i) p v ∈ (C.toR1Restart.data i).V) ∧
      ∃ y ∈ Ioo (C.toR1Restart.left i) (C.toR1Restart.right i),
        Tendsto (inPath (C.fam.event i)
          (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
          ((withRecordPath S C.fam).path i) (C.fam.contact i) p)
          (𝓝[<] (C.fam.contact i p).toNNReal) (𝓝 (y : ℂ))) : C.ChoiceInputs where
  selected_measurable := selected_measurable
  open_window := open_window
  zero_window := zero_window
  clearance := clearance
  kappa := kappa
  reference := reference
  physical_stop := physical_stop_of_finite_buffer C selected_measurable chart_geometry finite_buffer
  geometric := geometric_of_chart_geometry C selected_measurable chart_geometry windows
  chart_geometry := chart_geometry
  comparisons := comparisons
  history_cover := history_cover_of_same_time_selection C selected_cover
  completed_window := completed_window

end InteractingSLE.Sec5.Aux61SlitWZ
