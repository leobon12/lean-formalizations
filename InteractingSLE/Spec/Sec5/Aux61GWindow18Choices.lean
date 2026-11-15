/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow18Geometry

/-! # Record-localized choices for the normalized finite-restriction route

Both the seed collar and the pole-free compact buffer are tested on the
initial record. The additional finite restriction therefore discards none
of these selected records, pointwise rather than only almost surely.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow18
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61GR1F Aux61GWord Aux61FibData LawUnique
universe u

/-- The landed seed and finite-buffer pieces, with bounded real windows. -/
def choices (S : SourceSetting.{u}) : RestartChoices S where
  ι := Aux61GWindow17.RefinedIndex S
  q i := i.1.1
  selected i := Aux61GWindow17.windowRecords S i.1 i.2.2
  data i := referenceWindowData S.κ_pos (Aux61GWindow17.intervalWord S i.2.1)
    (windowGeometry i.2.2.1.1)
  left i := (Aux61GWindow17.intervalWord S i.2.1).left
  right i := (Aux61GWindow17.intervalWord S i.2.1).right

/-- The exact finite restriction consumed by WINDOW's current cover. -/
abbrev finiteChoices (S : SourceSetting.{u}) :=
  Aux61SlitWAC.restrictChoices (choices S) (Aux61WndCap.finiteRestrict (choices S))

/-- The fully normalized source, on that exact restricted choice model. -/
abbrev family (S : SourceSetting.{u}) :=
  Aux61SlitWX.source (finiteChoices S).toR1Restart (finiteChoices S).hasChart

theorem choices_selected_measurable (S : SourceSetting.{u}) :
    ∀ i, MeasurableSet ((choices S).selected i) :=
  fun i => Aux61GWindow17.measurableSet_windowRecords S i.1 i.2.2

theorem finiteChoices_selected_measurable (S : SourceSetting.{u}) :
    ∀ i, MeasurableSet ((finiteChoices S).selected i) :=
  Aux61WndCap.selected_measurable_finiteRestrict (choices S) (choices_selected_measurable S)

/-- Every selected initial record survives the additional finite test.
This includes the particular index selected by an actual capture. -/
theorem selected_survives_finite (S : SourceSetting.{u}) (i : (choices S).Idx)
    {y : SourceRecord S.nL S.nR} (hy : y ∈ (choices S).toR1Restart.selected i) :
    y ∈ (finiteChoices S).toR1Restart.selected i := by
  refine ⟨⟨hy.1, ?_⟩, hy.2⟩
  have he : Aux61WndCap.finiteRestrict (choices S) i.1 =
      Aux61WndCap.normFiniteRecords (choices S) i ((choices S).data i.1).buffer := by
    unfold Aux61WndCap.finiteRestrict
    exact dite_eq_left i.2
  rw [he]
  refine ⟨⟨hy, hy.1.1.2⟩, ?_⟩
  rw [normalized_chart_eq_recordChart]
  exact hy.1.2.1

theorem finite_selected_eq (S : SourceSetting.{u}) (i : (choices S).Idx) :
    (finiteChoices S).toR1Restart.selected i = (choices S).toR1Restart.selected i := by
  ext y
  exact ⟨fun hy => ⟨hy.1.1, hy.2⟩, selected_survives_finite S i⟩

/-- The actual event is unchanged by the finite restriction and by the
bounded-real-window correction. -/
theorem family_event_eq (S : SourceSetting.{u}) (i : (choices S).Idx) :
    (family S).event i = (Aux61GWindow17.refinedFamily S).event i := by
  change (fun p => sourceRecord (family S) (rationalTime S.s)
    S.own.W S.own.VL S.own.VR S.life i p) ⁻¹' (finiteChoices S).toR1Restart.selected i = _
  rw [finite_selected_eq]
  rfl

/-- The normalized chart is exactly the chart used for the landed seed
pieces and captures. Window and reference choices do not change it. -/
theorem family_chart_eq (S : SourceSetting.{u}) (i : (choices S).Idx) :
    (family S).chart i = (Aux61GWindow17.refinedFamily S).chart i :=
  normalized_chart_eq_recordChart (finiteChoices S) i

theorem family_sourceChart_eq (S : SourceSetting.{u}) (i : (choices S).Idx)
    (p : S.Ω × HistorySpace 0 0) :
    sourceChart (family S) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p =
      sourceChart (Aux61GWindow17.refinedFamily S) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p := by
  unfold sourceChart
  rw [family_chart_eq]
  rfl

/-- All selected path values agree with the landed capturing family. -/
theorem family_inPath_eq (S : SourceSetting.{u}) (i : (choices S).Idx)
    (p : S.Ω × HistorySpace 0 0) :
    inPath ((family S).event i)
      (sourceChart (family S) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((family S).path i) ((family S).contact i) p =
    inPath ((Aux61GWindow17.refinedFamily S).event i)
      (sourceChart (Aux61GWindow17.refinedFamily S) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i)
      ((Aux61GWindow17.refinedFamily S).path i) ((Aux61GWindow17.refinedFamily S).contact i) p := by
  funext v
  unfold inPath
  rw [family_event_eq, family_sourceChart_eq]
  rfl

end InteractingSLE.Sec5.Aux61GWindow18
