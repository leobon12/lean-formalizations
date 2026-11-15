/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GChoice15Windows
import InteractingSLE.Spec.Sec5.Aux61SlitWZHistory

/-! # Good actual records and the current history-cover field

On the source window event the actual record at the specified rational
time is good. Thus history-cover selection at that time need not supply
goodness separately. In particular a nonempty family selecting all records
at that time has the exact `ChoiceInputs.history_cover` field.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GChoice15
open Aux61SlitW Aux61R1C Aux61Restart Aux61GR1F LawUnique
open GlueCond (cfHullQ)
universe u

/-- The source window event makes its actual rational-time record good. -/
theorem ae_good_at_window (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    S.windowEvent p → actRec S S.t p ∈ goodSet (rationalTime S.s) S.t :=
  Aux61SlitWZ.ae_window_good_record S

/-- Selection of a record at the source time supplies the exact good-record
history cover; goodness is proved, not a second selection premise. -/
theorem history_cover_of_time_selection {S : SourceSetting.{u}} (C : RestartChoices S)
    (hselect : ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, C.q i = S.t ∧ C.record i p ∈ C.selected i) :
    ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, C.record i p ∈ C.selected i ∧ C.record i p ∈ C.good i :=
  Aux61SlitWZ.history_cover_of_same_time_selection C hselect

/-- Fixed-time choices select all initial records; the built family still
restricts the selected records to the measurable good-record event. -/
def fixedTimeChoices (S : SourceSetting.{u}) {ι : Type} [Countable ι]
    (R : ι → ReferenceWord S.κ) (G : ι → WindowGeometry) : RestartChoices S :=
  windowChoices S (fun _ => S.t) (fun _ => univ) R G

/-- Fixed-time initial-record selection is measurable. -/
theorem fixedTimeChoices_selected_measurable (S : SourceSetting.{u})
    {ι : Type} [Countable ι] (R : ι → ReferenceWord S.κ) (G : ι → WindowGeometry) :
    ∀ i, MeasurableSet ((fixedTimeChoices S R G).selected i) :=
  fun _ => MeasurableSet.univ

/-- A nonempty fixed-time family covers the source event by good selected
records, with no future capture or independent history-cover hypothesis. -/
theorem fixedTimeChoices_history_cover (S : SourceSetting.{u})
    {ι : Type} [Countable ι] [Nonempty ι]
    (R : ι → ReferenceWord S.κ) (G : ι → WindowGeometry) :
    ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, (fixedTimeChoices S R G).record i p ∈ (fixedTimeChoices S R G).selected i ∧
        (fixedTimeChoices S R G).record i p ∈ (fixedTimeChoices S R G).good i := by
  apply history_cover_of_time_selection
  exact ae_of_all _ fun _ _ => ⟨(Classical.ofNonempty : ι), rfl, mem_univ _⟩

end InteractingSLE.Sec5.Aux61GChoice15
