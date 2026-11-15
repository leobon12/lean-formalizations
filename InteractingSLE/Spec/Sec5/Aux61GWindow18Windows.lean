/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow18Choices

/-! # WindowData for the exact normalized finite-restricted choices

The fixed seed gap is valid on each index's record selection. All fields
of WINDOW's current WindowData input are constructed without assumptions.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow18
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61GR1F Aux61GWord Aux61FibData Aux61GInst LawUnique
universe u

/-- The complete WindowData input of the current finite-restriction route.
The seed condition is imposed on precisely the same record event as the
finite-buffer test, using the exact normalized chart. -/
def windows (S : SourceSetting.{u}) :
    Aux61SlitWX.WindowData (Aux61WndCap.finiteRestart (choices S)) (finiteChoices S).hasChart where
  open_window i := (windowGeometry i.1.2.2.1.1).open_window
  zero_window i := (windowGeometry i.1.2.2.1.1).zero_window
  clearance _ := rfl
  kappa _ := rfl
  reference i := (Aux61GWindow17.intervalWord S i.1.2.1).reference
  buffer i := basisBuffer (i.1.2.2.1.1 : WindowIndex).1
  gap i := ((i.1.2.2.1.1 : WindowIndex).2.2 : ℝ)
  bounded i := (i.1.2.2.1.1.2.2.2.2.isBounded.subset
    (subset_closure.trans (i.1.2.2.1.1.2.2.2.1.trans subset_closure)))
  window_subset _ := Subset.rfl
  seed i := by
    filter_upwards [Aux61GWindow17.refinedFamily_seed S i] with p hp he a ha
    change boundedInverse (sourceChart (family S) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life i p) (a : ℂ) ∉ _
    rw [family_sourceChart_eq S i p]
    exact hp ((family_event_eq S i) ▸ he) a ha

/-- The normalized source has all record restart facts; its physical
exit and own-tip inputs are the landed unconditional theorems. -/
theorem family_record_restart (S : SourceSetting.{u}) : RecordRestartFacts S (family S) :=
  Aux61GCaptureNext.normalized_recordRestartFacts _ _
    (Aux61SlitWZ.readers (finiteChoices S) (finiteChoices_selected_measurable S))
    (Aux61SlitWY.ownTipForwardLimit S) (windows S)
    (Aux61WndCap.physicalExit_finiteRestrict (choices S) (choices_selected_measurable S))

/-- The regular cut used in the current normalized-capture route is
conull, independently of comparisons and completed captures. -/
theorem family_ae_good (S : SourceSetting.{u}) :
    ∀ᵐ p ∂S.μ, p ∈ Aux61Asm2.goodSet S (family S) := by
  have R := Aux61SlitWZ.readers (finiteChoices S) (finiteChoices_selected_measurable S)
  have hR := family_record_restart S
  exact ae_mem_goodSet S (family S)
    (ae_goodPt S (family S) (path_version_withRecordPath S (family S))
      (dom_component_of_record S (family S) (R.record_domain (finiteChoices S).hasChart) hR.event_version)
      hR.raw.regular)

/-- The exact cut-source restart facts, with no remaining window or
normalization premise. -/
theorem family_cut_restart (S : SourceSetting.{u}) :
    SourceRestartFacts (cutSource S (family S)) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ :=
  Aux61GCaptureNext.normalized_cut_restart _ _
    (Aux61SlitWZ.readers (finiteChoices S) (finiteChoices_selected_measurable S))
    (Aux61SlitWY.ownTipForwardLimit S) (windows S)
    (Aux61WndCap.physicalExit_finiteRestrict (choices S) (choices_selected_measurable S))

/-- Every comparison set in this source is bounded. -/
theorem family_isBounded_real_window (S : SourceSetting.{u}) (i : (choices S).Idx) :
    Bornology.IsBounded ((family S).data i).O₀ := isBounded_real_window _

end InteractingSLE.Sec5.Aux61GWindow18
