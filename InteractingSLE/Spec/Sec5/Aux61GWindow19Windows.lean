/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow19Placement

/-! # Height-parametric WindowData in the theorem top's exact type

The reference heights and thin real comparison sets are unrestricted by
this construction. Placement supplies the uniform seed collar; the
existing deterministic window fields supply openness and RefWin.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow19
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61GR1F Aux61GWord Aux61GInst Aux61FibData LawUnique
universe u
variable {S : SourceSetting.{u}}

/-- The exact choice restriction used by the current theorem tops. -/
abbrev finiteChoices (C : RestartChoices S) : RestartChoices S :=
  Aux61SlitWAC.restrictChoices C (Aux61WndCap.finiteRestrict C)

/-- The normalized source associated to any per-outcome choice family. -/
abbrev family (C : RestartChoices S) : SourceRestartData S.Ω S.nL S.nR :=
  Aux61SlitWX.source (Aux61WndCap.finiteRestart C) (finiteChoices C).hasChart

namespace SeedPlacement
variable {C : RestartChoices S} (P : SeedPlacement C)
include P

/-- WindowData in precisely the `V` type of `T12Asm5Final`, for arbitrary
installed word heights and arbitrary real comparison neighborhoods. -/
def windows (W : WindowFields C.toR1Restart) :
    Aux61SlitWX.WindowData (Aux61WndCap.finiteRestart C) (finiteChoices C).hasChart where
  open_window := W.open_window
  zero_window := W.zero_window
  clearance := W.clearance
  kappa := W.kappa
  reference := W.reference
  buffer i := basisBuffer (P.window i.1).1.1.1.1
  gap i := ((P.window i.1).1.1.1.2.2 : ℝ)
  bounded i := (P.window i.1).1.1.2.2.2.2.isBounded.subset
    (subset_closure.trans ((P.window i.1).1.1.2.2.2.1.trans subset_closure))
  window_subset i := P.window_sub i.1
  seed i := by
    filter_upwards [S.counterflow_good] with p hcf he a ha
    have hw := P.selected_sub i.1 he.1.1
    have hf := Aux61GWindow17.seed_on_windowRecords S (P.time i.1) (P.window i.1) hw ha
    change boundedInverse (sourceChart (family C) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life i p) (a : ℂ) ∉ _
    rw [sourceChart_eq_time (finiteChoices C) i (P.time i.1) (P.time_eq i.1) p]
    change boundedInverse (Aux61GWindow17.recordChart S (P.time i.1) (C.record i.1 p)) (a : ℂ) ∉
      Aux61SlitWAB.recordBoundary (rationalTime S.s) (Aux61ULoc.stopRec (rationalTime S.s) p.2) at hf
    rwa [Aux61SlitWAB.recordBoundary_stopRec_eq hcf.1.1.2] at hf

/-- All restart facts follow for the placed, height-indexed source. -/
theorem record_restart (hsel : ∀ i, MeasurableSet (C.selected i)) (W : WindowFields C.toR1Restart) :
    RecordRestartFacts S (family C) :=
  Aux61GCaptureNext.normalized_recordRestartFacts _ _
    (Aux61SlitWZ.readers (finiteChoices C) (Aux61WndCap.selected_measurable_finiteRestrict C hsel))
    (Aux61SlitWY.ownTipForwardLimit S) (P.windows W) (Aux61WndCap.physicalExit_finiteRestrict C hsel)

/-- The exact regularity cut used by the current top is conull before
any access or completed-capture input is supplied. -/
theorem ae_good (hsel : ∀ i, MeasurableSet (C.selected i)) (W : WindowFields C.toR1Restart) :
    ∀ᵐ p ∂S.μ, p ∈ Aux61Asm2.goodSet S (family C) := by
  have R := Aux61SlitWZ.readers (finiteChoices C) (Aux61WndCap.selected_measurable_finiteRestrict C hsel)
  have hR := P.record_restart hsel W
  exact ae_mem_goodSet S (family C)
    (ae_goodPt S (family C) (path_version_withRecordPath S (family C))
      (dom_component_of_record S (family C) (R.record_domain (finiteChoices C).hasChart) hR.event_version)
      hR.raw.regular)

/-- Exact source-restart facts for the per-outcome family. -/
theorem cut_restart (hsel : ∀ i, MeasurableSet (C.selected i)) (W : WindowFields C.toR1Restart) :
    SourceRestartFacts (cutSource S (family C)) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ :=
  Aux61GCaptureNext.normalized_cut_restart _ _
    (Aux61SlitWZ.readers (finiteChoices C) (Aux61WndCap.selected_measurable_finiteRestrict C hsel))
    (Aux61SlitWY.ownTipForwardLimit S) (P.windows W) (Aux61WndCap.physicalExit_finiteRestrict C hsel)

end SeedPlacement
end InteractingSLE.Sec5.Aux61GWindow19
