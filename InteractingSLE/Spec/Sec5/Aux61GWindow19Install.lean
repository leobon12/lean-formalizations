/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow19Heights

/-! # Install arbitrary countably indexed heights and access restrictions

R103's word-piece and integer phase labels may be included in ι. The
supplied access selection is intersected with the Borel seed/buffer piece.
WindowData, selection measurability and the top's seed-height type follow
without choosing any particular landing height or real comparison set.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow19
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61GR1F Aux61GWord Aux61GInst Aux61FibData LawUnique
universe u

/-- Install reference words and thin comparison windows on any countable
index, retaining the uniform record pieces under arbitrary access tests. -/
def localizedChoices (S : SourceSetting.{u}) {ι : Type} [Countable ι]
    (t : ι → Aux61GWindow17.GoodTime S) (J : ι → Aux61GWindow17.AllowedWindow)
    (R : ι → ReferenceWord S.κ) (G : ι → WindowGeometry)
    (A : ι → Set (SourceRecord S.nL S.nR)) : RestartChoices S :=
  Aux61GChoice15.windowChoices S (fun i => (t i).1)
    (fun i => Aux61GWindow17.windowRecords S (t i) (J i) ∩ A i) R G

variable (S : SourceSetting.{u}) {ι : Type} [Countable ι]
  (t : ι → Aux61GWindow17.GoodTime S) (J : ι → Aux61GWindow17.AllowedWindow)
  (R : ι → ReferenceWord S.κ) (G : ι → WindowGeometry)
  (A : ι → Set (SourceRecord S.nL S.nR))

/-- Borel access tests give the exact hsel type of the current top. -/
theorem localized_selected_measurable (hA : ∀ i, MeasurableSet (A i)) :
    ∀ i, MeasurableSet ((localizedChoices S t J R G A).selected i) :=
  fun i => (Aux61GWindow17.measurableSet_windowRecords S (t i) (J i)).inter (hA i)

/-- All deterministic window fields hold for arbitrary installed heights. -/
theorem localized_window_fields : WindowFields (localizedChoices S t J R G A).toR1Restart where
  open_window i := (G i.1).open_window
  zero_window i := (G i.1).zero_window
  clearance _ := rfl
  kappa _ := rfl
  reference i := (R i.1).reference

/-- The thin window is placed in the fixed seed window; its closed
buffer is placed inside the candidate's certified finite buffer. -/
def localizedPlacement
    (hV : ∀ i, (G i).V ⊆ seedExitWindow (basisBuffer (J i).1.1.1.1) ((J i).1.1.1.2.2 : ℝ))
    (hB : ∀ i, closure (G i).buffer ⊆ closure (outerBuffer (J i).1.1)) :
    SeedPlacement (localizedChoices S t J R G A) where
  time := t
  window := J
  time_eq _ := rfl
  selected_sub _ := inter_subset_left
  window_sub := hV
  buffer_sub := hB

/-- The exact V binder of T12Asm5Final, for the caller's per-outcome
height-indexed words and thin comparison windows. -/
def localizedWindows
    (hV : ∀ i, (G i).V ⊆ seedExitWindow (basisBuffer (J i).1.1.1.1) ((J i).1.1.1.2.2 : ℝ))
    (hB : ∀ i, closure (G i).buffer ⊆ closure (outerBuffer (J i).1.1)) :
    Aux61SlitWX.WindowData (Aux61WndCap.finiteRestart (localizedChoices S t J R G A))
      (finiteChoices (localizedChoices S t J R G A)).hasChart :=
  (localizedPlacement S t J R G A hV hB).windows (localized_window_fields S t J R G A)

/-- Transfer canonical seed heights to the exact hSeed type of the top.
The preceding positive/negative lemmas allow every landing height. -/
theorem localized_seed_heights
    (hSeed : ∀ i, PiecewiseConstantBoundaryData.leftLim (R i).boundary 0 = -sleLambda S.κ ∧
      PiecewiseConstantBoundaryData.rightLim (R i).boundary 0 = sleLambda S.κ) :
    ∀ i, PiecewiseConstantBoundaryData.leftLim
          ((Aux61WndCap.finiteRestart (localizedChoices S t J R G A)).data i).bR 0 =
          -sleLambda ((Aux61WndCap.finiteRestart (localizedChoices S t J R G A)).data i).κ ∧
        PiecewiseConstantBoundaryData.rightLim
          ((Aux61WndCap.finiteRestart (localizedChoices S t J R G A)).data i).bR 0 =
          sleLambda ((Aux61WndCap.finiteRestart (localizedChoices S t J R G A)).data i).κ :=
  fun i => hSeed i.1

end InteractingSLE.Sec5.Aux61GWindow19
