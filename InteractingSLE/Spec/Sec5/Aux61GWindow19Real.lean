/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow19Install

/-! # Thin real comparison sets with the same actual capturing window

The caller may take O to be a seed interval union a landing interval.
The closed buffer's real trace lies in O by the candidate's certificate.
This constructor makes both seed placement inclusions definitional.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow19
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61GR1F Aux61GWord Aux61GInst Aux61FibData LawUnique
universe u

/-- Keep the actual capturing window and finite buffer, and install the
caller's open real comparison neighborhood with its geometric certificate. -/
def windowGeometryIn (j : SeedWindowIndex) (O : Set ℝ) (hO : IsOpen O)
    (hreal : ∀ z ∈ closure (outerBuffer j), z.im = 0 → z.re ∈ O) : WindowGeometry :=
  { Aux61GWindow18.windowGeometry j with O₀ := O, open_real := hO, real_buffer := hreal }

/-- Per-outcome words and access tests on countably indexed thin windows. -/
def localizedRealChoices (S : SourceSetting.{u}) {ι : Type} [Countable ι]
    (t : ι → Aux61GWindow17.GoodTime S) (J : ι → Aux61GWindow17.AllowedWindow)
    (R : ι → ReferenceWord S.κ) (O : ι → Set ℝ) (hO : ∀ i, IsOpen (O i))
    (hreal : ∀ i, ∀ z ∈ closure (outerBuffer (J i).1.1), z.im = 0 → z.re ∈ O i)
    (A : ι → Set (SourceRecord S.nL S.nR)) : RestartChoices S :=
  localizedChoices S t J R (fun i => windowGeometryIn (J i).1.1 (O i) (hO i) (hreal i)) A

variable (S : SourceSetting.{u}) {ι : Type} [Countable ι]
  (t : ι → Aux61GWindow17.GoodTime S) (J : ι → Aux61GWindow17.AllowedWindow)
  (R : ι → ReferenceWord S.κ) (O : ι → Set ℝ) (hO : ∀ i, IsOpen (O i))
  (hreal : ∀ i, ∀ z ∈ closure (outerBuffer (J i).1.1), z.im = 0 → z.re ∈ O i)
  (A : ι → Set (SourceRecord S.nL S.nR))

/-- These thin-window choices have a proved seed placement. -/
def localizedRealPlacement : SeedPlacement (localizedRealChoices S t J R O hO hreal A) :=
  localizedPlacement S t J R (fun i => windowGeometryIn (J i).1.1 (O i) (hO i) (hreal i)) A
    (fun _ => Subset.rfl) (fun _ => Subset.rfl)

/-- The exact top-level V input, with arbitrary per-outcome height and
thin real sets. No seed, normalization or placement hypothesis remains. -/
def localizedRealWindows :
    Aux61SlitWX.WindowData (Aux61WndCap.finiteRestart (localizedRealChoices S t J R O hO hreal A))
      (finiteChoices (localizedRealChoices S t J R O hO hreal A)).hasChart :=
  (localizedRealPlacement S t J R O hO hreal A).windows
    (localized_window_fields S t J R (fun i => windowGeometryIn (J i).1.1 (O i) (hO i) (hreal i)) A)

/-- The exact top-level hsel input follows from Borel access tests. -/
theorem localizedReal_selected_measurable (hA : ∀ i, MeasurableSet (A i)) :
    ∀ i, MeasurableSet ((localizedRealChoices S t J R O hO hreal A).selected i) :=
  localized_selected_measurable S t J R (fun i => windowGeometryIn (J i).1.1 (O i) (hO i) (hreal i)) A hA

/-- The deterministic window fields needed when porting hcap. -/
theorem localizedReal_window_fields :
    WindowFields (localizedRealChoices S t J R O hO hreal A).toR1Restart :=
  localized_window_fields S t J R (fun i => windowGeometryIn (J i).1.1 (O i) (hO i) (hreal i)) A

end InteractingSLE.Sec5.Aux61GWindow19
