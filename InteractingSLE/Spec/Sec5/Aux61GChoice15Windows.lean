/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R1CBuild
import InteractingSLE.Spec.Sec5.Aux61GR1FWindows

/-! # Buffered reference windows in the current restart-choice interface

The reference words and buffered windows already constructed by GLUEINST
give the five window fields on the original choice index. The good-record
restriction and chart construction remain those of `RestartChoices`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace InteractingSLE.Sec5.Aux61GChoice15
open Aux61SlitW Aux61R1C Aux61GR1F Aux61FibData Aux61Fib
universe u

/-- Install the landed buffered reference data directly in restart choices. -/
def windowChoices (S : SourceSetting.{u}) {ι : Type} [Countable ι]
    (q : ι → ℚ) (selected : ι → Set (SourceRecord S.nL S.nR))
    (R : ι → ReferenceWord S.κ) (G : ι → WindowGeometry) : RestartChoices S where
  ι := ι
  q := q
  selected := selected
  data i := referenceWindowData S.κ_pos (R i) (G i)
  left i := (R i).left
  right i := (R i).right

variable (S : SourceSetting.{u}) {ι : Type} [Countable ι]
  (q : ι → ℚ) (selected : ι → Set (SourceRecord S.nL S.nR))
  (R : ι → ReferenceWord S.κ) (G : ι → WindowGeometry)

/-- The actual chosen window is open. -/
theorem windowChoices_open_window :
    ∀ i, IsOpen ((windowChoices S q selected R G).data i).V :=
  fun i => (G i).open_window

/-- The seed belongs to the actual chosen window. -/
theorem windowChoices_zero_window :
    ∀ i, (0 : ℂ) ∈ ((windowChoices S q selected R G).data i).V :=
  fun i => (G i).zero_window

/-- The fibre clearance is computed from this same window. -/
theorem windowChoices_clearance : ∀ i,
    ((windowChoices S q selected R G).data i).ℓ =
      clr ((windowChoices S q selected R G).data i).V := fun _ => rfl

/-- The reference word uses the source parameter. -/
theorem windowChoices_kappa :
    ∀ i, ((windowChoices S q selected R G).data i).κ = S.κ := fun _ => rfl

/-- The forbidden reference interval is the interval installed in the choices. -/
theorem windowChoices_reference : ∀ i,
    Aux61Cov.RefWin ((windowChoices S q selected R G).data i).κ
      ((windowChoices S q selected R G).data i).bR
      ((windowChoices S q selected R G).data i).JR
      (Ioo ((windowChoices S q selected R G).left i)
        ((windowChoices S q selected R G).right i)) := fun i => (R i).reference

end InteractingSLE.Sec5.Aux61GChoice15
