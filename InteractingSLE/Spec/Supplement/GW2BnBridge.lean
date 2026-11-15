/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdoShape
import InteractingSLE.Spec.Supplement.GW2BnShape
import InteractingSLE.Spec.Supplement.GW2BnBuf

/-!
# D16's decoder: SDE's pinned near selection read measurably from the stage record

Packet PROVE-GW2-BUF (round 11). SDE's round 14 (`GW2SdoShape`, committed `0a313dfc0`) pins the near family of the
package `V.withNearS lam base kSel`. Where the near structure holds:
* its shape is `nearShape κ s flip (base ω)` (`withNearS_shape`);
* its positions are the flow-line positions of `nearDilWord s flip (base ω)` (`withNearS_positions`).

This file connects these to BUF's measurable readers.

* **`nearShape_eq_nearShapeM`** (definitional) and **`measurable_nearShape`**.
* **`positionsOf_pad`**: the positions of a family typed by a word are that word's padded positions
  (`padXL`, `padXR`).
* **`withNearS_decoder`**: suppose the base word at `ω` is read from the stage record `y` by `β`. Then the package's
  near family at `ω` has shape `nearShapeM κ s flip (β y)` and padded positions
  `padXL/XR (nearDilWord s flip (β y))`.
  These are measurable in `y` when `β` is (`measurable_nearShapeM_comp`, `measurable_nearPos_comp`). This is
  D16's decoder for `GW2BnStop.shapeStop`. At the schedule instance, `β` is the word map `(ch …).β` of the stage
  choice, measurable by the owners' `InstInputsX.word`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart GW2Sdo GW2Sdy GW2Sdx GW2Sdh GW2Sdf GW2JDetR11 GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootN4

theorem cutL_eq_cutCountL (β : BoundaryWord) : cutL β = cutCountL β := rfl

theorem cutR_eq_cutCountR (β : BoundaryWord) : cutR β = cutCountR β := rfl

/-- **SDE's explicit shape is BUF's measurable shape.** -/
theorem nearShape_eq_nearShapeM (κ : ℝ) (s : ℝ≥0) (flip : Bool) (c : BoundaryWord) :
    nearShape κ s flip c = nearShapeM κ s flip c := rfl

theorem measurable_nearShape (κ : ℝ) (s : ℝ≥0) (flip : Bool) : Measurable (nearShape κ s flip) := by
  have e : nearShape κ s flip = nearShapeM κ s flip := funext fun c => nearShape_eq_nearShapeM κ s flip c
  rw [e]
  exact measurable_nearShapeM κ s flip

theorem famShape_eq_famShapeB {κ : ℝ} (f : NearCrossingFamily.{u} κ) : famShape f = famShapeB f := rfl

/-- **The positions of a family typed by a word are its padded positions.** -/
theorem positionsOf_pad {κ : ℝ} {f : NearCrossingFamily.{u} κ} {β : BoundaryWord} (h : PositionsOf f β) :
    (∀ i : Fin f.nL, f.xL i = padXL β i) ∧ ∀ j : Fin f.nR, f.xR j = padXR β j := by
  obtain ⟨eL, eR, hL, hR⟩ := h
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have h1 := congrFun hL (Fin.cast eL.symm i)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at h1
    rw [h1, ← padXL_eq]
    rfl
  · have h1 := congrFun hR (Fin.cast eR.symm j)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at h1
    rw [h1, ← padXR_eq]
    rfl

section Pkg

variable (V : VPkgXFamily.{u}) (lam : NearDil.{u})
  (base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
  (kSel : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ)

/-- **D16's decoder.** If the base word at `ω` is the word `β y` read from the stage record `y`, then where the near
structure holds the package's near family has the shape `nearShapeM … (β y)` and the padded positions of the dilated
word `nearDilWord … (β y)`. -/
theorem withNearS_decoder (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (hlam : lam Ω c r l ω ≠ 0)
    {Y : Type*} (β : Y → BoundaryWord) (y : Y) (hy : base Ω c r l ω = β y)
    (h : NearStruct c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :
    famShapeB (((V.withNearS lam base kSel) Ω c r).nearFamily l ω) =
        nearShapeM c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (β y) ∧
      (∀ i, (((V.withNearS lam base kSel) Ω c r).nearFamily l ω).xL i =
        padXL (nearDilWord (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (β y)) i) ∧
      ∀ j, (((V.withNearS lam base kSel) Ω c r).nearFamily l ω).xR j =
        padXR (nearDilWord (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (β y)) j := by
  have hsh := withNearS_shape V lam base kSel Ω c r l ω hlam h
  have hpos := positionsOf_pad (withNearS_positions V lam base kSel Ω c r l ω hlam h)
  rw [hy] at hsh hpos
  exact ⟨hsh, hpos.1, hpos.2⟩

end Pkg

end InteractingSLE.Theorem14.GW2Bh
