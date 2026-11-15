/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BnMeas

/-!
# The near shape and positions are measurable in the base word (decision D16)

Packet PROVE-GW2-BUF (round 11). SDE's round 14 (`GW2SdoShape`, not yet committed) pins the near family's shape as
`nearShape κ s flip c` and its positions as the flow-line positions of `nearDilWord s flip c`. This file proves the
measurability of these functions of the base word `c`, at a fixed dilation scale `s` and orientation `flip`. Both
are fixed along a history: J32's near dilation `nearLam` depends only on the history length.

* `nearShapeM κ s flip c`: SDE's `nearShape` with the far-block counts `cutCountL`/`cutCountR`. These have the
  bodies of SDE's `cutL`/`cutR`, so the two shapes agree by definition.
* **`measurable_nearShapeM`**: measurable, with countable (discrete) range `ℕ × ℕ × ℕ × ℕ × Bool`.
* **`measurable_nearPosL`**, **`measurable_nearPosR`**: the padded positions of the dilated word.
* **`measurable_nearShapeM_comp`**, **`measurable_nearPos_comp`**: the same after any measurable base-word reader,
  e.g. GEOM2's word map of the stage record (`GW2Wm.wordMap_targets`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Restart GW2Sdy GW2TipSystem GW2TipSystem.RootH10

open Classical in
/-- **The explicit near shape of a base word** (SDE's `nearShape`, with `cutCountL`/`cutCountR`). -/
def nearShapeM (κ : ℝ) (s : ℝ≥0) (flip : Bool) (c : BoundaryWord) : ℕ × ℕ × ℕ × ℕ × Bool :=
  if NearStructTop κ s flip c then
    (flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0,
      flowLineNR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0, cutCountL (nearDilWord s flip c),
      flowLineNR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 - 1, true)
  else
    (flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0,
      flowLineNR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0,
      flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 - 1,
      cutCountR (nearDilWord s flip c), false)

theorem measurable_nearDilWord_at (s : ℝ≥0) (flip : Bool) : Measurable fun c : BoundaryWord => nearDilWord s flip c :=
  (measurable_nearDilWord flip).comp (measurable_const.prodMk measurable_id)

theorem measurableSet_nearStructTop_at (κ : ℝ) (s : ℝ≥0) (flip : Bool) :
    MeasurableSet {c : BoundaryWord | NearStructTop κ s flip c} :=
  (measurable_const.prodMk measurable_id) (measurableSet_nearStructTop κ flip)

/-- **The near shape is measurable in the base word.** -/
theorem measurable_nearShapeM (κ : ℝ) (s : ℝ≥0) (flip : Bool) : Measurable (nearShapeM κ s flip) := by
  have hd := measurable_nearDilWord_at s flip
  have hNL : Measurable fun c : BoundaryWord =>
      flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 := FCDet.measurable_flowLineNL_zero.comp hd
  have hNR : Measurable fun c : BoundaryWord =>
      flowLineNR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 := FCDet.measurable_flowLineNR_zero.comp hd
  have hsub : ∀ {f : BoundaryWord → ℕ}, Measurable f → Measurable fun c => f c - 1 := fun hf =>
    (measurable_from_nat (f := fun n : ℕ => n - 1)).comp hf
  classical
  unfold nearShapeM
  refine Measurable.ite (measurableSet_nearStructTop_at κ s flip) ?_ ?_
  · exact hNL.prodMk (hNR.prodMk ((measurable_cutCountL.comp hd).prodMk ((hsub hNR).prodMk measurable_const)))
  · exact hNL.prodMk (hNR.prodMk ((hsub hNL).prodMk ((measurable_cutCountR.comp hd).prodMk measurable_const)))

/-- The padded left positions of the dilated base word. -/
theorem measurable_nearPosL (s : ℝ≥0) (flip : Bool) :
    Measurable fun c : BoundaryWord => padXL (nearDilWord s flip c) :=
  measurable_padXL.comp (measurable_nearDilWord_at s flip)

/-- The padded right positions of the dilated base word. -/
theorem measurable_nearPosR (s : ℝ≥0) (flip : Bool) :
    Measurable fun c : BoundaryWord => padXR (nearDilWord s flip c) :=
  measurable_padXR.comp (measurable_nearDilWord_at s flip)

/-- **The near shape after a measurable base-word reader** (e.g. GEOM2's word map of the stage record). -/
theorem measurable_nearShapeM_comp {Y : Type*} [MeasurableSpace Y] {β : Y → BoundaryWord} (hβ : Measurable β)
    (κ : ℝ) (s : ℝ≥0) (flip : Bool) : Measurable fun y => nearShapeM κ s flip (β y) :=
  (measurable_nearShapeM κ s flip).comp hβ

/-- **The padded positions after a measurable base-word reader.** -/
theorem measurable_nearPos_comp {Y : Type*} [MeasurableSpace Y] {β : Y → BoundaryWord} (hβ : Measurable β)
    (s : ℝ≥0) (flip : Bool) :
    Measurable (fun y => padXL (nearDilWord s flip (β y))) ∧ Measurable fun y => padXR (nearDilWord s flip (β y)) :=
  ⟨(measurable_nearPosL s flip).comp hβ, (measurable_nearPosR s flip).comp hβ⟩

end InteractingSLE.Theorem14.GW2Bh
