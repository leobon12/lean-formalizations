/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1PatchStair
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Height

/-!
# A.1's finite patches for A22's seeded height field

Packet PROVE-A1-PATCH (R80). Source: Astra, *Follow-up 4* §2.5 items 1–4 (`ig1_followup4_audited.txt` L733–L796): the
normalized seeded density `M(s, t)` with continuous entrance values, its two coordinate martingales from time zero,
and the staircase patches built from them.

PROVE-ZHAN-GT4-A22's explicit field `seedHeightField d (x, y) s t` (own time `s` of curve `1`, frozen height `t` of
curve `2`, record `d t (x, y)` at that height) is the candidate two-time field of `IsRectField`. Here its axes and
positivity are recorded and its column hypothesis is identified with A22's one-height seeded density process:

* `seedHeightField_col_eq`: with the second path `y` fixed, `s ↦ N((x, y), s ∧ S₁ x, S₂ y)` is literally
  `seedDensityProcess (fun x => d (S₂ y) (x, y)) S₁` (the process A22's `seeded_source_calculus_right` makes a
  martingale);
* **`isRectField_seedHeightField`**: a protected rectangle of the seeded field from A22's one-height column
  martingales, the bounds (D9), and the row (t-view) martingales.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Patch

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {n : ℕ}

omit mX mY in
/-- **The column process of the seeded field is A22's one-height density process** of the record at the frozen
height `S₂ y`. -/
theorem seedHeightField_col_eq (d : ℝ → X × Y → SeedData n) (S₁ : X → ℝ≥0) (S₂ : Y → ℝ≥0) (y : Y) :
    (fun (s : ℝ≥0) x => seedHeightField d (x, y) (min (s : ℝ) (S₁ x)) (S₂ y)) =
      seedDensityProcess (fun x => d (S₂ y) (x, y)) S₁ := by
  funext s x
  simp only [seedHeightField, seedDensityProcess]

/-- **A protected rectangle of the seeded height field**: bounded stopping times, the two-sided bound (D9) on the
rectangle, A22's one-height column martingales (`seedDensityProcess` of the record at the exit height `S₂ y`, with the
second path fixed), and the row martingales (the t-view: with the first path fixed, `t ↦ N((x, y), a, t ∧ S₂ y)` for
`a ≤ S₁ x`). -/
theorem isRectField_seedHeightField {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX}
    {𝓕₂ : Filtration ℝ≥0 mY} {d : ℝ → X × Y → SeedData n} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0}
    (h₁ : IsStoppingTime 𝓕₁ fun x => (S₁ x : WithTop ℝ≥0)) (h₂ : IsStoppingTime 𝓕₂ fun y => (S₂ y : WithTop ℝ≥0))
    (hU : ∃ U : ℝ≥0, (∀ x, S₁ x ≤ U) ∧ ∀ y, S₂ y ≤ U)
    (hb : ∃ c C : ℝ, 0 < c ∧ ∀ x y (s t : ℝ), 0 ≤ s → s ≤ S₁ x → 0 ≤ t → t ≤ S₂ y →
      c ≤ seedHeightField d (x, y) s t ∧ seedHeightField d (x, y) s t ≤ C)
    (hcol : ∀ y, Martingale (seedDensityProcess (fun x => d (S₂ y) (x, y)) S₁) 𝓕₁ P₁)
    (hcolc : ∀ x y, Continuous fun s => seedDensityProcess (fun x => d (S₂ y) (x, y)) S₁ s x)
    (hrow : ∀ x (a : ℝ), 0 ≤ a → a ≤ S₁ x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField d (x, y) a (min (t : ℝ) (S₂ y))) 𝓕₂ P₂)
    (hrowc : ∀ x y (a : ℝ), 0 ≤ a → a ≤ S₁ x →
      Continuous fun t : ℝ≥0 => seedHeightField d (x, y) a (min (t : ℝ) (S₂ y))) :
    IsRectField P₁ P₂ 𝓕₁ 𝓕₂ S₁ S₂ (seedHeightField d) where
  stop₁ := h₁
  stop₂ := h₂
  bdd := hU
  bound := hb
  col y := by rw [seedHeightField_col_eq]; exact hcol y
  col_cont x y := by
    have e := congrFun (seedHeightField_col_eq d S₁ S₂ y)
    simpa only [funext fun s => congrFun (e s) x] using hcolc x y
  row := hrow
  row_cont := hrowc

omit mX mY in
/-- The seeded height field is positive and has axis value one in its own time (`seedHeightField_pos`,
`seedHeightField_zero_left`); its other axis is one when the zero-height record has constant normalized logarithm
(`seedHeightField_zero_right`, the identity chart: `seedHeightField_axes_of_identity`). -/
theorem seedHeightField_field_props {d : ℝ → X × Y → SeedData n}
    (h0 : ∀ ω s, (d 0 ω).normEll s = (d 0 ω).normEll 0) :
    (∀ ω s t, 0 < seedHeightField d ω s t) ∧ (∀ ω t, seedHeightField d ω 0 t = 1) ∧
      ∀ ω s, seedHeightField d ω s 0 = 1 :=
  ⟨seedHeightField_pos d, seedHeightField_zero_left d, seedHeightField_zero_right h0⟩

end InteractingSLE.ZhanGT4.A1Patch
