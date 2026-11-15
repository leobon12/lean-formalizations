/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Geometry
import InteractingSLE.Spec.Sec5.Aux61GChoice15History

/-! # A fixed countable family with all nonzero real landing intervals

Both the reference interval and the buffered continuation window are
indexed before seeing a continuation. The canonical retained chart is
independent of these indices.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61GR1F Aux61GWord Aux61GChoice15 LawUnique
universe u

/-- Rational intervals entirely on one side of the seed. -/
abbrev ReferenceInterval := {p : ℚ × ℚ //
  (0 < (p.1 : ℝ) ∧ (p.1 : ℝ) < p.2) ∨ ((p.1 : ℝ) < p.2 ∧ (p.2 : ℝ) < 0)}

/-- The countable interval family contains every nonzero real point. -/
theorem exists_referenceInterval {y : ℝ} (hy : y ≠ 0) :
    ∃ I : ReferenceInterval, y ∈ Ioo (I.1.1 : ℝ) (I.1.2 : ℝ) := by
  rcases lt_or_gt_of_ne hy with hy | hy
  · obtain ⟨a, ha⟩ := exists_rat_lt y
    obtain ⟨b, hyb, hb⟩ := exists_rat_btwn hy
    exact ⟨⟨(a, b), Or.inr ⟨ha.trans hyb, hb⟩⟩, ha, hyb⟩
  · obtain ⟨a, ha, hay⟩ := exists_rat_btwn hy
    obtain ⟨b, hb⟩ := exists_rat_gt y
    exact ⟨⟨(a, b), Or.inl ⟨ha, hay.trans hb⟩⟩, hay, hb⟩

/-- An admissible reference for each signed interval. Height agreement
with the physical conditional mean is a separate comparison question. -/
def intervalWord (S : SourceSetting.{u}) (I : ReferenceInterval) : ReferenceWord S.κ :=
  if h : 0 < (I.1.1 : ℝ) ∧ (I.1.1 : ℝ) < I.1.2 then
    positiveReference (v := sleLambda S.κ - Real.pi * chiC S.κ)
      S.κ_pos S.κ_lt_four.le h.1 h.2 le_rfl
  else
    negativeReference (v := sleLambda S.κ + Real.pi * chiC S.κ + 1)
      S.κ_pos S.κ_lt_four (I.2.resolve_left h).1 (I.2.resolve_left h).2
      (lt_add_one _)

theorem intervalWord_left (S : SourceSetting.{u}) (I : ReferenceInterval) :
    (intervalWord S I).left = (I.1.1 : ℝ) := by
  unfold intervalWord
  split <;> rfl

theorem intervalWord_right (S : SourceSetting.{u}) (I : ReferenceInterval) :
    (intervalWord S I).right = (I.1.2 : ℝ) := by
  unfold intervalWord
  split <;> rfl

/-- The actual fixed countable buffered window, with no supplied geometry. -/
def windowGeometry (j : SeedWindowIndex) : WindowGeometry where
  V := bufferedWindow j
  open_window := Aux61GInst.isOpen_seedExitWindow (isOpen_basisBuffer _) _
  zero_window := j.2.2.1
  O₀ := univ
  open_real := isOpen_univ
  buffer := outerBuffer j
  open_buffer := isOpen_basisBuffer _
  compact_buffer := j.2.2.2.2
  real_buffer := fun _ _ _ => mem_univ _
  window_sub := fun _ hz => j.2.2.2.1 (subset_closure hz.1)

/-- All signed rational reference intervals and all countable windows,
at the source's original retained time. -/
def captureChoices (S : SourceSetting.{u}) : RestartChoices S :=
  fixedTimeChoices S (fun p : ReferenceInterval × SeedWindowIndex => intervalWord S p.1)
    (fun p => windowGeometry p.2)

theorem captureChoices_selected_measurable (S : SourceSetting.{u}) :
    ∀ i, MeasurableSet ((captureChoices S).selected i) := fun _ => MeasurableSet.univ

end InteractingSLE.Sec5.Aux61GWindow17
