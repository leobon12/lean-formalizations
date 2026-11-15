/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Match
import InteractingSLE.Spec.Sec5.Aux61SlitWACRestrict
import InteractingSLE.Spec.Sec5.Aux61WndCapNorm

/-! # Bounded real neighborhoods and the exact normalized time chart

The real comparison set is a bounded open interval containing the real
trace of the closed buffer. The full normalized selector agrees with the
landed time-indexed selector, including after record restrictions.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow18
open Aux61SlitW Aux61R1C Aux61GR1F Aux61GWord Aux61FibData LawUnique
universe u

/-- A positive radius containing the whole closed buffer. -/
def realRadius (j : SeedWindowIndex) : ℝ :=
  Classical.choose (j.2.2.2.2.isBounded.subset_ball_lt 0 (0 : ℂ))

theorem realRadius_pos (j : SeedWindowIndex) : 0 < realRadius j :=
  (Classical.choose_spec (j.2.2.2.2.isBounded.subset_ball_lt 0 (0 : ℂ))).1

theorem closure_buffer_subset_ball (j : SeedWindowIndex) :
    closure (outerBuffer j) ⊆ ball (0 : ℂ) (realRadius j) :=
  (Classical.choose_spec (j.2.2.2.2.isBounded.subset_ball_lt 0 (0 : ℂ))).2

/-- The fixed buffered window with a bounded real comparison neighborhood. -/
def windowGeometry (j : SeedWindowIndex) : WindowGeometry where
  V := bufferedWindow j
  open_window := Aux61GInst.isOpen_seedExitWindow (isOpen_basisBuffer _) _
  zero_window := j.2.2.1
  O₀ := Ioo (-realRadius j) (realRadius j)
  open_real := isOpen_Ioo
  buffer := outerBuffer j
  open_buffer := isOpen_basisBuffer _
  compact_buffer := j.2.2.2.2
  real_buffer := by
    intro z hz _
    have hn : ‖z‖ < realRadius j := by
      simpa only [mem_ball, dist_zero_right] using closure_buffer_subset_ball j hz
    exact abs_lt.mp ((Complex.abs_re_le_norm z).trans_lt hn)
  window_sub := fun _ hz => j.2.2.2.1 (subset_closure hz.1)

theorem isBounded_real_window (j : SeedWindowIndex) :
    Bornology.IsBounded (windowGeometry j).O₀ := isBounded_Ioo _ _

theorem zero_mem_real_window (j : SeedWindowIndex) : (0 : ℝ) ∈ (windowGeometry j).O₀ :=
  ⟨neg_neg_of_pos (realRadius_pos j), realRadius_pos j⟩

/-- The complete normalized selector, rather than the weaker chart,
is exactly the landed chart chosen once at the retained rational time. -/
theorem normalized_chart_eq_recordChart {S : SourceSetting.{u}} (C : RestartChoices S) (i : C.Idx) :
    Aux61SlitWX.chart C.toR1Restart C.hasChart i =
      Aux61GWindow17.recordChart S ⟨C.q i.1, i.2⟩ :=
  Aux61SlitWAC.normalized_chart_eq_of_time_eq C
    (Aux61GWindow17.baseChoices S (C.q i.1)) i
    (Aux61GWindow17.baseIndex S ⟨C.q i.1, i.2⟩) rfl

end InteractingSLE.Sec5.Aux61GWindow18
