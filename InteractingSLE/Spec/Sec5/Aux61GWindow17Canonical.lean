/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Stable
import InteractingSLE.Spec.Sec5.Aux61SlitWZRead
import InteractingSLE.Spec.Sec5.Aux61GWordWindows

/-! # One certified chart for each retained rational time

Choose the normalized chart using a fixed auxiliary word and window.
The resulting chart depends only on the source and retained time. Later
window refinements therefore preserve its complete R1 certificate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61GR1F Aux61FibData LawUnique
universe u

/-- Fixed auxiliary geometry used only to choose the chart model. -/
def baseGeometry : WindowGeometry where
  V := ball 0 1
  open_window := isOpen_ball
  zero_window := mem_ball_self (by norm_num)
  O₀ := univ
  open_real := isOpen_univ
  buffer := ball 0 2
  open_buffer := isOpen_ball
  compact_buffer := by
    rw [closure_ball (0 : ℂ) (by norm_num : (2 : ℝ) ≠ 0)]
    exact isCompact_closedBall (0 : ℂ) 2
  real_buffer := fun _ _ _ => mem_univ _
  window_sub := ball_subset_ball (by norm_num)

/-- A fixed admissible reference word, independent of retained records. -/
def baseWord (S : SourceSetting.{u}) : ReferenceWord S.κ :=
  positiveReference (a := 1) (b := 2) (v := sleLambda S.κ - Real.pi * QuantumZipper.chiC S.κ)
    S.κ_pos S.κ_lt_four.le (by norm_num) (by norm_num) le_rfl

/-- A single-index model at a prescribed retained time. Its word and
window are auxiliary; only the complete chart certificate is reused. -/
def baseChoices (S : SourceSetting.{u}) (q : ℚ) : RestartChoices S :=
  Aux61GChoice15.windowChoices S (fun _ : Unit => q) (fun _ => univ)
    (fun _ => baseWord S) (fun _ => baseGeometry)

/-- The good index of the fixed model at a regular retained time. -/
def baseIndex (S : SourceSetting.{u}) (t : GoodTime S) : (baseChoices S t.1).Idx :=
  ⟨(), t.2⟩

/-- A fully certified retained-record chart with no window or selection
parameter. This definition does not use the weak chart selector. -/
def recordChart (S : SourceSetting.{u}) (t : GoodTime S) :
    SourceRecord S.nL S.nR → Chart :=
  Aux61SlitWX.chart (baseChoices S t.1).toR1Restart (baseChoices S t.1).hasChart (baseIndex S t)

/-- The canonical chart has the full R1 certificate, including its actual
target, current access, infinity limit and inherited physical lift. -/
theorem recordChart_spec (S : SourceSetting.{u}) (t : GoodTime S) :
    Aux61SlitWX.ChartFacts (baseChoices S t.1).toR1Restart (baseIndex S t)
      (Aux61SlitWX.base (baseChoices S t.1).toR1Restart (baseChoices S t.1).hasChart (baseIndex S t))
      (recordChart S t) :=
  Aux61SlitWX.chart_spec _ _ _

/-- Changing a window or a selected-record restriction leaves the
time-indexed normalized chart exactly the same. -/
theorem recordChart_eq_of_time_eq (S : SourceSetting.{u}) (t r : GoodTime S)
    (h : t.1 = r.1) : recordChart S t = recordChart S r :=
  congrArg (recordChart S) (Subtype.ext h)

end InteractingSLE.Sec5.Aux61GWindow17
