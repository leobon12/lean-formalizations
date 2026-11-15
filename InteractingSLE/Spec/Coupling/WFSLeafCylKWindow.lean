/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafCloseJAssembly
import Mathlib.Data.Nat.Pairing

/-!
# Finite continuous windows of a full killed history

A window retains the lifetime and the first finitely many dyadic samples in
Cantor pairing order. Filling the remaining samples with zero gives continuous
maps whose values converge to every history in its product topology.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique

/-- A lifetime and finitely many driving-state coordinates. -/
abbrev HistoryWindow (nL nR n : ℕ) : Type :=
  ℝ≥0∞ × (Fin n → DrivingValue nL nR)

/-- Retain the lifetime and the first `n` dyadic samples in Cantor pairing order. -/
def historyWindow {nL nR : ℕ} (n : ℕ) (γ : HistorySpace nL nR) : HistoryWindow nL nR n :=
  (γ.1, fun i => γ.2 (Nat.unpair i))

/-- Fill a finite window by zero at all unrecorded sample coordinates. -/
def historyFill {nL nR n : ℕ} (z : HistoryWindow nL nR n) : HistorySpace nL nR :=
  (z.1, fun p => if h : Nat.pair p.1 p.2 < n then z.2 ⟨Nat.pair p.1 p.2, h⟩ else 0)

/-- Finite history projection is continuous. -/
theorem continuous_historyWindow {nL nR : ℕ} (n : ℕ) :
    Continuous (historyWindow (nL := nL) (nR := nR) n) :=
  continuous_fst.prodMk
    (continuous_pi fun i => (continuous_apply (Nat.unpair i)).comp continuous_snd)

/-- Finite history projection is Borel. -/
theorem measurable_historyWindow {nL nR : ℕ} (n : ℕ) :
    Measurable (historyWindow (nL := nL) (nR := nR) n) :=
  (continuous_historyWindow n).measurable

/-- Filling the missing coordinates with zero is continuous. -/
theorem continuous_historyFill {nL nR n : ℕ} :
    Continuous (historyFill (nL := nL) (nR := nR) (n := n)) := by
  apply Continuous.prodMk continuous_fst
  apply continuous_pi
  intro p
  by_cases h : Nat.pair p.1 p.2 < n
  · simpa only [historyFill, h, ↓reduceDIte, Function.comp_def] using
      ((continuous_apply (⟨Nat.pair p.1 p.2, h⟩ : Fin n)).comp
        (continuous_snd : Continuous (Prod.snd : HistoryWindow nL nR n → _)))
  · simpa only [historyFill, h, ↓reduceDIte, Function.comp_def] using
      (continuous_const : Continuous fun _ : HistoryWindow nL nR n => (0 : DrivingValue nL nR))

/-- Filling increasingly long windows converges to the full history.
The lifetime coordinate is retained at every stage. -/
theorem tendsto_historyFill_window {nL nR : ℕ} (γ : HistorySpace nL nR) :
    Tendsto (fun n => historyFill (historyWindow n γ)) atTop (𝓝 γ) := by
  apply Tendsto.prodMk_nhds tendsto_const_nhds
  apply tendsto_pi_nhds.2
  intro p
  have he : (fun n => (historyFill (historyWindow n γ)).2 p) =ᶠ[atTop]
      fun _ => γ.2 p := by
    filter_upwards [eventually_gt_atTop (Nat.pair p.1 p.2)] with n hn
    simp only [historyFill, hn, ↓reduceDIte, historyWindow, Nat.unpair_pair]
  exact tendsto_const_nhds.congr' he.symm

end InteractingSLE.WFS
