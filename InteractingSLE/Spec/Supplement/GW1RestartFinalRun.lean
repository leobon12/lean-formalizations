/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartFinalTrace

/-!
# Terminal readers for the actual staged charts

The range invariant includes every completed ordinary piece and every retained
connector. No positive separation from the ordinary piece's endpoint is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.GW1RestartFinal

open Exist.Staged Exist.StagedLaw

/-- All regular staged charts are conformal and their finite boundary values
are in the full recorded past or outside the physical upper half-plane. -/
theorem chart_boundaryRange_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ,
      (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    (stChart (ExplState.run κ b jumps spec D n)).IsConformal ∧
      HasBoundaryRange (stChart (ExplState.run κ b jumps spec D n))
        (SB.prefixPhysSet κ b jumps spec D n) := by
  induction n with
  | zero => exact ⟨Chart.isConformal_id.recenter spec.1, hasBoundaryRange_recenter_id _ _⟩
  | succ n ih =>
    have ih' := ih.2.mono
      (GW1Z.prefixPhysSet_subset_succ (κ := κ) (b := b) (jumps := jumps) spec D n)
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch
        (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [show stChart (ExplState.run κ b jumps spec D (n + 1)) = _ from ha]
      exact ⟨ih.1.recenter a, ih'.recenter a⟩
    · have hr := hreg n c θ hl
      have hsub := GW1Z.tipSet_subset_prefixPhysSet_succ
        (κ := κ) (b := b) (jumps := jumps) spec D hl
      obtain ⟨-, he, hc⟩ := eq_launch_of_launches
        (κ := κ) (b := b) (jumps := jumps) spec D hl
      rcases eq_or_ne (min (instrTime spec n) (D n).2) ⊤ with htop | htop
      · change (ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.IsConformal ∧
          HasBoundaryRange (ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1 _
        rw [he, GW1P.chart_launch_of_top _ _ _ _ _ htop]
        exact ⟨ih.1, ih'⟩
      · change (ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.IsConformal ∧
          HasBoundaryRange (ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1 _
        rw [he, chart_launch _ _ _ _ _ htop]
        rw [hc] at hsub
        obtain ⟨hU, hU0⟩ := hr.continuous_stoppedReal
        exact ⟨ih.1.loewner hU hU0 (NNReal.coe_nonneg _),
          ih'.loewner_stopped hr htop hsub⟩

/-- Each regular run chart admits a Borel reader, including its true finite
boundary limits, relative to the entire recorded past. -/
theorem exists_terminalChartReader_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ,
      (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    ∃ read : ℂ → ℂ,
      GW1RestartLaw.IsTerminalChartReader (stChart (ExplState.run κ b jumps spec D n))
        (SB.prefixPhysSet κ b jumps spec D n) read ∧
      ∀ p ∈ Hbar, Tendsto (stChart (ExplState.run κ b jumps spec D n)).2.1
        (𝓝[H] p) (𝓝 (read p)) := by
  obtain ⟨hc, hr⟩ := chart_boundaryRange_run spec D hreg n
  exact hr.exists_terminalChartReader hc

/-- Piece regularity supplies a reader at every actual staged time, including
the time immediately after a finite ordinary piece. The reader is pathwise;
joint measurable selection of readers is not asserted here. -/
theorem ae_exists_terminalChartReader_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : StagedPiecesRegular κ b jumps P spec E) :
    ∀ᵐ ω ∂P, ∀ n, ∃ read : ℂ → ℂ,
      GW1RestartLaw.IsTerminalChartReader
        (stChart (ExplState.run κ b jumps spec (fun j => E j ω) n))
        (SB.prefixPhysSet κ b jumps spec (fun j => E j ω) n) read ∧
      ∀ p ∈ Hbar, Tendsto
        (stChart (ExplState.run κ b jumps spec (fun j => E j ω) n)).2.1
        (𝓝[H] p) (𝓝 (read p)) := by
  filter_upwards [hreg] with ω hr
  intro n
  apply exists_terminalChartReader_run spec (fun j => E j ω) _ n
  intro k c θ hl
  obtain ⟨hk, -, -⟩ := eq_launch_of_launches spec (fun j => E j ω) hl
  exact hr k θ (instrTime spec k) c hk hl

end InteractingSLE.Theorem14.GW1RestartFinal
