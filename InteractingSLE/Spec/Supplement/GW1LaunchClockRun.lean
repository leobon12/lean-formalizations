/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LaunchClockStep

/-! # GW1: launch parity, completed runs, and the predecessor of a restart -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1LaunchClock

open Exist.Staged Exist.StagedLaw GW1WalkFinish GW1WalkExit
open PiecewiseConstantBoundaryData (jumpSet)

/-- An index that cannot launch imposes no clock condition. -/
theorem isLaunchClock_of_noLaunch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hn : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none) :
    GW1Z.IsLaunchClock κ b jumps P h W spec E k (fun _ _ => 0) (fun _ => ⊤) (fun _ => id) := by
  have hf (ω : Ω) (c : Chart) (θ : ℝ)
      (hl : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k =
        some (c, θ)) : False := by
    rw [hn ω] at hl
    cases hl
  exact ⟨fun _ => measurable_const,
    Eventually.of_forall fun ω c θ hl => False.elim (hf ω c θ hl),
    Eventually.of_forall fun ω c θ hl => False.elim (hf ω c θ hl)⟩

/-- A later launch has a preceding launch. This uses the proved ready-state
induction; a done state stays done through both instructions of a round. -/
theorem previous_launch_of_next {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hreg : ∀ k, IsRegularDriver (D k))
    (hS : WalkStageData κ b jumps θ right D)
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    {n : ℕ} (hn : n < (jumpSet b jumps).card)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n + 1)).2.2.2.1
      (2 * n) ≠ none := by
  let spec := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps spec D
  rcases walk_prefix_geometry hκ hb D hreg hS hP n (by omega) with hd | ⟨hr, -, -⟩
  · have h1 : R (2 * n + 1) = R (2 * n) := done_run_succ spec D hd
    have h2 : R (2 * n + 1 + 1) = R (2 * n + 1) :=
      done_run_succ spec D (by change stStatus (R (2 * n + 1)) = stDone; rw [h1]; exact hd)
    have hdone : stStatus (R (2 * (n + 1))) = stDone := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, h2, h1]
      exact hd
    exact False.elim ((hS (2 * (n + 1)) hl).2.1.not_done hdone)
  · exact (launch_at_even_of_launchReady D (by omega) hr).2

end InteractingSLE.Theorem14.GW1LaunchClock
