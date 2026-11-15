/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2PointStep

/-!
# Finite SB4 avoidance from positive-duration conditional tail sewing

The named open input requires actual tail sewing only when the next stopped
duration is almost surely positive under its retained conditional law.
The zero-stop case and the finite induction are proved without that input.
This does not provide either assigned SB4 launch-tail leaf.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Retain

open Leaf GW2Schedule

/-- The remaining geometric input for schedule avoidance. It is a named
hypothesis, not an asserted property of staged histories. In particular it
retains the original next piece, forbidden set and conditional past. -/
def SchedulePositiveTailSewing {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (S : Ω → Set ℂ) : Prop :=
  ∀ k < (scheduleProgram 0 l).length,
    (∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅) →
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      (∀ᵐ ω ∂(condExpKernel P
        (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ (E ⟨x, true, scheduleProgram 0 l⟩) k) ω₀),
        0 < min (schedDelta 0 l k) (E ⟨x, true, scheduleProgram 0 l⟩ k ω).2) →
      ∀ᵐ ω ∂(condExpKernel P
        (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ (E ⟨x, true, scheduleProgram 0 l⟩) k) ω₀),
        ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ (E ⟨x, true, scheduleProgram 0 l⟩) k →
          HasActualTailSewing
            (schedulePiece κ b jumps x l (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) (S ω)

/-- The open positive-duration geometry implies the original SB4 step
avoidance predicate; zero-stop geometry and measurability are discharged. -/
theorem scheduleStepAvoidance_of_positive_tail
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ (E ⟨x, true, scheduleProgram 0 l⟩))
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ (E ⟨x, true, scheduleProgram 0 l⟩))
    {specL : ExplSpec} {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hELm : ∀ j, Measurable (EL j))
    (hRL : StagedPiecesRegular κ b jumps P specL EL)
    (hpositive : SchedulePositiveTailSewing κ b jumps P E x l
      (fun ω => rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω)))) :
    ScheduleStepAvoidance κ b jumps P E x l
      (fun ω => rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω))) := by
  intro k hk hprev
  exact ae_schedulePiece_avoids_of_positive_tail hκ hb hE hR hELm hRL hk hprev
    (hpositive k hk hprev)

/-- Conditional on the named positive-duration sewing input, every finite
available schedule history avoids the actual physical right side, with all
old pieces and finite terminal endpoints retained. -/
theorem schedule_avoids_of_positive_tail
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ (E ⟨x, true, scheduleProgram 0 l⟩))
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ (E ⟨x, true, scheduleProgram 0 l⟩))
    {specL : ExplSpec} {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hELm : ∀ j, Measurable (EL j))
    (hRL : StagedPiecesRegular κ b jumps P specL EL)
    (hroot : ∀ᵐ ω ∂P, (x : ℂ) ∉ rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω)))
    (hpositive : SchedulePositiveTailSewing κ b jumps P E x l
      (fun ω => rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω)))) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) ∩
        rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω)) = ∅ := by
  exact schedule_avoids_of_step hroot
    (scheduleStepAvoidance_of_positive_tail hκ hb hE hR hELm hRL hpositive)

end InteractingSLE.Theorem14.SB.Retain
