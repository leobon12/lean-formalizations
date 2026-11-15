/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2SidePhys
import InteractingSLE.Spec.Supplement.SBTail2ReadoutLaunch

/-! # SB4 launch data with the forbidden side's measurability discharged

Only the actual conditional-tail construction remains an additional input.
The measurable path, exact rational incidence, continuity and side openness
are supplied from the original driver measurability and R51 hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Side

open Leaf

/-- The launch parametrization and exact rational-incidence events for the
actual forbidden right side, with no side-version hypothesis. -/
theorem exists_rightSide_launch_param {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {specL : ExplSpec} (hELm : ∀ j, Measurable (EL j))
    (hRL : StagedPiecesRegular κ b jumps P specL EL)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) :
    ∃ a : Ω → ℝ≥0 → ℂ,
      (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈
        rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω))}) ∧
      ∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
        Continuous (a ω) ∧
          IsOpen (rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω))) ∧
          schedulePiece κ b jumps x l (fun j => E j ω) k = range (a ω) := by
  exact Readout.exists_rightSide_launch_param_of_version hb hEm hR hRL hk
    (exists_measurable_physSet_side_versions hb specL hELm hRL).1

/-- Conditional on the actual relative-tail construction, all other launch
data are now proved. `hcanon` retains the genuine geometric/conditional-law
obligation; this helper is distinct from either assigned SB4 leaf. -/
theorem hasScheduleLaunchTail_of_canonical_physSet
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E)
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {specL : ExplSpec} (hELm : ∀ j, Measurable (EL j))
    (hRL : StagedPiecesRegular κ b jumps P specL EL)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) {original : Set ℝ}
    (hcanon : ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
        ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
          HasActualTailSewing (schedulePiece κ b jumps x l (fun j => E j ω) k)
            (rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω)))) ∨
      Canon.CanonicalLaunchData κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E k l original
        (fun ω => schedulePiece κ b jumps x l (fun j => E j ω) k)
        (fun ω => rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω))) ω₀ c) :
    HasScheduleLaunchTail κ b jumps P h x l E k original
      (fun ω => schedulePiece κ b jumps x l (fun j => E j ω) k)
      (fun ω => rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω))) := by
  exact Canon.hasScheduleLaunchTail_of_canonical hκ
    (exists_rightSide_launch_param hb hE.1 hR hELm hRL hk) hcanon

end InteractingSLE.Theorem14.SB.Side
