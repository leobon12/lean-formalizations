/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwFinal
import InteractingSLE.Spec.Supplement.GW1Base

/-!
# Staged histories only see the data through its one-sided limits and genuine jumps

Packet PROVE-T14-SB2LOW. The frozen run `ExplState.run κ b jumps` uses the boundary data only through its one-sided
limits (the seed heights, `ExplState.heights`) and its genuine jumps (the restart marks of `ExplState.contStep`). So two
data with the same one-sided limits and genuine jumps run every program identically, and every predicate built from the
run — the retained past `pastSigma`, `IsStagedHistory`, `StagedPiecesRegular`, the prefix `prefixPhysSet`, GW1's walk
`boundaryWalkSpec` — is the same for both (`run_congr_data` and its corollaries). SB2(2) at the first launch uses this
for the recentred data `affData 1 m b'` of the launch witness, which agree with `b` off a finite set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lh

open Exist Exist.StagedLaw Exist.Staged Restart
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

variable {κ : ℝ} {b b' : ℝ → ℝ} {J J' : Finset ℝ}

/-- **The run depends on the data only through its one-sided limits and genuine jumps.** -/
theorem run_congr_data (hL : leftLim b = leftLim b') (hR : rightLim b = rightLim b') (hS : jumpSet b J = jumpSet b' J')
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    ExplState.run κ b J spec D n = ExplState.run κ b' J' spec D n := by
  have hH : ExplState.heights κ b = ExplState.heights κ b' := by
    funext s
    unfold ExplState.heights
    rw [hL, hR]
  have hF : ExplState.flowStep κ b = ExplState.flowStep κ b' := by
    funext gw2 s k d θ t
    unfold ExplState.flowStep
    rw [hH]
  have hC : ExplState.contStep κ b J = ExplState.contStep κ b' J' := by
    funext s v p
    unfold ExplState.contStep
    rw [hL, hR, hS]
  have hstep : ExplState.step κ b J = ExplState.step κ b' J' := by
    funext gw2 d s ik
    unfold ExplState.step
    rw [hF, hC]
  unfold ExplState.run
  rw [hstep]

/-- GW1's walk program depends on the data only through its genuine jumps. -/
theorem boundaryWalkSpec_congr (hS : jumpSet b J = jumpSet b' J') (θ : ℝ) (right : Bool) :
    boundaryWalkSpec b J θ right = boundaryWalkSpec b' J' θ right := by
  unfold boundaryWalkSpec
  rw [hS]

section Hist

variable (hrun : ∀ (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ),
  ExplState.run κ b J spec D n = ExplState.run κ b' J' spec D n)
include hrun

theorem run_eq_data : ExplState.run κ b J = ExplState.run κ b' J' :=
  funext fun spec => funext fun D => funext fun n => hrun spec D n

theorem pastSigma_congr_data {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    pastSigma κ b J spec E k = pastSigma κ b' J' spec E k := by
  unfold pastSigma
  rw [run_eq_data hrun]

theorem isStagedHistory_congr_data {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    IsStagedHistory κ b J P h spec E ↔ IsStagedHistory κ b' J' P h spec E := by
  unfold IsStagedHistory pastSigma
  rw [run_eq_data hrun]

theorem stagedPiecesRegular_congr_data {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    StagedPiecesRegular κ b J P spec E ↔ StagedPiecesRegular κ b' J' P spec E := by
  unfold StagedPiecesRegular
  rw [run_eq_data hrun]

theorem prefixPhysSet_congr_data (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    SB.prefixPhysSet κ b J spec D n = SB.prefixPhysSet κ b' J' spec D n := by
  unfold SB.prefixPhysSet
  rw [run_eq_data hrun]

end Hist

end InteractingSLE.Theorem14.SB.Lh
