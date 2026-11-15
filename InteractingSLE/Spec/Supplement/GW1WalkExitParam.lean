/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitD4

/-!
# GW1: the exit and D.4 inputs are discharged

Theorem 1.3 supplies the regular pieces and the ambient height bounds. The finite-stage
record induction then proves the D.4 statement in both orientations. Together with the
proved exit classification, this closes the two walk parametrizations from the per-piece
statement, or from its existing clock-based provider.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish

theorem walkD4GeometryStatement_of_theorem13
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0}) :
    WalkD4GeometryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg right
  let spec := GW1Z.walkSpec b jumps right
  have hS := walkStageData_of_theorem13 hT13₀
    κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg right
  have hR := stagedPiecesRegular_of_regular hT13 hκ hb
    (hE spec
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right))
    (hreg spec)
  filter_upwards [hS, hR] with ω hs hr
  apply walk_recordGeometry hκ hb (fun j => E spec j ω) (fun j => hreg spec j ω) hs
  intro k c θ hl
  obtain ⟨hk, -, -⟩ := eq_launch_of_launches spec _ hl
  exact hr k θ _ c hk hl

/-- The per-piece statement now suffices: both local walk obligations have proofs. -/
theorem paramEveryRegStatements_of_pieceSimple
    (hS : GW1Z.GW1PieceSimpleStatement.{u})
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0}) :
    GW1X.GW1ParamEveryRegStatement.{u} ∧ WalkProper.LeftWalkParamEveryRegStatement.{u} :=
  paramEveryRegStatements_of_pieceSimple_and_d4 hS hT13
    (walkExitClassificationStatement_of_theorem13 hT13₀)
    (walkD4GeometryStatement_of_theorem13 hT13 hT13₀)

/-- Clock-based assembly with no remaining tip, clearance, completion, exit, or D.4 input. -/
theorem paramEveryRegStatements_of_walkClock
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hClock : GW1Z.WalkLaunchClockStatement.{u}) :
    GW1X.GW1ParamEveryRegStatement.{u} ∧ WalkProper.LeftWalkParamEveryRegStatement.{u} :=
  paramEveryRegStatements_of_pieceSimple
    (GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 hT13 hT13₀ hClock) hT13 hT13₀

end InteractingSLE.Theorem14.GW1WalkExit
