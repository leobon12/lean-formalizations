/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitRun

/-!
# GW1: the exit-classification statement is discharged

Theorem 1.3 supplies GW0 and hence the ambient bounds. The landed active-word induction
gives the word and ready state at each launch. The classified-exit laws and the restart
admissibility induction then cover every live ordinary instruction, in both orientations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish

theorem walkExitClassificationStatement_of_theorem13 (hT13₀ : Theorem13Statement.{0}) :
    WalkExitClassificationStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg right
  have hamb := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀)
    hκ hκ4 hb hh hcf hζ'
  cases right
  · let spec := GW1Z.walkSpec b jumps false
    have hS := hE spec
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc false) false)
    have hA : ∀ᵐ ω ∂P, ∀ k,
        (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)).2.2.2.1 k ≠ none →
        ClassifiedExit κ b false (ExplState.run κ b jumps spec (fun j => E spec j ω) k)
          (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)) := by
      refine ae_all_iff.2 fun k => ?_
      obtain ⟨β, Y, hW, hI⟩ := GW1W.exists_witness_left hκ hb hh hS (hreg spec) hamb.2 k
      exact ae_classifiedExit_left hκ hb hh hS (hreg spec) hW hI
    filter_upwards [hA] with ω hω
    exact forwardExit_at_rounds_of_classifiedExits hκ hb _ hω
  · let spec := GW1Z.walkSpec b jumps true
    have hS := hE spec
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc true) true)
    have hA : ∀ᵐ ω ∂P, ∀ k,
        (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)).2.2.2.1 k ≠ none →
        ClassifiedExit κ b true (ExplState.run κ b jumps spec (fun j => E spec j ω) k)
          (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)) := by
      refine ae_all_iff.2 fun k => ?_
      obtain ⟨β, Y, hW, hI⟩ := GW1W.exists_witness_right hκ hb hh hS (hreg spec) hamb.1 k
      exact ae_classifiedExit_right hκ hb hh hS (hreg spec) hW
        (hI.mono fun ω hω hl => ⟨(hω hl).1, (hω hl).2.1⟩)
    filter_upwards [hA] with ω hω
    exact forwardExit_at_rounds_of_classifiedExits hκ hb _ hω

/-- The former completion obligation now follows without a new geometric hypothesis. -/
theorem walkCompletionStatement_of_theorem13 (hT13₀ : Theorem13Statement.{0}) :
    GW1ParamEvery.WalkCompletionStatement.{u} :=
  walkCompletionStatement_of_exitClassification
    (walkExitClassificationStatement_of_theorem13 hT13₀)

/-- The local exit statement is no longer an input to the two parametrizations. -/
theorem paramEveryRegStatements_of_walkClock_and_geometry
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hClock : GW1Z.WalkLaunchClockStatement.{u}) (hD4 : WalkD4GeometryStatement.{u}) :
    GW1X.GW1ParamEveryRegStatement.{u} ∧ WalkProper.LeftWalkParamEveryRegStatement.{u} :=
  paramEveryRegStatements_of_walkClock_and_d4 hGB6 hT13 hT13₀ hClock
    (walkExitClassificationStatement_of_theorem13 hT13₀) hD4

end InteractingSLE.Theorem14.GW1WalkExit
