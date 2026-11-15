/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkFinishTip
import InteractingSLE.Spec.Supplement.GW1WalkFinishRecord

/-!
# GW1: the remaining local inputs and the two parametrization statements

This is a conditional assembly, not an unconditional provider. The unproved inputs are
the local exit classification and the D.4 exterior-chart/real-record geometry, explicitly
defined below. The earlier tip, clearance, and completion statements are consequences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1WalkFinish

open Exist Exist.Staged Exist.StagedLaw GW1WalkChain GW1ParamEvery
open PiecewiseConstantBoundaryData (jumpSet)

/-- The local classification at each live ordinary instruction. It includes positivity
at admissible restarts and the choice of the outward threshold at a finite lifetime. -/
def WalkExitClassification (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ n ≤ (jumpSet b jumps).card,
    let R := ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D
    stStatus (R (2 * n)) ≠ stDone →
      ForwardExit κ b right (R (2 * n)) (R (2 * n + 1))

/-- The precise D.4 geometry still needed: the new piece's real contacts lie behind
its exit record, and the exterior chart corresponds to the physical record at launches
and finite exits. The continuous extension itself is already proved to exist. -/
def WalkD4Geometry (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  PieceRealRecordBound κ b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right D ∧
  (∀ k, let R := ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D
    (R (k + 1)).2.2.2.1 k ≠ none →
      ExteriorRecord right (R k) ∧ ((D k).2 ≠ ⊤ → ExteriorRecord right (R (k + 1))))

/-- Both orientations, with exactly the ambient assumptions of the earlier run interface.
The orientation is passed to the predicate explicitly. -/
def WalkLocalStatement
    (F : ℝ → (ℝ → ℝ) → Finset ℝ → Bool → (ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec k ω, IsRegularDriver (E spec k ω)) →
      ∀ right : Bool, ∀ᵐ ω ∂P,
        F κ b jumps right (fun j => E (GW1Z.walkSpec b jumps right) j ω)

/-- Unproved probabilistic input: local classification of the exit of every live stage. -/
def WalkExitClassificationStatement : Prop := WalkLocalStatement.{u} WalkExitClassification

/-- Unproved D.4 input: the physical records and the exterior chart correspondence. -/
def WalkD4GeometryStatement : Prop := WalkLocalStatement.{u} WalkD4Geometry

theorem walkCompletionStatement_of_exitClassification
    (hX : WalkExitClassificationStatement.{u}) : WalkCompletionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg right
  filter_upwards [hX κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg right] with ω hXω
  exact walkCompletion_of_forwardExit _ hXω

theorem walkConnectorClearanceStatement_of_d4_and_exit
    (hX : WalkExitClassificationStatement.{u}) (hD4 : WalkD4GeometryStatement.{u}) :
    WalkConnectorClearanceStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg right
  filter_upwards [hX κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg right,
    hD4 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg right] with ω hXω hD4ω
  exact walkConnectorClearance_of_pieceRealRecordBound _ hXω hD4ω.1

theorem walkTipCoordinatesStatement_of_d4 (hT13 : Theorem13Statement.{u})
    (hD4 : WalkD4GeometryStatement.{u}) : WalkTipCoordinatesStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg right
  have hR := stagedPiecesRegular_of_regular hT13 hκ hb
    (hE (GW1Z.walkSpec b jumps right)
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right))
    (hreg (GW1Z.walkSpec b jumps right))
  filter_upwards [hD4 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg right, hR]
    with ω hD4ω hRω
  apply walkTipCoordinates_of_exteriorRecords _ ?_ hD4ω.2
  intro k c θ hl
  obtain ⟨hk, -, -⟩ := eq_launch_of_launches (GW1Z.walkSpec b jumps right) _ hl
  exact hRω k θ _ c hk hl

/-- Both parametrizations from GW1Z's per-piece theorem and the two explicit local inputs.
No earlier tip-coordinate, connector-clearance, or walk-completion statement is assumed. -/
theorem paramEveryRegStatements_of_pieceSimple_and_d4
    (hS : GW1Z.GW1PieceSimpleStatement.{u}) (hT13 : Theorem13Statement.{u})
    (hX : WalkExitClassificationStatement.{u}) (hD4 : WalkD4GeometryStatement.{u}) :
    GW1X.GW1ParamEveryRegStatement.{u} ∧ WalkProper.LeftWalkParamEveryRegStatement.{u} := by
  have hG := walkChainStatement_of_pieceSimple hS hT13
    (walkTipCoordinatesStatement_of_d4 hT13 hD4)
    (walkConnectorClearanceStatement_of_d4_and_exit hX hD4)
    (walkCompletionStatement_of_exitClassification hX)
  exact ⟨gw1ParamEveryRegStatement_of_chain hG, leftWalkParamEveryRegStatement_of_chain hG⟩

/-- Clock-based assembly with the remaining local mathematics visible as hypotheses.
This does not assert that either remaining input has been proved. -/
theorem paramEveryRegStatements_of_walkClock_and_d4
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hClock : GW1Z.WalkLaunchClockStatement.{u})
    (hX : WalkExitClassificationStatement.{u}) (hD4 : WalkD4GeometryStatement.{u}) :
    GW1X.GW1ParamEveryRegStatement.{u} ∧ WalkProper.LeftWalkParamEveryRegStatement.{u} :=
  paramEveryRegStatements_of_pieceSimple_and_d4
    (GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 hT13 hT13₀ hClock) hT13 hX hD4

end InteractingSLE.Theorem14.GW1WalkFinish
