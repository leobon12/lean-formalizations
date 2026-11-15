/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronLeaf
import InteractingSLE.Spec.Supplement.WalkWordsAccess

/-!
# The pair leaf with the held WalkWords bookkeeping input explicit

Only committed WalkWordsAccess is imported. The already-proved, in-flight
Arc/Run/Piece chain is represented by its exact bookkeeping implication.
Actual direction and chronology are supplied by the new checked theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkIntRunChron

open Exist WalkBdry WalkMean WalkNorm WalkInf

variable (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hBookkeeping : (
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkInf.WalkPairPathFacts κ b jumps E ω) →
      (∀ᵐ ω ∂P, WalkNorm.WalkPiecesSimple κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ pR ∈ (WalkMean.walkRuns κ b jumps E ω).1.1, ∀ pL ∈ (WalkMean.walkRuns κ b jumps E ω).2.1,
        ∀ (a a' c c' : ℝ≥0) (z z' : ℂ), (a : ℝ≥0∞) ≤ pR.2.2 → (a' : ℝ≥0∞) ≤ pR.2.2 →
          (c : ℝ≥0∞) ≤ pL.2.2 → (c' : ℝ≥0∞) ≤ pL.2.2 →
          pR.1.tipAt pR.2.1 a z → pR.1.tipAt pR.2.1 a' z' → pL.1.tipAt pL.2.1 c z → pL.1.tipAt pL.2.1 c' z' →
          a < a' → c < c'
      ) → WalkWords.WalkPairArcDataStatement.{u})

include hT13 hT13₀ hBookkeeping

/-- Actual chronology discharges the direction input. The only retained
pair-bookkeeping input is the implication proved in the held modules. -/
theorem walkPairGeomCOStatement_of_bookkeeping (hS : GW1Z.GW1PieceSimpleStatement.{u}) :
    WalkPairGeomCOStatement.{u} :=
  WalkWords.walkPairGeomCOStatement_of_arcData hS
    (hBookkeeping (ae_recorded_piece_direction hT13 hT13₀))

/-- The original pair leaf from the existing proper-walk/contact facts
and the explicitly retained bookkeeping theorem, with no hChron input. -/
theorem walkPairGeomStatement_of_bookkeeping (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hS : GW1Z.GW1PieceSimpleStatement.{u}) : WalkPairGeomStatement.{u} :=
  walkPairGeomStatement_of_co hCO hPR hPL
    (walkPairGeomCOStatement_of_bookkeeping hT13 hT13₀ hBookkeeping hS)

end InteractingSLE.Theorem14.WalkIntRunChron
