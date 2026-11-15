/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkChainPiece
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# GW1: right and left walk parametrizations from explicit local geometry

The stochastic input is GW1Z's per-piece theorem, including its launch-clock hypothesis.
The three remaining geometric obligations are named below: physical tip coordinates,
connector clearance, and successful completion of the finite program. The results in this
file are conditional reductions; none asserts that these three obligations are proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1ParamEvery

open Exist Exist.Staged Exist.StagedLaw GW1WalkChain GW1Bookkeep

/-- Quantification over both boundary walks of an everywhere-regular staged family.
This is only a shared binder interface for the explicitly named remaining obligations. -/
def WalkRunStatement
    (F : ℝ → (ℝ → ℝ) → Finset ℝ → ExplSpec → (ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) → Prop) : Prop :=
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
        F κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)

/-- Unproved geometric obligation: radial tips agree with the recorded seed and finite endpoint. -/
def WalkTipCoordinatesStatement : Prop := WalkRunStatement.{u} WalkTipCoordinates

/-- Unproved geometric obligation: each traversed real connector clears the entire retained past. -/
def WalkConnectorClearanceStatement : Prop :=
  WalkRunStatement.{u} (fun κ b jumps spec D =>
    WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps) spec D)

/-- Unproved geometric obligation: the finite program reaches `done`, including terminal rays. -/
def WalkCompletionStatement : Prop :=
  WalkRunStatement.{u} (fun κ b jumps spec D =>
    stStatus (ExplState.run κ b jumps spec D spec.2.2.length) = stDone)

/-- The intermediate conclusion of the deterministic run reduction. -/
def WalkChainStatement : Prop :=
  WalkRunStatement.{u} (fun κ b jumps spec D =>
    WalkChainRepresentation spec.1 (ExplState.run κ b jumps spec D spec.2.2.length))

/-- Both orientations of the walk-wide reduction from per-piece simplicity. Theorem 1.3
supplies R51 regularity from the everywhere-regular driver hypothesis. -/
theorem walkChainStatement_of_pieceSimple
    (hS : GW1Z.GW1PieceSimpleStatement.{u}) (hT13 : Theorem13Statement.{u})
    (hT : WalkTipCoordinatesStatement.{u}) (hC : WalkConnectorClearanceStatement.{u})
    (hD : WalkCompletionStatement.{u}) : WalkChainStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg right
  have hR : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec) :=
    fun spec hs => stagedPiecesRegular_of_regular hT13 hκ hb (hE spec hs) (hreg spec)
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hR right,
    hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg right,
    hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg right,
    hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg right] with ω hSω hTω hCω hDω
  apply walkChainRepresentation_of_pieceSimpleAt
    (θ := if right then -(Real.pi / 2) else Real.pi / 2)
    (right := right) (D := fun j => E (GW1Z.walkSpec b jumps right) j ω) ?_ hCω hDω
  intro k c θ hl hseed
  have hpr : ∀ j c θ, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E (GW1Z.walkSpec b jumps right) j ω).1
        (min (instrTime (GW1Z.walkSpec b jumps right) j)
          (E (GW1Z.walkSpec b jumps right) j ω).2) := by
    intro j c θ hj
    obtain ⟨f, α, C, hf, hC, h0, hW, hα, htr, hi, ha⟩ := hSω j c θ hj
    exact ⟨h0, hW, α, hα, htr⟩
  have hmaps := maps_H_chart_run (κ := κ) (b := b) (jumps := jumps)
    (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω) hpr k
  obtain ⟨_, _, hc⟩ := eq_launch_of_launches (GW1Z.walkSpec b jumps right)
    (fun j => E (GW1Z.walkSpec b jumps right) j ω) hl
  have hmaps' : MapsTo c.2.1 QuantumZipper.H QuantumZipper.H := by rw [hc]; exact hmaps
  exact pieceSimpleAt_of_isSimplePiece (hSω k c θ hl) hmaps' hseed (hTω k c θ hl).1 (hTω k c θ hl).2

theorem gw1ParamEveryRegStatement_of_chain (hG : WalkChainStatement.{u}) :
    GW1X.GW1ParamEveryRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true] with ω hω
  obtain ⟨γ, hγ, hγ0, hset⟩ := exists_isProperCurve_of_walkChainRepresentation hω
  refine ⟨γ, hγ, ?_, hset⟩
  simpa only [GW1Z.walkSpec, boundaryWalkSpec, Complex.ofReal_zero] using hγ0

theorem leftWalkParamEveryRegStatement_of_chain (hG : WalkChainStatement.{u}) :
    WalkProper.LeftWalkParamEveryRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false] with ω hω
  obtain ⟨γ, hγ, hγ0, hset⟩ := exists_isProperCurve_of_walkChainRepresentation hω
  refine ⟨γ, hγ, ?_, hset⟩
  simpa only [GW1Z.walkSpec, boundaryWalkSpec, Complex.ofReal_zero] using hγ0

/-- GW1Z's clock theorem followed by the run reduction, for both walks. The three explicit
geometric hypotheses remain unproved; this is not an unconditional provider. -/
theorem paramEveryRegStatements_of_walkClock
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hClock : GW1Z.WalkLaunchClockStatement.{u})
    (hT : WalkTipCoordinatesStatement.{u}) (hC : WalkConnectorClearanceStatement.{u})
    (hD : WalkCompletionStatement.{u}) :
    GW1X.GW1ParamEveryRegStatement.{u} ∧ WalkProper.LeftWalkParamEveryRegStatement.{u} := by
  have hS := GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 hT13 hT13₀ hClock
  have hG := walkChainStatement_of_pieceSimple hS hT13 hT hC hD
  exact ⟨gw1ParamEveryRegStatement_of_chain hG, leftWalkParamEveryRegStatement_of_chain hG⟩

end InteractingSLE.Theorem14.GW1ParamEvery
