/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartPairLaw

/-!
# GW1: checked hypotheses for the two remaining source laws

`RestartData` contains the original step assumptions and the local simplicity and
exit data proved from them. Neither remaining source law assumes the next launch
clock. These named law statements have no providers in this file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1RestartPair

open Exist Exist.Staged Exist.StagedLaw
open PiecewiseConstantBoundaryData (jumpSet)

/-- The existing launch datum and its proved local geometric consequences. -/
structure RestartData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (right : Bool) (n : ℕ)
    (V : ℝ≥0 → Ω → ℝ) (ζV : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0) : Prop where
  pos : 0 < κ
  lt_four : κ < 4
  boundary : IsPiecewiseConstantBoundaryData b jumps
  field : IsGFFWithBoundaryData P h b jumps
  counterflow : IsCenteredCounterflowDriver κ P h W' ζ'
  complete : ∀ᵐ ω ∂P, ζ' ω = ⊤
  staged : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
    IsStagedHistory κ b jumps P h spec (E spec)
  regular : ∀ spec k ω, IsRegularDriver (E spec k ω)
  pieces : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
    StagedPiecesRegular κ b jumps P spec (E spec)
  lt_card : n < (jumpSet b jumps).card
  current : GW1Z.IsLaunchClock κ b jumps P h W' (GW1Z.walkSpec b jumps right)
    (E (GW1Z.walkSpec b jumps right)) (2 * n) V ζV ℓ
  simple : ∀ᵐ ω ∂P, ∀ c θ,
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) =
        some (c, θ) →
    GW1Z.IsSimplePiece c (E (GW1Z.walkSpec b jumps right) (2 * n) ω).1
      (min (instrTime (GW1Z.walkSpec b jumps right) (2 * n))
        (E (GW1Z.walkSpec b jumps right) (2 * n) ω).2)
      (SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n))
  stages : ∀ᵐ ω ∂P, GW1WalkExit.WalkStageData κ b jumps
    (if right then -(Real.pi / 2) else Real.pi / 2) right
    (fun j => E (GW1Z.walkSpec b jumps right) j ω)

/-- BW1 in the current conditional domain, retaining the entire older past.
This is a named missing mathematical input, not a proved source theorem. -/
def TerminalRestartLawStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (right : Bool) (n : ℕ)
    (V : ℝ≥0 → Ω → ℝ) (ζV : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
    RestartData κ b jumps P h W' ζ' E right n V ζV ℓ →
    ∃ (Q : ℝ≥0 → Ω → ℝ) (ζQ : Ω → ℝ≥0∞) (β : Ω → ℝ≥0 → ℝ≥0),
      IsTerminalRestart κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n V Q ζQ β

/-- BW2's finite forced connector and BR4a's full field–path retargeting within
the independently supplied terminal pair. This is a second named missing input. -/
def FiniteRetargetLawStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (right : Bool) (n : ℕ)
    (V : ℝ≥0 → Ω → ℝ) (ζV : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
    RestartData κ b jumps P h W' ζ' E right n V ζV ℓ →
    ∀ (Q : ℝ≥0 → Ω → ℝ) (ζQ : Ω → ℝ≥0∞) (β : Ω → ℝ≥0 → ℝ≥0),
      IsTerminalRestart κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n V Q ζQ β →
    ∃ (U : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (a : Ω → ℝ≥0 → ℝ≥0),
      IsForcedRetarget κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n Q U ζ a

end InteractingSLE.Theorem14.GW1RestartPair
