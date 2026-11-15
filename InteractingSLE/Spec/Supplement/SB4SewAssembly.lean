/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewKernel

/-!
# SB4 and the frontier conditional on the retained-tail construction

The deterministic sewing, including real contacts, is proved in the preceding
modules. The two propositions below are the remaining open construction for
arbitrary staged histories: joint retained conditional comparisons and Borel
incidence data. Their hypotheses preserve every original source hypothesis.
No unconditional SB4 or frontier result is claimed in this file.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.SB

open Sec4
open PiecewiseConstantBoundaryData (rightLim jumpSet)

/-- Open input: construct the actual retained-tail data at every distinct-seed
switch, in both orientations, with the unchanged source hypotheses. -/
def SB4DistinctSeedRetainedTailStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      (∀ u ≤ 0, (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        ScheduleActualTailSewing κ b jumps P E u l (fun ω =>
          rightSideOf (lowerWalkSet κ b jumps E ω))) ∧
      (∀ v, 0 ≤ v → (∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        ScheduleActualTailSewing κ b jumps P E v l (fun ω =>
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))))

/-- The unresolved local construction after retaining the initial lower connector
through its seed, with the original low-arc and angle hypotheses unchanged. -/
def SB4InitialArcRetainedTailStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ v : ℝ, 0 < v →
      rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ →
      (∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      ScheduleActualTailSewing κ b jumps P E v l (fun ω =>
        rightSideOf (lowerWalkSet κ b jumps E ω))

/-- Distinct-seed switch comparison from the still-open retained-tail input. -/
theorem sb4DistinctSeedSwitchRegStatement_of_retainedTail
    (hC : SB4DistinctSeedRetainedTailStatement.{u}) :
    SB4DistinctSeedSwitchRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  have hc := hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun x hx hθ hL hH =>
    scheduleStepAvoidance_of_actualTailSewing (hc.1 x hx hθ hL hH),
    fun x hx hθ hR hH =>
    scheduleStepAvoidance_of_actualTailSewing (hc.2 x hx hθ hR hH)⟩

/-- Initial-connector switch comparison from its retained-tail input. -/
theorem sb4InitialArcSwitchRegStatement_of_retainedTail
    (hC : SB4InitialArcRetainedTailStatement.{u}) :
    SB4InitialArcSwitchRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
    v hv hlow0 hlow l hl h41 hθ
  exact scheduleStepAvoidance_of_actualTailSewing
    (hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
      v hv hlow0 hlow l hl h41 hθ)

/-- The entire distinct-seed schedule, conditional on the retained-tail input. -/
theorem sb4DistinctSeedRegStatement_of_retainedTail
    (hC : SB4DistinctSeedRetainedTailStatement.{u}) : SB4DistinctSeedRegStatement.{u} :=
  sb4DistinctSeedRegStatement_of_switch
    (sb4DistinctSeedSwitchRegStatement_of_retainedTail hC)

/-- The entire initial-connector schedule, conditional on the retained-tail input. -/
theorem sb4InitialArcRegStatement_of_retainedTail
    (hC : SB4InitialArcRetainedTailStatement.{u}) : SB4InitialArcRegStatement.{u} :=
  sb4InitialArcRegStatement_of_switch (sb4InitialArcSwitchRegStatement_of_retainedTail hC)

/-- The exact frontier statement, still conditional on both retained-tail
constructions and the existing light-cone and walk-range inputs. -/
theorem sbFrontierRegStatement_of_retainedTail
    (hGW2 : GW2LightConeStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hDS : SB4DistinctSeedRetainedTailStatement.{u})
    (hIA : SB4InitialArcRetainedTailStatement.{u}) : SBFrontierRegStatement.{u} :=
  sbFrontierRegStatement_of_switch hGW2 hGW0
    (sb4DistinctSeedSwitchRegStatement_of_retainedTail hDS)
    (sb4InitialArcSwitchRegStatement_of_retainedTail hIA)

end InteractingSLE.Theorem14.SB

