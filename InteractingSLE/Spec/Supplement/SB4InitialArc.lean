/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4DistinctSeed

/-!
# SB4's initial-connector barrier from the one-piece comparison

The last paragraph of SB4's proof (specification p. 635) retains the lower prefix
through the initial-connector seed, applies the common-seed barrier in its conditional
field, and restores that prefix by the winding comparison. This retained-field and
physical-side step remains explicit below; the finite induction is proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.SB

open PiecewiseConstantBoundaryData (rightLim jumpSet)

/-- The still-unproved one-piece comparison for a seed on the initial forced lower
connector. Its hypotheses, including the low-arc height conditions and R51 regularity,
are exactly those of `SB4InitialArcRegStatement`. It requires the retained conditional
field at the connector seed and physical side transport after every actual launch. -/
def SB4InitialArcSwitchRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
      ScheduleStepAvoidance κ b jumps P E v l (fun ω =>
        rightSideOf (lowerWalkSet κ b jumps E ω))

/-- Finite induction proves the initial-connector conclusion from its named
one-piece comparison. The comparison remains a hypothesis. -/
theorem sb4InitialArcRegStatement_of_switch
    (hS : SB4InitialArcSwitchRegStatement.{u}) : SB4InitialArcRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
    v hv hlow0 hlow l hl h41 hθ
  exact schedule_avoids_of_step
    (Filter.Eventually.of_forall fun ω hz => ofReal_notMem_H v hz.1.1)
    (hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
      v hv hlow0 hlow l hl h41 hθ)

end InteractingSLE.Theorem14.SB
