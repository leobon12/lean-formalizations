/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SwitchWords
import InteractingSLE.Spec.Supplement.SB4SwitchStopped
import InteractingSLE.Spec.Supplement.SB4SwitchKernel
import InteractingSLE.Spec.Supplement.SBFrontierReg

/-!
# SB4 switches from retained conditional comparisons

This file separates the unresolved local sewing construction from its proved
consequences. The remaining inputs produce S1 certificates in the retained chart,
physical side correspondence, and measurable rational incidence of the actual
piece. They do not assert either requested switch proposition as a hypothesis.
They remain mathematical obligations; these are conditional helpers, not providers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open QuantumZipper (chiC)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB

open Sec4
open PiecewiseConstantBoundaryData (rightLim jumpSet)

/-- The remaining retained-chart sewing data for a single actual piece. The
conditional S1 and physical side correspondence are `HasSewnSideCertificate`;
the other fields permit the proved conditional-law transfer with R51 regularity.
This predicate is not proved by any theorem in this file. -/
def HasConditionalSewnSideData {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (F : Set Ω) (A S : Ω → Set ℂ) : Prop :=
  ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (a : Ω → ℝ≥0 → ℂ),
    NullMeasurableSet F P ∧
    (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
    (∀ᵐ ω ∂P, ω ∈ F → Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω)) ∧
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀),
      ω ∈ F → HasSewnSideCertificate (A ω) (S ω)

/-- Local data for every prescribed switch, assuming only the already retained
prefix's avoidance. This is the still-open conditional sewing construction. -/
def ScheduleConditionalComparison {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (S : Ω → Set ℂ) : Prop :=
  ∀ k < (scheduleProgram 0 l).length,
    (∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅) →
    HasConditionalSewnSideData P
      {ω | (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k ≠ none}
      (fun ω => schedulePiece κ b jumps x l
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) S

/-- The measurable kernel transfer discharges the switch consequence of the
retained conditional comparison; it adds no source premise to the switch target. -/
theorem scheduleStepAvoidance_of_conditionalComparison {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {x : ℝ} {l : List (ℝ × ℝ≥0)} {S : Ω → Set ℂ}
    (hC : ScheduleConditionalComparison κ b jumps P E x l S) :
    ScheduleStepAvoidance κ b jumps P E x l S := by
  intro k hk hprev
  obtain ⟨𝒢, a, hF, hm, hreg, hcert⟩ := hC k hk hprev
  exact ae_piece_avoids_of_kernel_certificate 𝒢.2 hF hm hreg hcert

/-- The unresolved distinct-seed local construction, with the original hypotheses
unchanged and the original-real bridge word retained. -/
def SB4DistinctSeedConditionalComparisonStatement : Prop :=
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
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      (∀ u ≤ 0, (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        ScheduleConditionalComparison κ b jumps P E u l (fun ω =>
          rightSideOf (lowerWalkSet κ b jumps E ω))) ∧
      (∀ v, 0 ≤ v → (∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        ScheduleConditionalComparison κ b jumps P E v l (fun ω =>
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))))

/-- The unresolved local construction after retaining the initial lower connector
through its seed, with the original low-arc and angle hypotheses unchanged. -/
def SB4InitialArcConditionalComparisonStatement : Prop :=
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
      ScheduleConditionalComparison κ b jumps P E v l (fun ω =>
        rightSideOf (lowerWalkSet κ b jumps E ω))

/-- The requested distinct-seed switch proposition from its exact remaining local
conditional sewing data. The latter still requires proof. -/
theorem sb4DistinctSeedSwitchRegStatement_of_conditionalComparison
    (hC : SB4DistinctSeedConditionalComparisonStatement.{u}) :
    SB4DistinctSeedSwitchRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  have hc := hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun x hx hθ hL hH =>
    scheduleStepAvoidance_of_conditionalComparison (hc.1 x hx hθ hL hH),
    fun x hx hθ hR hH =>
    scheduleStepAvoidance_of_conditionalComparison (hc.2 x hx hθ hR hH)⟩

/-- The requested initial-arc switch proposition from its exact remaining local
conditional sewing data. The latter still requires proof. -/
theorem sb4InitialArcSwitchRegStatement_of_conditionalComparison
    (hC : SB4InitialArcConditionalComparisonStatement.{u}) :
    SB4InitialArcSwitchRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
    v hv hlow0 hlow l hl h41 hθ
  exact scheduleStepAvoidance_of_conditionalComparison
    (hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
      v hv hlow0 hlow l hl h41 hθ)

/-- The already landed frontier assembly now consumes the local conditional
sewing inputs through the checked switch and finite-induction theorems. -/
theorem sbFrontierRegStatement_of_conditionalComparison
    (hGW2 : GW2LightConeStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hDS : SB4DistinctSeedConditionalComparisonStatement.{u})
    (hIA : SB4InitialArcConditionalComparisonStatement.{u}) : SBFrontierRegStatement.{u} :=
  sbFrontierRegStatement_of_switch hGW2 hGW0
    (sb4DistinctSeedSwitchRegStatement_of_conditionalComparison hDS)
    (sb4InitialArcSwitchRegStatement_of_conditionalComparison hIA)

end InteractingSLE.Theorem14.SB
