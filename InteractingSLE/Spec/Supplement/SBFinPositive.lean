/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2PointSchedule
import InteractingSLE.Spec.Supplement.SB4InitialArc
import InteractingSLE.Spec.Supplement.GW2Sched

/-!
# SB4's lower barriers from positive-duration sewing alone (no zero-stop certificate)

Packet PROVE-T14-SBFIN. The launch-form leaves `SB.Leaf.SB4DistinctSeedLaunchTailStatement` and
`SB.Leaf.SB4InitialArcLaunchTailStatement` ask, at every switch, for a sewing certificate
`HasActualTailSewing` even when the next piece is conditionally almost surely the singleton seed (`hzero` of
`hasScheduleLaunchTail_of_seed_cases`). The source has nothing to prove there ("If its new angle has an inadmissible
seed group, its available new history is the singleton seed and there is nothing to add", p. 634), and
PROVE-T14-SBTAIL2 proved the zero-stop avoidance directly (`Retain.ae_zero_stop_avoids_of_prefix`,
`Retain.scheduleStepAvoidance_of_positive_tail`). This file states SB4's two lower-barrier inputs with sewing only
on the positive-duration branch and proves from them the one-piece comparisons and the regularized SB4 clauses:

* `SB4LowerPositiveTailStatement` (the lower-walk half of the distinct-seed clause) and
  `SB4InitialArcPositiveTailStatement` (the initial-arc clause): the hypotheses of the corresponding SB4 clause and
  `Retain.SchedulePositiveTailSewing` against `rightSideOf (lowerWalkSet …)`;
* `sb4InitialArcSwitchRegStatement_of_positiveTail`, **`sb4InitialArcRegStatement_of_positiveTail`**;
* `sb4LowerStepAvoidance_of_positiveTail` (the first conjunct of `SB4DistinctSeedSwitchRegStatement`).

The reflected (upper-walk) half of the distinct-seed clause is unchanged (its sewing input is the reflected one).
These are conditional helpers with distinct names; the positive-duration sewing is the remaining SB2(2) + SB3 step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)

universe u

namespace InteractingSLE.Theorem14.SB.Fin

open Sec4
open PiecewiseConstantBoundaryData (rightLim jumpSet)

/-- The program of the completed lower walk is boundary-continued. -/
theorem isBoundaryContinuedProgram_lowerWalk (b : ℝ → ℝ) (jumps : Finset ℝ) :
    IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
  isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true

/-- **The one-piece comparison against the completed lower walk from positive-duration sewing** (any schedule from
any seed `x` with angles in `[−π/2, π/2]`): the zero-stop branch is the landed direct avoidance. -/
theorem scheduleStepAvoidance_lowerWalk_of_positiveTail {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    {x : ℝ} {l : List (ℝ × ℝ≥0)} (hθ : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hpos : Retain.SchedulePositiveTailSewing κ b jumps P E x l
      (fun ω => rightSideOf (lowerWalkSet κ b jumps E ω))) :
    ScheduleStepAvoidance κ b jumps P E x l (fun ω => rightSideOf (lowerWalkSet κ b jumps E ω)) := by
  have hprog := GW2Sched.isBoundaryContinuedProgram_scheduleProgram hθ 0
  have hL := isBoundaryContinuedProgram_lowerWalk b jumps
  exact Retain.scheduleStepAvoidance_of_positive_tail hκ hb (hE _ hprog) (hreg _ hprog)
    (hE _ hL).1 (hreg _ hL) hpos

/-- **The lower-walk half of SB4's distinct-seed input, positive-duration form**: the hypotheses of the first
conjunct of `SB4DistinctSeedSwitchRegStatement`, with sewing asked only on the positive-duration branch. -/
def SB4LowerPositiveTailStatement : Prop :=
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
      ∀ u ≤ 0, (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        Retain.SchedulePositiveTailSewing κ b jumps P E u l
          (fun ω => rightSideOf (lowerWalkSet κ b jumps E ω))

/-- The first conjunct of `SB4DistinctSeedSwitchRegStatement` from positive-duration sewing. -/
theorem sb4LowerStepAvoidance_of_positiveTail (hS : SB4LowerPositiveTailStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    {l : List (ℝ × ℝ≥0)} (hl : l.Pairwise (fun p q => p.2 < q.2))
    (h41 : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) :
    ∀ u ≤ 0, (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      ScheduleStepAvoidance κ b jumps P E u l (fun ω => rightSideOf (lowerWalkSet κ b jumps E ω)) :=
  fun u hu hθ hL hH => scheduleStepAvoidance_lowerWalk_of_positiveTail hκ hb hE hreg
    (fun p hp => Ioc_subset_Icc_self (hθ p hp))
    (hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41 u hu hθ hL hH)

/-- **SB4's initial-arc input, positive-duration form**: the hypotheses of `SB4InitialArcSwitchRegStatement`, with
sewing asked only on the positive-duration branch. -/
def SB4InitialArcPositiveTailStatement : Prop :=
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
      Retain.SchedulePositiveTailSewing κ b jumps P E v l
        (fun ω => rightSideOf (lowerWalkSet κ b jumps E ω))

/-- `SB4InitialArcSwitchRegStatement` from positive-duration sewing. -/
theorem sb4InitialArcSwitchRegStatement_of_positiveTail (hS : SB4InitialArcPositiveTailStatement.{u}) :
    SB4InitialArcSwitchRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ
  exact scheduleStepAvoidance_lowerWalk_of_positiveTail hκ hb hE hreg
    (fun p hp => Ioc_subset_Icc_self (hθ p hp))
    (hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ)

/-- **SB4's initial-arc clause (regularized) from positive-duration sewing.** -/
theorem sb4InitialArcRegStatement_of_positiveTail (hS : SB4InitialArcPositiveTailStatement.{u}) :
    SB4InitialArcRegStatement.{u} :=
  sb4InitialArcRegStatement_of_switch (sb4InitialArcSwitchRegStatement_of_positiveTail hS)

end InteractingSLE.Theorem14.SB.Fin
