/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLeafStep

/-!
# The two SB4 retained-tail leaves from SB3 and the S1-free relative data

Packet PROVE-T14-SBTAIL. Theorem 1.4's wiring (`Wire.theorem14Statement_current_expanded`) has the
leaves `SB4DistinctSeedRetainedTailStatement` and `SB4InitialArcRetainedTailStatement`
(`Spec/Supplement/SB4SewAssembly`). Each asks, at every switch of an upper schedule, for SBSEW's
`HasConditionalActualTailSewing`, whose S1 clause is the whole comparison of SB4's proof.

Following the proof of SB4 (specification pp. 634–635: "The distinct-seed version of SB3 just proved
applies ... Apply its stage induction to this new upper piece and the actual relative lower walk"),
this file derives both leaves from

* `SB3InductionGenStatement` (Lemma SB3's stage induction, source form), and
* the S1-free statements `SB4DistinctSeedRelTailStatement`, `SB4InitialArcRelTailStatement`:
  the same hypotheses as the leaves, with `HasConditionalRelativeTail` in place of
  `HasConditionalActualTailSewing` (SB2(2)'s relative walk and the new piece's relative chart as an
  SB3 instance under the retained conditional law, plus the pathwise gluing geometry),

together with Theorems 1.2–1.3 (permitted for Theorem 1.4, R48). No comparison or crossing
argument remains in the new statements. They are open inputs, not proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Leaf

open Sec4
open PiecewiseConstantBoundaryData (rightLim jumpSet)

/-- The S1-free switch data at every instruction of a schedule from `x`, against the forbidden
side `S` (the analogue of `ScheduleActualTailSewing`). -/
def ScheduleRelativeTail {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (S : Ω → Set ℂ) : Prop :=
  ∀ k < (scheduleProgram 0 l).length,
    (∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅) →
    HasConditionalRelativeTail κ P
      {ω | (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k ≠ none}
      (fun ω => schedulePiece κ b jumps x l
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) S

/-- SB3 turns the S1-free switch data into SBSEW's local construction. -/
theorem scheduleActualTailSewing_of_relativeTail (hSB3 : SB3InductionGenStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {x : ℝ} {l : List (ℝ × ℝ≥0)} {S : Ω → Set ℂ}
    (h : ScheduleRelativeTail κ b jumps P E x l S) :
    ScheduleActualTailSewing κ b jumps P E x l S :=
  fun k hk hprev => hasConditionalActualTailSewing_of_relativeTail hSB3 h12 h13 hκ hκ4 (h k hk hprev)

/-- **S1-free form of `SB4DistinctSeedRetainedTailStatement`**: the same hypotheses, with the
relative SB3 instance and gluing geometry at every switch instead of the sewing certificate. -/
def SB4DistinctSeedRelTailStatement : Prop :=
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
        ScheduleRelativeTail κ b jumps P E u l (fun ω =>
          rightSideOf (lowerWalkSet κ b jumps E ω))) ∧
      (∀ v, 0 ≤ v → (∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        ScheduleRelativeTail κ b jumps P E v l (fun ω =>
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))))

/-- **S1-free form of `SB4InitialArcRetainedTailStatement`**. -/
def SB4InitialArcRelTailStatement : Prop :=
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
      ScheduleRelativeTail κ b jumps P E v l (fun ω =>
        rightSideOf (lowerWalkSet κ b jumps E ω))

/-- **The distinct-seed retained-tail leaf from SB3 and the S1-free data.** -/
theorem sb4DistinctSeedRetainedTailStatement_of_relTail (hSB3 : SB3InductionGenStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : SB4DistinctSeedRelTailStatement.{u}) : SB4DistinctSeedRetainedTailStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  have hc := hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun x hx hθ hL hH =>
      scheduleActualTailSewing_of_relativeTail hSB3 h12 h13 hκ hκ4 (hc.1 x hx hθ hL hH),
    fun x hx hθ hR' hH =>
      scheduleActualTailSewing_of_relativeTail hSB3 h12 h13 hκ hκ4 (hc.2 x hx hθ hR' hH)⟩

/-- **The initial-arc retained-tail leaf from SB3 and the S1-free data.** -/
theorem sb4InitialArcRetainedTailStatement_of_relTail (hSB3 : SB3InductionGenStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : SB4InitialArcRelTailStatement.{u}) : SB4InitialArcRetainedTailStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ
  exact scheduleActualTailSewing_of_relativeTail hSB3 h12 h13 hκ hκ4
    (hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ)

/-- SB4's distinct-seed clause (both orientations) from SB3 and the S1-free data. -/
theorem sb4DistinctSeedRegStatement_of_relTail (hSB3 : SB3InductionGenStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : SB4DistinctSeedRelTailStatement.{u}) : SB4DistinctSeedRegStatement.{u} :=
  sb4DistinctSeedRegStatement_of_retainedTail
    (sb4DistinctSeedRetainedTailStatement_of_relTail hSB3 h12 h13 hR)

/-- SB4's initial-arc clause from SB3 and the S1-free data. -/
theorem sb4InitialArcRegStatement_of_relTail (hSB3 : SB3InductionGenStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : SB4InitialArcRelTailStatement.{u}) : SB4InitialArcRegStatement.{u} :=
  sb4InitialArcRegStatement_of_retainedTail
    (sb4InitialArcRetainedTailStatement_of_relTail hSB3 h12 h13 hR)

end InteractingSLE.Theorem14.SB.Leaf
