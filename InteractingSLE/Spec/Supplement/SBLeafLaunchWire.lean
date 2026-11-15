/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLeafLaunch
import InteractingSLE.Spec.Supplement.SBLeafAssembly
import InteractingSLE.Spec.Supplement.GW2Sched

/-!
# The SB4 leaves from SB3 and the launch-form switch data

Packet PROVE-T14-SBTAIL. The finest form of the remaining SB4 input: at every switch the schedule's
own staged launch clause supplies the conditional field and the new piece
(`HasLaunchRelativeTail`); SB4's word paragraph is reduced to the height classification. The
distinct-seed bridge `(u, 0)` is the retained original word (`distinctSeed_bridge`); on the initial
forced arc every low-arc height is a low group, so no original word is retained there. The
reflected (upper-walk) half of the distinct-seed clause keeps the chart-free form
`ScheduleRelativeTail`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Leaf

open Sec4 GW2Schedule
open PiecewiseConstantBoundaryData (rightLim jumpSet)

/-- The launch-form switch data at every instruction of a schedule from `x`, with retained original
word `original`, against the forbidden side `S`. -/
def ScheduleLaunchTail {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (original : Set ℝ) (S : Ω → Set ℂ) : Prop :=
  ∀ k < (scheduleProgram 0 l).length,
    (∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅) →
    HasScheduleLaunchTail κ b jumps P h x l (E ⟨x, true, scheduleProgram 0 l⟩) k original
      (fun ω => schedulePiece κ b jumps x l
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) S

/-- The launch form gives the chart-free switch data, for a schedule whose angles satisfy (SB4.1)
and whose retained original word satisfies the bridge hypothesis. -/
theorem scheduleRelativeTail_of_launch (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ} {S : Ω → Set ℂ}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩
      (E ⟨x, true, scheduleProgram 0 l⟩))
    (hangles : ∀ p ∈ l, -(Real.pi / 2) < p.1)
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ p ∈ l, ∀ B ∈ original,
      -2 < cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (hL : ScheduleLaunchTail κ b jumps P h E x l original S) :
    ScheduleRelativeTail κ b jumps P E x l S :=
  fun k hk hprev => hasConditionalRelativeTail_of_launch h13 hκ hκ4 hE hangles hgaps hbridge
    (Eventually.of_forall fun _ _ _ hcθ => launch_angle_mem_schedule hcθ)
    (hasLaunchRelativeTail_of_schedule hE hk (hL k hk hprev))

/-- **Launch form of the distinct-seed input**: the same hypotheses as
`SB4DistinctSeedRetainedTailStatement`; the lower-walk half in launch form with the retained bridge
word `b((u, 0))`, the reflected half in the chart-free form. -/
def SB4DistinctSeedLaunchTailStatement : Prop :=
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
        ScheduleLaunchTail κ b jumps P h E u l (b '' {x | x ∈ Ioo u 0 ∧ x ∉ jumps}) (fun ω =>
          rightSideOf (lowerWalkSet κ b jumps E ω))) ∧
      (∀ v, 0 ≤ v → (∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        ScheduleRelativeTail κ b jumps P E v l (fun ω =>
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))))

/-- **Launch form of the initial-arc input** (no retained original word: on the initial forced arc
the heights are low groups). -/
def SB4InitialArcLaunchTailStatement : Prop :=
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
      ScheduleLaunchTail κ b jumps P h E v l ∅ (fun ω =>
        rightSideOf (lowerWalkSet κ b jumps E ω))

theorem sb4DistinctSeedRelTailStatement_of_launch (h13 : Exist.Theorem13Statement.{u})
    (hL : SB4DistinctSeedLaunchTailStatement.{u}) : SB4DistinctSeedRelTailStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  have hc := hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41
  refine ⟨fun x hx hθ hLx hH => ?_, hc.2⟩
  have hprog := GW2Sched.isBoundaryContinuedProgram_scheduleProgram
    (fun p hp => Ioc_subset_Icc_self (hθ p hp)) 0
  exact scheduleRelativeTail_of_launch h13 hκ hκ4 (hE _ hprog) (fun p hp => (hθ p hp).1) h41
    (distinctSeed_bridge hLx hH) (hc.1 x hx hθ hLx hH)

theorem sb4InitialArcRelTailStatement_of_launch (h13 : Exist.Theorem13Statement.{u})
    (hL : SB4InitialArcLaunchTailStatement.{u}) : SB4InitialArcRelTailStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ
  have hprog := GW2Sched.isBoundaryContinuedProgram_scheduleProgram
    (fun p hp => Ioc_subset_Icc_self (hθ p hp)) 0
  exact scheduleRelativeTail_of_launch h13 hκ hκ4 (hE _ hprog) (fun p hp => (hθ p hp).1) h41
    (fun _ _ _ hB => absurd hB (notMem_empty _))
    (hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ)

/-- **Both SB4 leaves of Theorem 1.4's wiring** from SB3 (source form), Theorems 1.2–1.3 and the
launch-form switch data. -/
theorem sb4RetainedTailStatements_of_launch (hSB3 : SB3InductionGenStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hDS : SB4DistinctSeedLaunchTailStatement.{u}) (hIA : SB4InitialArcLaunchTailStatement.{u}) :
    SB4DistinctSeedRetainedTailStatement.{u} ∧ SB4InitialArcRetainedTailStatement.{u} :=
  ⟨sb4DistinctSeedRetainedTailStatement_of_relTail hSB3 h12 h13
      (sb4DistinctSeedRelTailStatement_of_launch h13 hDS),
    sb4InitialArcRetainedTailStatement_of_relTail hSB3 h12 h13
      (sb4InitialArcRelTailStatement_of_launch h13 hIA)⟩

end InteractingSLE.Theorem14.SB.Leaf
