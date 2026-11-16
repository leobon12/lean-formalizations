/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver_completedRange_eq_closure_lightCone
import InteractingSLE.Spec.Supplement.GW2InteriorQFixed

/-!
# Theorem 1.4's light cone for every prescribed schedule set: target statements (ruling R126)

Orchestrator-owned interface file (ruling R126; workers import it and never edit it).

The frozen light-cone theorem `IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone` asserts the range
identity for *some* deterministic countable dense schedule set `Q ⊂ (0, ∞)`, chosen after the law (`∃ Q`). The paper
(p. 22) uses the positive rational switching times, and its Proposition 5.9 allows any dense time set. The statement
below asserts the identity for *every* deterministic countable dense `Q ⊂ (0, ∞)`, so in particular for the positive
rationals. It implies the frozen theorem.

The only place where the special `Q` enters the proof is the interior-switch condition: in
`Theorem14.GW2Tip.gw2LightConeR51Statement_of_interiorQ'`, the tip exhaustion (`GW2TipExhaustionAllQStatement`)
already holds for every `Q`. Only the containment of each schedule's path in the range uses GB9a's set of good
times (`GW2InteriorScheduleQStatement'`). That set is produced by Fubini from the pathwise null set of bad switching
times. `GW2InteriorScheduleAllQStatement` is that condition at every deterministic schedule.

## Statements

* `GW2InteriorScheduleAllQStatement`: the core. It is GB9a's interior-switch condition for every deterministic
  countable dense `Q ⊂ (0, ∞)`.
* `LightConeAllScheduleStatement`: Theorem 1.4's light cone for every such `Q`, both bullets of the frozen theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.LightConeAllQ

/-- **The core: interior switching tips at every deterministic schedule.** GB9a's condition
(`Theorem14.GW2Tip.GW2InteriorScheduleQStatement'`) with the schedule set `Q` given (any deterministic countable dense
`Q ⊂ (0, ∞)`) instead of chosen: almost surely, before every launched instruction of a `Q`-schedule from the root `0`
or a lower-arc root, every switching tip is interior. -/
def GW2InteriorScheduleAllQStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
    ∀ Q : Set ℝ≥0, Q.Countable → Dense Q → (∀ q ∈ Q, 0 < q) →
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        ∀ x : ℝ, (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) →
        ∀ l : List (ℝ × ℝ≥0), IsSchedule Θ Q l →
        ∀ k : ℕ, k < l.length → ∀ᵐ ω ∂P,
          Theorem14.GW2Schedule.AllSucc (Theorem14.GW2Schedule.schedDelta 0 l)
            (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k →
          Theorem14.GW2Later.SwitchTipsInterior ⟨x, true, scheduleProgram 0 l⟩
            (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k

/-- **Theorem 1.4, light cone, for every prescribed schedule set.** The frozen theorem
`IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone` with its `∃ Q` replaced by a given deterministic
countable dense `Q ⊂ (0, ∞)` (for instance the positive rationals, as in the paper, p. 22). -/
def LightConeAllScheduleStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (_hcf : IsCenteredCounterflowDriver κ P h W' ζ') (_hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (Θ : Set ℝ) (_hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (_hΘc : Θ.Countable)
    (_hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ)
    (Q : Set ℝ≥0) (_hQc : Q.Countable) (_hQd : Dense Q) (_hQpos : ∀ q ∈ Q, 0 < q),
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
          counterflowCompletedRange (fun t => W' t ω)) ∧
      ∀ 𝒞 : Set (List Instr), 𝒞.Countable → (∀ p ∈ 𝒞, IsBoundaryContinuedProgram p) →
        ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪
            (⋃ p ∈ 𝒞, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω)) ∪
            {0}) =
          counterflowCompletedRange (fun t => W' t ω)

end InteractingSLE.LightConeAllQ
