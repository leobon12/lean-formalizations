/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LaunchClockRun

/-!
# GW1: launch-clock induction from the finite terminal/connector pair

The base, clock composition, and run induction are proved. The remaining named
input is the retained-past BW1–BW2–BR4a pair, with measurable regular drivers.
The existing statement-only BW1 and BR4a interfaces do not prove that input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1LaunchClock

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish
open PiecewiseConstantBoundaryData (jumpSet)

/-- The outstanding source step: BW1 for the completed ordinary piece, BW2's
finite forced connector, and BR4a retargeting under the longer retained-past kernel.
It supplies a local clock in the previous pair, not a clock in the original pair.
GB6's conditional counterflow-given-flow-line law remains an explicit input. -/
def FiniteRestartPairStatement : Prop :=
  Supp8.GB6.GB6RestartStatement.{u} →
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
      (∀ spec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (right : Bool) (n : ℕ), n < (jumpSet b jumps).card →
    ∀ (V : ℝ≥0 → Ω → ℝ) (ζV : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
      GW1Z.IsLaunchClock κ b jumps P h W' (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n) V ζV ℓ →
      ∃ (U : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (a : Ω → ℝ≥0 → ℝ≥0),
        IsFiniteRestartPair κ b jumps P h (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) n V U ζ a

/-- Conditional assembly with the exact remaining retained-past pair visible.
This theorem does not claim a proof of `FiniteRestartPairStatement`. -/
theorem walkLaunchClockStatement_of_finiteRestartPair
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hStep : FiniteRestartPairStatement.{u}) : GW1Z.WalkLaunchClockStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ E hE hreg hPieces right k
  let spec := GW1Z.walkSpec b jumps right
  have hProg := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (GW1Z.walkAngle_mem_Icc right) right
  have hS := GW1WalkExit.walkStageData_of_theorem13 hT13₀
    κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ E hE hreg right
  have hP := hPieces spec hProg
  have hprev (n : ℕ) (hn : n < (jumpSet b jumps).card) : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps spec (fun j => E spec j ω) (2 * (n + 1) + 1)).2.2.2.1
        (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps spec (fun j => E spec j ω) (2 * n + 1)).2.2.2.1
        (2 * n) ≠ none := by
    filter_upwards [hS, hP] with ω hs hp
    apply previous_launch_of_next hκ hb _ (fun j => hreg spec j ω) hs ?_ hn
    intro j c θ hl
    exact hp j θ _ c (eq_launch_of_launches spec _ hl).1 hl
  have hInd : ∀ n ≤ (jumpSet b jumps).card,
      ∃ (V : ℝ≥0 → Ω → ℝ) (ζV : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
        GW1Z.IsLaunchClock κ b jumps P h W' spec (E spec) (2 * n) V ζV ℓ := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨V, hV⟩ := exists_isLaunchClock_zero hT13 hκ b jumps hcf hζ spec rfl (E spec)
      exact ⟨V, ζ', fun _ => id, hV⟩
    | succ n ih =>
      intro hn
      obtain ⟨V, ζV, ℓ, hV⟩ := ih (by omega)
      obtain ⟨U, ζ, a, hR⟩ := hStep hGB6 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ
        E hE hreg hPieces right n (by omega) V ζV ℓ hV
      exact ⟨U, ζ, fun ω => ℓ ω ∘ a ω,
        isLaunchClock_succ_of_finiteRestartPair hV hR (hprev n (by omega))⟩
  by_cases hk : k % 2 = 0 ∧ k / 2 ≤ (jumpSet b jumps).card
  · have heq : 2 * (k / 2) = k := by omega
    simpa only [heq] using hInd (k / 2) hk.2
  · refine ⟨fun _ _ => 0, fun _ => ⊤, fun _ => id, isLaunchClock_of_noLaunch ?_⟩
    intro ω
    by_contra hn
    obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hn
    rw [boundaryWalk_length] at hlen
    exact hk ⟨hev, by omega⟩

/-- Both walk parametrizations with the remaining BW1–BW2–BR4a step named explicitly. -/
theorem paramEveryRegStatements_of_finiteRestartPair
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hStep : FiniteRestartPairStatement.{u}) :
    GW1X.GW1ParamEveryRegStatement.{u} ∧ WalkProper.LeftWalkParamEveryRegStatement.{u} :=
  GW1WalkExit.paramEveryRegStatements_of_walkClock hGB6 hT13 hT13₀
    (walkLaunchClockStatement_of_finiteRestartPair hGB6 hT13 hT13₀ hStep)

end InteractingSLE.Theorem14.GW1LaunchClock
