/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkRecordSeed

/-! # The finite-exit input reduces exactly to later nonzero lifetimes

The first piece and every positive finite exit are controlled by the general
staged law. No trace-existence theorem is needed for these seed assertions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkRecordSeed

open Exist.Staged Exist.StagedLaw GW1WalkFinish WalkFirstSeed WalkSeedFinite WalkCapBlock WalkLaterSeed
open PiecewiseConstantBoundaryData (leftLim rightLim)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The first seed is blocked from the staged law alone. This proof uses
regularity of all drivers, rather than a trace-existence hypothesis. -/
theorem ae_first_seedBlocked_of_staged (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, SeedBlocked κ b θ
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) 1) := by
  have hfl := hE.isFlowLineDriver_first hκ hb hh rfl (GW1P.boundaryWalkSpec_prog b jumps θ right)
  filter_upwards [ae_all_stageGood hκ hb hh hE hreg, ae_seed_test_of_isFlowLineDriver hκ hfl]
    with ω hgood hseed
  have hr : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) 1 =
      ExplState.launch (ExplState.init 0) 0 (E 0 ω) θ ⊤ := by
    rw [show 1 = 0 + 1 from rfl, GW1W.run_succ_walk_flow
      (by rw [boundaryWalk_length]; omega) (by rfl)]
    rfl
  have hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      (fun j => E j ω) 1).2.2.2.1 0 ≠ none := by
    rw [hr, launches_launch, Function.update_self]
    exact Option.some_ne_none _
  have hs := hgood 0 hl
  rw [GW1W.instrAngle_walk hl, hr] at hs
  rw [hr]
  by_cases ht : (E 0 ω).2 = ⊤
  · exact Or.inl (isTerminal_launch_of_top _ 0 (E 0 ω) θ ⊤ (by rw [ht]; rfl))
  by_cases hz : (E 0 ω).2 = 0
  · obtain ⟨hst, hpt, -⟩ := GW1W.launch_zero (s := ExplState.init 0) (k := 0) (θ := θ) hz
      (by intro he; cases he)
    right
    intro ha
    apply hseed.1 hz
    rw [heights_eq, hst] at ha
    change ExplState.IsAdmissibleSeed κ
      (leftLim b (stPt (ExplState.launch (ExplState.init 0) 0 (E 0 ω) θ ⊤)))
      (rightLim b (stPt (ExplState.launch (ExplState.init 0) 0 (E 0 ω) θ ⊤))) θ at ha
    rw [hpt] at ha
    exact ha
  · exact seedBlocked_launch_of_threshold_heights _ 0 (E 0 ω) hz ht
      (fun hst => (hs.2.1 hst).1) (fun hst => (hs.2.2.1 hst).1)

/-- Under the actual staged law, all finite exits have blocked seeds if and
only if all later actual launches have nonzero lifetime. The first exit is
proved, and zero lifetime is the only remaining finite-exit obstruction. -/
theorem ae_finiteExitSeedData_iff_noZero (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    (∀ᵐ ω ∂P, FiniteExitSeedData κ b jumps θ right (fun j => E j ω)) ↔
      ∀ᵐ ω ∂P, NoZeroLaterLaunchData κ b jumps θ right (fun j => E j ω) := by
  constructor
  · intro hF
    filter_upwards [hF] with ω hω
    apply (laterFiniteExitSeedData_iff _).1 ?_ |>.1
    intro k _ hk hfin
    exact hω k hk hfin
  · intro hnz
    filter_upwards [ae_first_seedBlocked_of_staged hκ hb hh hE hreg,
      ae_positiveLaterExitSeedData hκ hb hh hE hreg, hnz] with ω h0 hp hz
    exact finiteExitSeedData_of_first_later _ h0 ((laterFiniteExitSeedData_iff _).2 ⟨hz, hp⟩)

/-- Original seed data now need only later nonzero lifetimes and restart
freshness. Positive finite exits are proved, not additional hypotheses. -/
theorem ae_walkSeedData_of_noZero_fresh (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hnz : ∀ᵐ ω ∂P, NoZeroLaterLaunchData κ b jumps θ right (fun j => E j ω))
    (hfresh : ∀ᵐ ω ∂P, FreshRestartData κ b jumps θ right (fun j => E j ω)) :
    ∀ᵐ ω ∂P, WalkSeedData κ b jumps θ right (fun j => E j ω) := by
  filter_upwards [(ae_finiteExitSeedData_iff_noZero hκ hb hh hE hreg).2 hnz, hfresh] with ω hF hfr
  exact seedData_of_finiteExits_freshRestarts (fun j => E j ω) hF hfr

end InteractingSLE.Theorem14.WalkRecordSeed
