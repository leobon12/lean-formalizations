/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkFirstSeed

/-! # First exits removed from the open input; walks without original jumps -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkFirstSeed

open Exist.Staged Exist.StagedLaw GW1WalkFinish WalkSeedFinite WalkCapBlock
open PiecewiseConstantBoundaryData (jumpSet)

/-- The finite-exit input restricted to strictly later actual launches. -/
def LaterFiniteExitSeedData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  ∀ k, 0 < k → (R (k + 1)).2.2.2.1 k ≠ none → (D k).2 ≠ ⊤ → SeedBlocked κ b θ (R (k + 1))

theorem finiteExitSeedData_of_first_later {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (h0 : SeedBlocked κ b θ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D 1))
    (hL : LaterFiniteExitSeedData κ b jumps θ right D) : FiniteExitSeedData κ b jumps θ right D := by
  intro k hk hfin
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact h0
  · exact hL k hk0 hk hfin

/-- Without original jump marks, no later ordinary instruction can launch. -/
theorem laterFiniteExitSeedData_of_no_marks {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hJ : jumpSet b jumps = ∅) :
    LaterFiniteExitSeedData κ b jumps θ right D := by
  intro k hk0 hk _
  obtain ⟨he, hlt⟩ := GW1W.even_of_launches_walk hk
  rw [boundaryWalk_length, hJ, Finset.card_empty] at hlt
  omega

/-- The freshness condition is vacuous when there is at most one positive
round, as happens when there are no original jump marks. -/
theorem freshRestartData_of_no_marks {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hJ : jumpSet b jumps = ∅) :
    FreshRestartData κ b jumps θ right D := by
  intro m n hm hmn hn _
  rw [hJ, Finset.card_empty] at hn
  omega

/-- For data without original jumps, all seed assertions are proved without
any additional exit or freshness hypothesis, for every angle and either walk. -/
theorem ae_seedData_of_no_marks (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ ω, IsRegularDriver (E 0 ω)) (hJ : jumpSet b jumps = ∅) :
    ∀ᵐ ω ∂P, WalkSeedData κ b jumps θ right (fun j => E j ω) := by
  filter_upwards [ae_first_seedBlocked h13 hκ hb hh hE hreg] with ω hω
  exact seedData_of_finiteExits_freshRestarts (fun j => E j ω)
    (finiteExitSeedData_of_first_later _ hω (laterFiniteExitSeedData_of_no_marks _ hJ))
    (freshRestartData_of_no_marks _ hJ)

/-- Every non-flow cap of a walk without original jumps skips its added
launch. In particular this covers the off-sector constant-data case. -/
theorem ae_noLaunch_capSpec_of_no_marks (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ ω, IsRegularDriver (E 0 ω)) (hJ : jumpSet b jumps = ∅)
    (ℓ : ℕ) (hℓ : ℓ ≤ (boundaryWalkSpec b jumps θ right).2.2.length)
    (hnon : (boundaryWalkSpec b jumps θ right).2.2[ℓ]? ≠ some (Sum.inl (θ, ⊤))) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps θ right) ℓ θ 0)
        (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = none := by
  filter_upwards [ae_seedData_of_no_marks h13 hκ hb hh hE hreg hJ] with ω hω
  exact noLaunch_capSpec_of_seedData (fun j => E j ω) hω ℓ hℓ hnon

end InteractingSLE.Theorem14.WalkFirstSeed
