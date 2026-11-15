/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkFirstSeedMain

/-! # Later launches: the original seed and the zero-lifetime obstruction

These deterministic results require no conditional word or stochastic law.
They distinguish original seed admissibility from admissibility in the active chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkLaterSeed

open Exist.Staged Exist.StagedLaw GW1WalkFinish WalkFirstSeed WalkSeedFinite WalkCapBlock
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- A later actual launch starts at an original jump mark with an admissible
original seed. This does not identify the active conditional boundary word. -/
theorem laterLaunch_mark_seed (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk0 : 0 < k)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) :
    let s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k
    (∃ r, stStatus s = GW1W.stArcM r ∧ stPt s ∈ jumpSet b jumps) ∧
      ExplState.IsAdmissibleSeed κ (leftLim b (stPt s)) (rightLim b (stPt s)) θ := by
  let w := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps w D
  obtain ⟨hev, hlt⟩ := GW1W.even_of_launches_walk hk
  have heq : k = 2 * (k / 2) := by omega
  have hn : k / 2 ≤ (jumpSet b jumps).card + 1 := by
    rw [boundaryWalk_length] at hlt
    omega
  have hmark := terminal_or_mark_at_round (κ := κ) (θ := θ) (right := right) D hn
    (by omega : 0 < k / 2)
  rw [← heq] at hmark
  rcases hmark with ht | ⟨r, hs, hp⟩
  · exact (hk (isTerminal_run_of_le w D ht k le_rfl).2).elim
  · refine ⟨⟨r, hs, hp⟩, ?_⟩
    have hf : R (k + 1) = ExplState.flowStep κ b false (R k) k (D k) θ ⊤ :=
      GW1W.run_succ_walk_flow hlt hev
    have hl : (flowByStatus κ b false (stStatus (R k)) (R k) k (D k) θ ⊤).2.2.2.1 k ≠ none := by
      rw [← flowStep_eq_byStatus, ← hf]
      exact hk
    have ha := (launches_flowByStatus_ne_none_iff false (stStatus (R k)) (R k)
      (launches_run_of_le w D le_rfl) (D k) θ ⊤).1 hl
    change stStatus (R k) = GW1W.stArcM r at hs
    rw [hs] at ha
    have hseed := ha.2
    rw [heights_eq, hs] at hseed
    exact hseed

/-- A zero-lifetime later launch ends at the same original admissible seed,
and hence cannot satisfy the finite-exit seed-blocking claim. -/
theorem not_seedBlocked_of_later_zero (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk0 : 0 < k)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none)
    (hz : (D k).2 = 0) :
    ¬ SeedBlocked κ b θ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)) := by
  obtain ⟨⟨r, hs, -⟩, ha⟩ := laterLaunch_mark_seed D hk0 hk
  have htip : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) ≠ stTip := by
    rw [hs]
    intro h
    cases h
  obtain ⟨hst, hpt, -⟩ := GW1W.launch_zero (s := ExplState.run κ b jumps
    (boundaryWalkSpec b jumps θ right) D k) (k := k) (θ := θ) hz htip
  rw [← GW1W.launch_walk hk] at hst hpt
  rintro (ht | hbad)
  · change stStatus _ = stDone ∨ stStatus _ = stDead at ht
    rcases ht with ht | ht <;> rw [hst] at ht <;> cases ht
  · apply hbad
    rw [heights_eq, hst]
    change ExplState.IsAdmissibleSeed κ (leftLim b (stPt _)) (rightLim b (stPt _)) θ
    rwa [hpt]

/-- The zero-lifetime exclusion needed by later finite-exit seed blocking. -/
def NoZeroLaterLaunchData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  ∀ k, 0 < k → (R (k + 1)).2.2.2.1 k ≠ none → (D k).2 ≠ 0

/-- The remaining finite-exit geometry restricted to positive lifetimes. -/
def PositiveLaterExitSeedData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  ∀ k, 0 < k → (R (k + 1)).2.2.2.1 k ≠ none → 0 < (D k).2 → (D k).2 ≠ ⊤ →
    SeedBlocked κ b θ (R (k + 1))

/-- This is an equivalence: excluding later zero lifetimes is necessary,
and together with positive finite exits is sufficient. -/
theorem laterFiniteExitSeedData_iff (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    LaterFiniteExitSeedData κ b jumps θ right D ↔
      NoZeroLaterLaunchData κ b jumps θ right D ∧ PositiveLaterExitSeedData κ b jumps θ right D := by
  constructor
  · intro h
    constructor
    · intro k hk0 hk hz
      exact not_seedBlocked_of_later_zero D hk0 hk hz
        (h k hk0 hk (by rw [hz]; exact ENNReal.zero_ne_top))
    · intro k hk0 hk _ hfin
      exact h k hk0 hk hfin
  · rintro ⟨hz, hp⟩ k hk0 hk hfin
    exact hp k hk0 hk (pos_iff_ne_zero.2 (hz k hk0 hk)) hfin

end InteractingSLE.Theorem14.WalkLaterSeed
