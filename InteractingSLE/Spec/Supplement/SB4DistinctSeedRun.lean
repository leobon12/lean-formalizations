/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OwnHistoryPath

/-!
# SB4: finite induction over actual schedule launches

The switch argument of SB4 (specification pp. 634–635) adds precisely one stopped
ordinary piece. This file proves the deterministic and almost-everywhere induction,
including unsuccessful launches and finite terminal endpoints. The conditional-field
comparison for a new piece is an explicit hypothesis `ScheduleStepAvoidance`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB

open Exist.Staged Exist.StagedLaw CounterflowRange GW2Schedule

/-- The physical tip set added by instruction `k` when it launches, including its
available terminal value. The expression is used only on the launch event. -/
def schedulePiece (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : Set ℂ :=
  (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D k).2.2.2.2.1.tipSet
    (fun r : ℝ≥0 => (D k).1
      (min (r : ℝ≥0∞) (min (schedDelta 0 l k) (D k).2)).toNNReal)
    (min (schedDelta 0 l k) (D k).2)

/-- A successful schedule launch adjoins exactly its stopped physical piece. -/
theorem prefixPhysSet_schedule_succ_of_launch {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hk : k < (scheduleProgram 0 l).length)
    (hlaunch : (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D
      (k + 1)).2.2.2.1 k ≠ none) :
    prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D (k + 1) =
      prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D k ∪
        schedulePiece κ b jumps x l D k := by
  obtain ⟨cθ, hcθ⟩ := Option.ne_none_iff_exists'.1 hlaunch
  obtain ⟨_, hr, _⟩ := eq_launch_of_launches ⟨x, true, scheduleProgram 0 l⟩ D hcθ
  have ht : instrTime (x, true, scheduleProgram 0 l) k = schedDelta 0 l k := by
    unfold instrTime
    rw [isFlowProg_scheduleProgram 0 l k hk]
  unfold prefixPhysSet schedulePiece
  simp only []
  rw [hr, ht, pieces_launch, arcs_launch]
  ext z
  simp only [mem_union, mem_iUnion, List.mem_append, List.mem_singleton, exists_prop]
  constructor
  · rintro ((hroot | ⟨p, hp | rfl, hz⟩) | harc)
    · exact Or.inl (Or.inl (Or.inl hroot))
    · exact Or.inl (Or.inl (Or.inr ⟨p, hp, hz⟩))
    · exact Or.inr hz
    · exact Or.inl (Or.inr harc)
  · rintro (((hroot | ⟨p, hp, hz⟩) | harc) | hnew)
    · exact Or.inl (Or.inl hroot)
    · exact Or.inl (Or.inr ⟨p, Or.inl hp, hz⟩)
    · exact Or.inr harc
    · exact Or.inl (Or.inr ⟨_, Or.inr rfl, hnew⟩)

/-- Without a launch a schedule adds no physical points, including after a threshold. -/
theorem prefixPhysSet_schedule_succ_of_noLaunch {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hk : k < (scheduleProgram 0 l).length)
    (hlaunch : (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D
      (k + 1)).2.2.2.1 k = none) :
    prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D (k + 1) =
      prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D k := by
  have hi := isFlowProg_scheduleProgram 0 l k hk
  have hr : ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D (k + 1) =
      ExplState.flowStep κ b true
        (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D k) k (D k)
        (schedAngle l k) (schedDelta 0 l k) := by
    rw [run_succ, hi]
    rfl
  rcases flowStep_trichotomy (κ := κ) (b := b) true
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D k) k (D k)
      (schedAngle l k) (schedDelta 0 l k) with he | he | he
  · simp only [prefixPhysSet, hr, he]
  · simp only [prefixPhysSet, hr, he, setDead]
  · have hn := hlaunch
    rw [hr, he, launches_launch, Function.update_self] at hn
    cases hn

/-- The missing one-piece comparison in SB4: if the retained schedule is on the
permitted side, every actual next launch is on that side too. This is an unproved
hypothesis, not a source theorem or a provider. -/
def ScheduleStepAvoidance {Ω : Type u} [MeasurableSpace Ω]
    (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (S : Ω → Set ℂ) : Prop :=
  ∀ k < (scheduleProgram 0 l).length,
    (∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅) →
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k ≠ none →
      schedulePiece κ b jumps x l
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅

/-- Finite induction consumes the one-piece comparison without dropping old pieces
or finite terminal endpoints. No measurability of the pathwise avoidance event is needed. -/
theorem schedule_avoids_of_step {Ω : Type u} [MeasurableSpace Ω]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {P : Measure Ω}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {S : Ω → Set ℂ}
    (hroot : ∀ᵐ ω ∂P, (x : ℂ) ∉ S ω)
    (hstep : ScheduleStepAvoidance κ b jumps P E x l S) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) ∩ S ω = ∅ := by
  have hind : ∀ k ≤ (scheduleProgram 0 l).length, ∀ᵐ ω ∂P,
      prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅ := by
    intro k
    induction k with
    | zero =>
      intro _
      filter_upwards [hroot] with ω hω
      simpa only [prefixPhysSet, ExplState.run, List.take_zero, List.foldl_nil,
        ExplState.init, List.not_mem_nil, iUnion_of_empty, iUnion_empty, union_empty] using
        (singleton_inter_eq_empty.2 hω)
    | succ k ih =>
      intro hk
      have hk' : k < (scheduleProgram 0 l).length := Nat.lt_of_succ_le hk
      have hprev := ih hk'.le
      filter_upwards [hprev, hstep k hk' hprev] with ω hω hn
      by_cases hl : (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
          (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k = none
      · rw [prefixPhysSet_schedule_succ_of_noLaunch hk' hl]
        exact hω
      · rw [prefixPhysSet_schedule_succ_of_launch hk' hl,
          union_inter_distrib_right, hω, hn hl, empty_union]
  exact hind _ le_rfl

end InteractingSLE.Theorem14.SB
