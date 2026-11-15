/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkCapBlockMain

/-!
# Original restart marks without a fixed direction

Packet PROVE-T14-WALKSIDE2. These deterministic invariants apply to arbitrary
drivers. A complete continuation either stops or selects an original mark;
an inadmissible seed at such a mark remains blocked in subsequent rounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkSeedFinite

open Exist.Staged Exist.StagedLaw GW1WalkFinish WalkCapBlock
open PiecewiseConstantBoundaryData (jumpSet)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- An existing restart mark is the only way a complete continuation can keep
an unverified point. Every newly selected mark belongs to the original set. -/
theorem terminal_or_mark_contStep (s : ExplState) (pref : Bool)
    (hm : ∀ r, stStatus s = GW1W.stArcM r → stPt s ∈ jumpSet b jumps) :
    IsTerminal (ExplState.contStep κ b jumps s none pref) ∨
      stPt (ExplState.contStep κ b jumps s none pref) ∈ jumpSet b jumps := by
  classical
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, rR, rL⟩ := s
  unfold ExplState.contStep
  dsimp only
  repeat' first
    | exact Or.inl (Or.inl rfl)
    | exact Or.inl (Or.inr rfl)
    | exact Or.inr (hm _ rfl)
    | (right; rw [GW1W.stPt_moveAlong]; exact (Finset.mem_filter.1 (Finset.min'_mem _ _)).1)
    | (right; rw [GW1W.stPt_moveAlong]; exact (Finset.mem_filter.1 (Finset.max'_mem _ _)).1)
    | split

/-- A full-lifetime launch never leaves an existing restart-mark status. -/
theorem launch_top_ne_arcM (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (r : Bool) :
    stStatus (ExplState.launch s k D θ ⊤) ≠ GW1W.stArcM r := by
  by_cases ht : D.2 = ⊤
  · obtain ⟨-, -, -, -, hs, -⟩ := launch_eq_of_top s k D θ ⊤ (by rw [ht]; rfl)
    rw [hs]
    intro h
    cases h
  · obtain ⟨-, -, -, -, hs, -⟩ :=
      launch_eq_of_ne_top s k D θ ⊤ (by simpa only [min_top_left] using ht)
    rw [hs]
    simp only [lStatus, not_lt.2 (le_top : D.2 ≤ ⊤), ↓reduceIte]
    split_ifs
    · split <;> intro h <;> cases h
    all_goals intro h; cases h

/-- Every positive round starts at a terminal state or an original restart
mark. No monotonicity of the successive marks is assumed. -/
theorem terminal_or_mark_at_round {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (hn : n ≤ (jumpSet b jumps).card + 1) (hn0 : 0 < n) :
    let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
    IsTerminal (R (2 * n)) ∨
      (∃ r, stStatus (R (2 * n)) = GW1W.stArcM r ∧ stPt (R (2 * n)) ∈ jumpSet b jumps) := by
  let w := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps w D
  have hInv : ∀ n ≤ (jumpSet b jumps).card + 1,
      ∀ r, stStatus (R (2 * n)) = GW1W.stArcM r → stPt (R (2 * n)) ∈ jumpSet b jumps := by
    intro n
    induction n with
    | zero => intro _ r hr; cases hr
    | succ n ih =>
      intro hn r hr
      have hlt : 2 * n + 1 < w.2.2.length := by rw [boundaryWalk_length]; omega
      have hf : R (2 * n + 1) = ExplState.flowStep κ b false (R (2 * n))
          (2 * n) (D (2 * n)) θ ⊤ :=
        GW1W.run_succ_walk_flow (by rw [boundaryWalk_length]; omega) (by omega)
      have hc : R (2 * (n + 1)) = ExplState.contStep κ b jumps (R (2 * n + 1)) none right := by
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
        exact GW1W.run_succ_walk_cont hlt (by omega)
      have hm : ∀ r, stStatus (R (2 * n + 1)) = GW1W.stArcM r →
          stPt (R (2 * n + 1)) ∈ jumpSet b jumps := by
        rw [hf]
        rcases GW1W.flowStep_false_cases (κ := κ) (b := b)
          (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ with he | he
        · rw [he]
          exact ih (by omega)
        · rw [he]
          intro r hs
          exact (launch_top_ne_arcM _ _ _ _ _ hs).elim
      rcases terminal_or_mark_contStep (R (2 * n + 1)) right hm with ht | hm
      · rw [← hc] at ht
        change stStatus (R (2 * (n + 1))) = stDone ∨
          stStatus (R (2 * (n + 1))) = stDead at ht
        rcases ht with hs | hs <;> rw [hr] at hs <;> cases hs
      · rwa [← hc] at hm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hc : R (2 * (m + 1)) = ExplState.contStep κ b jumps (R (2 * m + 1)) none right := by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
    exact GW1W.run_succ_walk_cont (by rw [boundaryWalk_length]; omega) (by omega)
  rcases GW1W.status_contStep (κ := κ) (b := b) (jumps := jumps)
    (R (2 * m + 1)) right with ⟨r, hs⟩ | hs | hs
  · right
    rw [← hc] at hs
    exact ⟨r, hs, hInv (m + 1) hn r hs⟩
  · rw [← hc] at hs
    exact Or.inl (Or.inl hs)
  · rw [← hc] at hs
    exact Or.inl (Or.inr hs)

end InteractingSLE.Theorem14.WalkSeedFinite
