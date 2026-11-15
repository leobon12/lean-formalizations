/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkFinishChart

/-!
# GW1: finite completion from the local classification of an ordinary exit

This is a deterministic conditional helper. `ForwardExit` records the unresolved local
exit classification, including the zero-lifetime case. The number of rounds, the selected
original marks, their strict order, and persistence of completion are proved from the machine.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1WalkFinish

open Exist Exist.Staged Exist.StagedLaw GW1WalkChain
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- A finite ordinary exit permits continuation in the walk's prescribed direction.
At zero lifetime the direction is determined by the original one-sided heights. -/
def OutwardThreshold (κ : ℝ) (b : ℝ → ℝ) (right : Bool) (s : ExplState) : Prop :=
  stStatus s = stThr (some right) ∨
    (stStatus s = stThr none ∧ if right then
      rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ
    else -sleLambda κ < rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ∧
      sleLambda κ ≤ leftLim b (stPt s) + stAngle s * QuantumZipper.chiC κ)

/-- The local ordinary-stage classification needed below. This remains an explicit
mathematical input; it is stronger than saying that each piece is simple. -/
def ForwardExit (κ : ℝ) (b : ℝ → ℝ) (right : Bool) (s t : ExplState) : Prop :=
  stStatus t = stDone ∨
    (sideCoord right (stPt s) ≤ sideCoord right (stPt t) ∧ OutwardThreshold κ b right t)

theorem contStep_done_or_mark {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {right : Bool} {s : ExplState} (h : OutwardThreshold κ b right s) :
    stStatus (ExplState.contStep κ b jumps s none right) = stDone ∨
      (stPt (ExplState.contStep κ b jumps s none right) ∈ jumpSet b jumps ∧
        sideCoord right (stPt s) <
          sideCoord right (stPt (ExplState.contStep κ b jumps s none right))) := by
  classical
  cases right
  · have heq : ExplState.contStep κ b jumps s none false =
        if hC : (GW1W.restartSetL κ b jumps s).Nonempty then
          ExplState.moveAlong s false ((GW1W.restartSetL κ b jumps s).max' hC) true
        else ExplState.moveToEnd s false := by
      rcases h with h | ⟨h, hR, hL⟩
      · exact GW1W.contStep_thr_false b jumps s h false
      · exact GW1W.contStep_thr_none_left b jumps s h hR hL
    rw [heq]
    split_ifs with hC
    · have hm := Finset.mem_filter.1 ((GW1W.restartSetL κ b jumps s).max'_mem hC)
      exact Or.inr ⟨by rw [GW1W.stPt_moveAlong]; exact hm.1,
        by rw [GW1W.stPt_moveAlong]; exact neg_lt_neg hm.2.1⟩
    · exact Or.inl (by cases s; rfl)
  · have heq : ExplState.contStep κ b jumps s none true =
        if hC : (GW1W.restartSet κ b jumps s).Nonempty then
          ExplState.moveAlong s true ((GW1W.restartSet κ b jumps s).min' hC) true
        else ExplState.moveToEnd s true := by
      rcases h with h | ⟨h, hR⟩
      · exact GW1W.contStep_thr_true' b jumps s h
      · exact GW1W.contStep_thr_none_right b jumps s h hR
    rw [heq]
    split_ifs with hC
    · have hm := Finset.mem_filter.1 ((GW1W.restartSet κ b jumps s).min'_mem hC)
      exact Or.inr ⟨by rw [GW1W.stPt_moveAlong]; exact hm.1,
        by rw [GW1W.stPt_moveAlong]; exact hm.2.1⟩
    · exact Or.inl (by cases s; rfl)

theorem done_run_succ {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (h : stStatus (ExplState.run κ b jumps spec D k) = stDone) :
    ExplState.run κ b jumps spec D (k + 1) = ExplState.run κ b jumps spec D k := by
  rw [run_succ]
  cases hk : spec.2.2[k]? with
  | none => rfl
  | some ins =>
    rcases ins with ⟨θ, t⟩ | r | ⟨x, r⟩
    · exact isTerminal_flowStep (Or.inl h) _ _ _ _
    · exact contStep_of_done h none r
    · exact contStep_of_done h (some x) r

theorem boundaryWalk_length (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) :
    (boundaryWalkSpec b jumps θ right).2.2.length = 2 * ((jumpSet b jumps).card + 1) := by
  simp only [boundaryWalkSpec, List.length_flatten, List.map_replicate, List.sum_replicate,
    List.length_cons, List.length_nil, smul_eq_mul]
  ring

/-- A finite walk completes once its local ordinary exits are classified. In particular,
the counting argument does not require an additional termination hypothesis. -/
theorem walkCompletion_of_forwardExit {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {θ : ℝ} {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hExit : ∀ n ≤ (jumpSet b jumps).card,
      let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      stStatus (R (2 * n)) ≠ stDone →
        ForwardExit κ b right (R (2 * n)) (R (2 * n + 1))) :
    stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length) = stDone := by
  let spec := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps spec D
  have hdone : ∀ n, stStatus (R (2 * n)) = stDone →
      stStatus (R (2 * (n + 1))) = stDone := by
    intro n hn
    have h1 : R (2 * n + 1) = R (2 * n) := done_run_succ spec D hn
    have h2 : R (2 * n + 1 + 1) = R (2 * n + 1) :=
      done_run_succ spec D (by change stStatus (R (2 * n + 1)) = stDone; rw [h1]; exact hn)
    simpa only [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, h2, h1] using hn
  have hfinal := done_of_finite_progress (jumpSet b jumps) (fun n => stPt (R (2 * n)))
    (fun n => stStatus (R (2 * n)) = stDone) right hdone (fun n hn hnot => by
      have hcont : R (2 * (n + 1)) = ExplState.contStep κ b jumps (R (2 * n + 1)) none right := by
        have hlt : 2 * n + 1 < spec.2.2.length := by
          rw [boundaryWalk_length]; omega
        exact (show 2 * (n + 1) = 2 * n + 1 + 1 by omega) ▸
          GW1W.run_succ_walk_cont hlt (by omega)
      rcases hExit n hn hnot with hd | ⟨hle, hthr⟩
      · exact Or.inl (by rw [hcont, contStep_of_done hd]; exact hd)
      · rcases contStep_done_or_mark (jumps := jumps) hthr with hd | ⟨hmark, hlt⟩
        · exact Or.inl (by rw [hcont]; exact hd)
        · exact Or.inr ⟨by rw [hcont]; exact hmark, by rw [hcont]; exact hle.trans_lt hlt⟩)
  simpa only [boundaryWalk_length] using hfinal

end InteractingSLE.Theorem14.GW1WalkFinish
