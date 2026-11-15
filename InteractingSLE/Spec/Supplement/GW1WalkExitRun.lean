/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitRestart

/-! # GW1: no ordinary instruction is skipped at a selected restart mark -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish
open PiecewiseConstantBoundaryData (jumpSet)

theorem launch_at_even_of_launchReady {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (hn : n ≤ (jumpSet b jumps).card)
    (hready : LaunchReady κ b θ right
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n))) :
    ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n + 1) =
      ExplState.launch (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n))
        (2 * n) (D (2 * n)) θ ⊤ ∧
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n + 1)).2.2.2.1
      (2 * n) ≠ none := by
  have hr := GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps)
    (θ := θ) (right := right) (D := D) (k := 2 * n)
    (by rw [boundaryWalk_length]; omega) (by omega)
  rw [flowStep_of_launchReady hready] at hr
  refine ⟨hr, ?_⟩
  rw [hr, launches_launch, Function.update_self]
  exact Option.some_ne_none _

/-- The live round starts at the root or an admissible mark. Thus the classified-exit
law at actual launches also applies at every live ordinary instruction. -/
theorem forwardExit_at_rounds_of_classifiedExits {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hC : ∀ k,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none →
      ClassifiedExit κ b right
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))) :
    ∀ n ≤ (jumpSet b jumps).card,
      let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      stStatus (R (2 * n)) ≠ stDone →
        ForwardExit κ b right (R (2 * n)) (R (2 * n + 1)) := by
  let spec := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps spec D
  have hcont (n : ℕ) (hn : n ≤ (jumpSet b jumps).card) :
      R (2 * (n + 1)) = ExplState.contStep κ b jumps (R (2 * n + 1)) none right := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    apply GW1W.run_succ_walk_cont
    · rw [boundaryWalk_length]; omega
    · omega
  have hInv : ∀ n ≤ (jumpSet b jumps).card + 1,
      stStatus (R (2 * n)) = stDone ∨ LaunchReady κ b θ right (R (2 * n)) := by
    intro n
    induction n with
    | zero => intro _; exact Or.inr (Or.inl rfl)
    | succ n ih =>
      intro hn
      have hn' : n ≤ (jumpSet b jumps).card := by omega
      have hc := hcont n hn'
      rcases ih (by omega) with hd | hready
      · have hf : R (2 * n + 1) = R (2 * n) := done_run_succ spec D hd
        exact Or.inl (by rw [hc, hf, GW1WalkChain.contStep_of_done hd]; exact hd)
      · obtain ⟨hlaunch, hl⟩ := launch_at_even_of_launchReady D hn' hready
        change R (2 * n + 1) = ExplState.launch (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ at hlaunch
        have hclass := hC (2 * n) hl
        have hangle : stAngle (R (2 * n + 1)) = θ := by
          rw [hlaunch]
          exact angle_launch _ _ _ _
        rcases hclass.1 with hd | ⟨-, hOut⟩
        · exact Or.inl (by rw [hc, GW1WalkChain.contStep_of_done hd]; exact hd)
        · have hnot : stStatus (R (2 * n + 1)) ≠ stDone := by
            cases right <;> rcases hOut with h | ⟨h, -⟩ <;>
              rw [h] <;> intro he <;> cases he
          have hNext := contStep_launchReady_or_done hκ hb hOut (hclass.2 hnot) hangle
          rwa [← hc] at hNext
  intro n hn
  dsimp only
  intro hnot
  rcases hInv n (by omega) with hd | hready
  · exact False.elim (hnot hd)
  · exact (hC (2 * n) (launch_at_even_of_launchReady D hn hready).2).1

end InteractingSLE.Theorem14.GW1WalkExit
