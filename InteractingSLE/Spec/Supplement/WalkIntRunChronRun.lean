/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkChainRun

/-!
# Chronological histories at every actual boundary-run stage

Export the live invariant of the existing terminal-chain construction.
All step arguments reuse its proved launch and connector lemmas. A finite
dead ending is allowed; terminal successful completion is not required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1X GW1Bookkeep Exist Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool}
  {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- Every actual boundary-run stage has a chronological finite history
or its completed terminal representation. No final-completion premise. -/
theorem stateRepresented_run
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))))
    (hC : WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)
    (n : ℕ) : StateRepresented 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
  let spec := boundaryWalkSpec b jumps θ right
  induction n with
  | zero => exact stateRepresented_init 0
  | succ n ih =>
    by_cases hdone : stStatus
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) = stDone
    · have heq : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1) =
          ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n := by
        rw [run_succ]
        cases hk : spec.2.2[n]? with
        | none => rfl
        | some a =>
          change ExplState.step κ b jumps false D
            (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (a, n) =
              ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n
          rcases a with ⟨a, t⟩ | r | ⟨v, r⟩
          · exact isTerminal_flowStep (Or.inl hdone) n (D n) a t
          · exact contStep_of_done hdone none r
          · exact contStep_of_done hdone (some v) r
      rw [heq]
      exact ih
    · have hHist : ArcHistory (0 : ℂ)
          (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n))
          (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) : ℂ) := by
        rcases ih with ⟨hd, _⟩ | ⟨_, hh⟩
        · exact False.elim (hdone hd)
        · exact hh
      cases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
          (n + 1)).2.2.2.1 n with
      | some p =>
        obtain ⟨c, θ'⟩ := p
        have hn : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
            (n + 1)).2.2.2.1 n ≠ none := by
          rw [hl]
          exact Option.some_ne_none _
        have heq := GW1W.launch_walk hn
        have hpiece := hP n c θ' hl hHist.endpoint_mem
        obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hn
        have htime : instrTime spec n = ⊤ := by
          simp only [spec, instrTime, GW1Conn.getElem?_boundaryWalkSpec, hlen, hev, ↓reduceIte]
        obtain ⟨_, _, hc⟩ := eq_launch_of_launches spec D hl
        rw [htime, min_top_left, hc, heq] at hpiece
        rw [heq]
        exact stateRepresented_launch hHist n (D n) θ hpiece
      | none =>
        by_cases hlen : n < spec.2.2.length
        · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
          · have heq := GW1W.run_succ_walk_flow (κ := κ) (D := D) hlen hev
            have hnl := hl
            rw [heq] at hnl
            rw [heq, GW1W.flowStep_eq_self_of_noLaunch _ _ _ _ _ hnl]
            exact ih
          · have heq := GW1W.run_succ_walk_cont (κ := κ) (D := D) hlen hodd
            rcases contStep_none_cases (κ := κ) b jumps
              (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) right
              with hs | hs | ⟨r, x, hd, hs⟩ | ⟨r, hs⟩
            · rw [heq, hs]
              exact ih
            · rw [heq, hs]
              refine Or.inr ⟨?_, hHist⟩
              intro hf
              cases hf
            · rw [heq, hs]
              exact stateRepresented_moveAlong hHist r x true hd ((hC n).1 r x (heq.trans hs))
            · rw [heq, hs]
              exact stateRepresented_moveToEnd hHist r ((hC n).2 r (heq.trans hs))
        · have heq : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1) =
          ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n := by
            rw [run_succ, GW1Conn.getElem?_boundaryWalkSpec, ite_eq_right hlen]
          rw [heq]
          exact ih

end InteractingSLE.Theorem14.WalkIntRunChron
