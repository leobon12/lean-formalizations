/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwRec

/-!
# SB2(2): the upper right record is at most `R` (item 4a, deterministic)

Packet PROVE-SB2-LIFTSET (round 17).

* `upper_launch_le`: before a launch of the upper schedule every instruction launched a piece stopped at an interior
  tip;
* **`upper_rec_le`**: along the upper schedule run, with the state invariant at each launch and whole traces of the
  launched pieces, the right record at a launch is at most every bound `R ≥ 0` of the real points of the prefix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.StagedLaw Exist.Staged Restart GW1W Lh

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₀ : ℝ} {l : List (ℝ × ℝ≥0)} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **Before a launch of the upper schedule every instruction launched a tip-stopped piece.** -/
theorem upper_launch_le :
    ∀ k : ℕ, (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D (k + 1)).2.2.2.1 k ≠ none →
      ∀ j < k, (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D (j + 1)).2.2.2.1 j ≠ none ∧
        instrTime (Lu.upperSpec x₀ l) j ≠ ⊤ ∧ instrTime (Lu.upperSpec x₀ l) j < (D j).2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hl j hj
    have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le j) hj
    obtain ⟨hl', htop, hlt⟩ := upper_launch_prev (D := D) hk hl
    have hk' : k - 1 + 1 = k := by omega
    rcases eq_or_lt_of_le (show j ≤ k - 1 by omega) with rfl | hjk
    · exact ⟨hl', htop, hlt⟩
    · exact ih (k - 1) (by omega) hl' j hjk

/-- **The upper right record at a launch is at most every bound `R ≥ 0` of the prefix's real points.** -/
theorem upper_rec_le (hx₀ : x₀ ≤ 0) (hregD : ∀ j, IsRegularDriver (D j))
    (hreg : ∀ j c θ', (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (D j).1 (min (instrTime (Lu.upperSpec x₀ l) j) (D j).2))
    (hfull : ∀ j, (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D (j + 1)).2.2.2.1 j ≠ none →
      GW1P.PieceRegular (D j).1 (D j).2)
    (hUS : ∀ j, (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D (j + 1)).2.2.2.1 j ≠ none →
      UState x₀ (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D j))
    {k : ℕ} (hk : (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D (k + 1)).2.2.2.1 k ≠ none) {R : ℝ} (hR0 : 0 ≤ R)
    (hRpre : ∀ y : ℝ, (y : ℂ) ∈ SB.prefixPhysSet κ b jumps (Lu.upperSpec x₀ l) D k → y ≤ R) :
    stRecR (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D k) ≤ R := by
  have hle := upper_launch_le (D := D) k hk
  suffices H : ∀ j, j ≤ k → stRecR (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D j) ≤ R from H k le_rfl
  intro j
  induction j with
  | zero =>
    intro _
    show x₀ ≤ R
    linarith
  | succ j ih =>
    intro hjk
    have hjk' : j < k := by omega
    obtain ⟨hlj, htop, hlt⟩ := hle j hjk'
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlj
    obtain ⟨-, hrun, -⟩ := eq_launch_of_launches _ D hcθ
    have hnot := Lx.stStatus_ne_done_of_launches _ D hcθ
    have hUj := hUS j hlj
    have hroot : (Lu.upperSpec x₀ l).1 ≤ stRecR (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D j) := hUj.2.2.2.2.2.1
    obtain ⟨g, hgc, hgi, hginv⟩ := ginv_of_run (Lu.upperSpec x₀ l) D hreg j hnot hUj hroot
    rw [hrun]
    refine rec_le_of_launch hUj j θ (hregD j) htop hlt (hfull j hlj) hgc hgi hginv (ih hjk'.le) fun x hx => ?_
    refine hRpre x (WalkIntRunChron.prefixPhysSet_mono (κ := κ) (b := b) (jumps := jumps) _ D hjk ?_)
    refine Or.inl (Or.inr ?_)
    simp only [mem_iUnion, exists_prop]
    refine ⟨(stChart (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D j),
      fun r : ℝ≥0 => (D j).1 (min (r : ℝ≥0∞) (min (instrTime (Lu.upperSpec x₀ l) j) (D j).2)).toNNReal,
      min (instrTime (Lu.upperSpec x₀ l) j) (D j).2), ?_, hx⟩
    rw [hrun, CounterflowRange.pieces_launch]
    exact List.mem_append_right _ (List.mem_singleton_self _)

end InteractingSLE.Theorem14.SB.Lk
