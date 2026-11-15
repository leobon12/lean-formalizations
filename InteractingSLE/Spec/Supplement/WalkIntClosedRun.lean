/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFillRetained

/-!
# Physical hulls after completed finite launches

The current run chart already has its normalized physical hull model.
Unless an infinite piece has completed the run, domain avoidance and the
existing frontier theorem identify that hull with the whole recorded
ordinary support in H, including the endpoint of a finite piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntClosed

open WalkBdry WalkIntCanon Exist.StagedLaw

/-- A finite launch never has the infinite-completion status. Threshold
and dead statuses are allowed; no successful-continuation premise is needed. -/
theorem status_launch_ne_done (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (h : min t D.2 ≠ ⊤) :
    stStatus (ExplState.launch s k D θ t) ≠ stDone := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  simp only [h, ↓reduceIte]
  split_ifs <;> try (intro heq; cases heq)
  rcases status with _ | _ | _ | _ | _ | _ <;> intro heq <;> cases heq

/-- The hull of a non-completed run chart is the filling of the actual
ordinary set. This includes a finite launch stopped at its full lifetime. -/
theorem hull_eq_fillH_wsetOf_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (w : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps w D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime w k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps w D n) ≠ stDone)
    (M : HullModel (stChart (ExplState.run κ b jumps w D n))) :
    M.hull = fillH (wsetOf (ExplState.run κ b jumps w D n)) := by
  have hdis := (WalkSide.disjoint_dom_or_done w D hreg n).resolve_left hnot
  symm
  apply WalkIntFill.fillH_eq_of_frontier_subset M.isHull
  · intro z hz
    by_contra hzK
    have hzdom : z ∈ (stChart (ExplState.run κ b jumps w D n)).dom := by
      change z ∈ ((stChart (ExplState.run κ b jumps w D n)).dom : Set ℂ)
      rw [M.dom_eq]
      exact ⟨hz.2, hzK⟩
    exact Set.disjoint_left.1 hdis hzdom hz.1
  · rintro z ⟨hzfr, hzH⟩
    rw [← M.dom_eq, (stChart (ExplState.run κ b jumps w D n)).dom.isOpen.frontier_eq] at hzfr
    exact subset_closure (WalkLeaf.mem_stageSet_of_frontier w
      (fun k (_ : Unit) => D k) () hreg n z hzH hzfr.1 hzfr.2)

end InteractingSLE.Theorem14.WalkIntClosed
