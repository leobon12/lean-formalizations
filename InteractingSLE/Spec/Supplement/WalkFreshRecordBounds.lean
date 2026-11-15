/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkFreshRecord

/-! # The current point lies between the two records -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkFreshRecord

open Exist.Staged Exist.StagedLaw GW2aConn

def RecordBounds (s : ExplState) : Prop := stRecL s ≤ stPt s ∧ stPt s ≤ stRecR s

theorem recordBounds_moveAlong {s : ExplState} (h : RecordBounds s) (r : Bool) (x : ℝ) (m : Bool)
    (hx : if r then stPt s ≤ x else x ≤ stPt s) : RecordBounds (ExplState.moveAlong s r x m) := by
  cases r
  · exact ⟨by rw [GW1W.stPt_moveAlong, GW1W.stRecL_moveAlong_false]; exact min_le_right _ _,
      by rw [GW1W.stPt_moveAlong, GW1W.stRecR_moveAlong_false]; exact hx.trans h.2⟩
  · exact ⟨by rw [GW1W.stPt_moveAlong, stRecL_moveAlong_true]; exact h.1.trans hx,
      by rw [GW1W.stPt_moveAlong, GW1W.stRecR_moveAlong_true]; exact le_max_right _ _⟩

theorem recordBounds_moveToEnd {s : ExplState} (h : RecordBounds s) (r : Bool) :
    RecordBounds (ExplState.moveToEnd s r) := by
  cases s
  cases r <;> exact h

theorem recordBounds_rBranch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {s : ExplState}
    (h : RecordBounds s) (v : Option ℝ) : RecordBounds (rBranch κ b jumps s v) := by
  rcases rMove_rBranch (κ := κ) (b := b) (jumps := jumps) s v with ⟨x, m, he, hx, -⟩ | ⟨he, -⟩
  · rw [he]; exact recordBounds_moveAlong h true x m hx.le
  · rw [he]; exact recordBounds_moveToEnd h true

theorem recordBounds_lBranch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {s : ExplState}
    (h : RecordBounds s) (v : Option ℝ) : RecordBounds (lBranch κ b jumps s v) := by
  rcases lMove_lBranch (κ := κ) (b := b) (jumps := jumps) s v with ⟨x, m, he, hx, -⟩ | ⟨he, -⟩
  · rw [he]; exact recordBounds_moveAlong h false x m hx.le
  · rw [he]; exact recordBounds_moveToEnd h false

/-- Every continuation preserves the interval bound on the current point. -/
theorem recordBounds_contStep {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {s : ExplState}
    (h : RecordBounds s) (v : Option ℝ) (pref : Bool) :
    RecordBounds (ExplState.contStep κ b jumps s v pref) := by
  rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s v pref with he | he | ⟨r, x, m, he⟩ | ⟨r, he⟩
  · rwa [he]
  · rw [he]; cases s; exact h
  · have hne : (ExplState.contStep κ b jumps s v pref).2.1 ≠ s.2.1 := by
      rw [he]
      exact GW2aConn.arcs_moveAlong s r x m
    rcases contStep_arc_cases s v pref hne with ⟨-, hr⟩ | ⟨-, hl⟩
    · rw [hr]; exact recordBounds_rBranch h v
    · rw [hl]; exact recordBounds_lBranch h v
  · rw [he]; exact recordBounds_moveToEnd h r

/-- At a launch, the point is unchanged or becomes one of the new records.
Expansion of the records therefore suffices to preserve its interval bound. -/
theorem recordBounds_launch {s : ExplState} (h : RecordBounds s) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (hG : RecordsGrow s (ExplState.launch s k D θ ⊤)) :
    RecordBounds (ExplState.launch s k D θ ⊤) := by
  by_cases ht : D.2 = ⊤
  · obtain ⟨-, -, hR, hL, -, hp⟩ := launch_eq_of_top s k D θ ⊤ (by rw [ht]; rfl)
    exact ⟨by rw [hL, hp]; exact h.1, by rw [hR, hp]; exact h.2⟩
  · obtain ⟨-, -, hR, hL, -, hp⟩ := launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top ht)
    have horder := hG.1.trans ((h.1.trans h.2).trans hG.2)
    have hold : stRecL (ExplState.launch s k D θ ⊤) ≤ stPt s ∧
        stPt s ≤ stRecR (ExplState.launch s k D θ ⊤) := ⟨hG.1.trans h.1, h.2.trans hG.2⟩
    unfold RecordBounds
    rw [hp]
    unfold lPt
    split_ifs
    · exact hold
    · exact hold
    · rw [← hR]; exact ⟨horder, le_rfl⟩
    · rw [← hL]; exact ⟨le_rfl, horder⟩
    · exact hold

end InteractingSLE.Theorem14.WalkFreshRecord
