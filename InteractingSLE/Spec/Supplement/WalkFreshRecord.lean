/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkRecordSeedMain

/-! # Two-sided record growth, without a fixed walk direction -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkFreshRecord

open Exist.Staged Exist.StagedLaw Restart

/-- Both ends of the recorded real interval expand. -/
def RecordsGrow (s t : ExplState) : Prop := stRecL t ≤ stRecL s ∧ stRecR s ≤ stRecR t

theorem RecordsGrow.refl (s : ExplState) : RecordsGrow s s := ⟨le_rfl, le_rfl⟩

theorem RecordsGrow.trans {s t v : ExplState} (h : RecordsGrow s t) (h' : RecordsGrow t v) :
    RecordsGrow s v := ⟨h'.1.trans h.1, h.2.trans h'.2⟩

/-- The general invariant supplies exactly the two good profiles needed for
record growth. No profile-smallness or seed admissibility is needed. -/
theorem recordsGrow_launch {θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {β : BoundaryWord} {s : ExplState} (hI : GW2aConn.GInv b jumps β s)
    (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (hreg : IsRegularDriver D)
    (hgood : D.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ D))) :
    RecordsGrow s (ExplState.launch s k D θ ⊤) := by
  by_cases ht : D.2 = ⊤
  · obtain ⟨-, -, hR, hL, -, -⟩ := launch_eq_of_top s k D θ ⊤ (by rw [ht]; rfl)
    exact ⟨le_of_eq hL, le_of_eq hR.symm⟩
  · obtain ⟨-, -, hR, hL, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top ht)
    constructor
    · rw [hL, lRecL_eq_newRec hI.1]
      exact neg_le.2 (le_newRec hI.2.2.1.1 (isRealFlow_stop hreg (hgood ht)).2)
    · rw [hR, lRecR_eq_newRec hI.1]
      exact le_newRec hI.2.1.1 (isRealFlow_stop hreg (hgood ht)).1

/-- A boundary continuation expands both records, even if it stops early,
kills the state, or follows the boundary to the target. -/
theorem recordsGrow_contStep {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (s : ExplState) (v : Option ℝ) (pref : Bool) :
    RecordsGrow s (ExplState.contStep κ b jumps s v pref) := by
  rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s v pref with h | h | ⟨r, x, m, h⟩ | ⟨r, h⟩
  · rw [h]; exact RecordsGrow.refl s
  · rw [h]; cases s; exact ⟨le_rfl, le_rfl⟩
  · rw [h]
    cases r
    · exact ⟨by rw [GW1W.stRecL_moveAlong_false]; exact min_le_left _ _,
        by rw [GW1W.stRecR_moveAlong_false]⟩
    · exact ⟨by rw [GW2aConn.stRecL_moveAlong_true],
        by rw [GW1W.stRecR_moveAlong_true]; exact le_max_left _ _⟩
  · rw [h]; cases s; cases r <;> exact ⟨le_rfl, le_rfl⟩

end InteractingSLE.Theorem14.WalkFreshRecord
