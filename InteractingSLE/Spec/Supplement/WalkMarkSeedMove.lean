/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMarkSeedLocal

/-! # A completed connector selects an untouched exterior restart mark -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkMarkSeed

open Exist.Staged Exist.StagedLaw GW2aConn

/-- At a marked endpoint of a moved connector, its literal move has its
`atMark` flag set. -/
theorem atMark_of_moveAlong {s : ExplState} {r m : Bool} {w : ℝ}
    (hs : ∃ r', stStatus (ExplState.moveAlong s r w m) = GW1W.stArcM r') : m = true := by
  obtain ⟨r', hs⟩ := hs
  rw [stStatus_moveAlong] at hs
  have he : (r, m) = (r', true) := by
    simpa only [GW1W.stArcM, Sum.inr.injEq, Sum.inl.injEq] using hs
  exact congrArg Prod.snd he

/-- A complete connector that leaves a nonterminal arc mark moves beyond
the old record on its actual side. The side may differ from the preference. -/
theorem completed_connector_move {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (s : ExplState) (pref : Bool) (hOld : ∀ r, stStatus s ≠ GW1W.stArcM r)
    (hArc : ∃ r, stStatus (ExplState.contStep κ b jumps s none pref) = GW1W.stArcM r)
    (hLive : ¬ IsTerminal (ExplState.contStep κ b jumps s none pref))
    (hR : RStart κ b s → stPt s = stRecR s) (hL : LStart κ b s → stPt s = stRecL s) :
    ∃ (r : Bool) (w : ℝ), ExplState.contStep κ b jumps s none pref =
      ExplState.moveAlong s r w true ∧ (stRecR s < w ∨ w < stRecL s) := by
  rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s none pref with
    he | he | ⟨r, x, m, he⟩ | ⟨r, he⟩
  · obtain ⟨r, hs⟩ := hArc
    exact (hOld r (he ▸ hs)).elim
  · exact (hLive (by rw [he]; cases s; exact Or.inr rfl)).elim
  · have hne : (ExplState.contStep κ b jumps s none pref).2.1 ≠ s.2.1 := by
      rw [he]; exact GW2aConn.arcs_moveAlong s r x m
    rcases contStep_arc_cases s none pref hne with ⟨hstart, hb⟩ | ⟨hstart, hb⟩
    · rcases rMove_rBranch (κ := κ) (b := b) (jumps := jumps) s none with
        ⟨w, mk, hm, hw, -⟩ | ⟨hm, -⟩
      · have he' := hb.trans hm
        have hmk : mk = true := atMark_of_moveAlong (by rwa [← he'])
        rw [hmk] at he'
        exact ⟨true, w, he', Or.inl (by rw [← hR hstart]; exact hw)⟩
      · exact (hLive (by rw [hb, hm]; exact isTerminal_moveToEnd' s true)).elim
    · rcases lMove_lBranch (κ := κ) (b := b) (jumps := jumps) s none with
        ⟨w, mk, hm, hw, -⟩ | ⟨hm, -⟩
      · have he' := hb.trans hm
        have hmk : mk = true := atMark_of_moveAlong (by rwa [← he'])
        rw [hmk] at he'
        exact ⟨false, w, he', Or.inr (by rw [← hL hstart]; exact hw)⟩
      · exact (hLive (by rw [hb, hm]; exact isTerminal_moveToEnd' s false)).elim
  · exact (hLive (by rw [he]; exact isTerminal_moveToEnd' s r)).elim

end InteractingSLE.Theorem14.WalkMarkSeed
