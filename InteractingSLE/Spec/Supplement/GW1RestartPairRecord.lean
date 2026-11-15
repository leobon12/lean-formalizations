/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartPairPiece

/-! # GW1: a positive finite threshold strictly advances the physical record -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1RestartPair

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish GW1WalkExit

/-- At a positive finite own threshold the new endpoint is strictly beyond the
previous seed. This supplies BW1's nonzero relative terminal point. -/
theorem point_lt_of_finite_positive {κ θ : ℝ} {b : ℝ → ℝ} {right : Bool}
    {s : ExplState} (hs : OwnProfile right s) (hr : OwnReady right s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hfin : D.2 ≠ ⊤) (hz : D.2 ≠ 0)
    (hC : ClassifiedExit κ b right s (ExplState.launch s k D θ ⊤)) :
    sideCoord right (stPt s) < sideCoord right (stPt (ExplState.launch s k D θ ⊤)) := by
  have hthr := own_threshold_of_pos_classified hfin hz hC
  have hpt := (profile_point_of_finite_classified hs hr k hreg hgood hfin hC).2
  rw [hr.point_eq, hpt]
  cases right
  · obtain ⟨-, ⟨x, hx, hhit⟩, -, -⟩ := GW1W.launch_thr_false hfin hthr
    obtain ⟨-, -, -, hrec, -, -⟩ :=
      launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)
    change -stRecL s < -stRecL (ExplState.launch s k D θ ⊤)
    rw [hrec, lRecL_eq_newRec hs.1, neg_neg]
    refine (neg_lt_neg hx).trans_le (le_csSup
      (bddAbove_dead hs.2.1 (isRealFlow_stop hreg hgood).2) (Or.inr ⟨neg_lt_neg hx, ?_⟩))
    have hh := (lHit_iff hs.1 ⊤ D x).1 hhit
    simpa only [GW1W.lProf_eq, neg_neg] using hh.2
  · obtain ⟨-, ⟨x, hx, hhit⟩, -, -⟩ := GW1W.launch_thr_true hfin hthr
    obtain ⟨-, -, hrec, -, -, -⟩ :=
      launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)
    change stRecR s < stRecR (ExplState.launch s k D θ ⊤)
    rw [hrec, lRecR_eq_newRec hs.1]
    exact hx.trans_le (le_csSup (bddAbove_dead hs.2.1 (isRealFlow_stop hreg hgood).1)
      (Or.inr ⟨hx, ((lHit_iff hs.1 ⊤ D x).1 hhit).2⟩))

/-- In particular a nonempty finite piece cannot end at its old seed. -/
theorem point_ne_of_finite_positive {κ θ : ℝ} {b : ℝ → ℝ} {right : Bool}
    {s : ExplState} (hs : OwnProfile right s) (hr : OwnReady right s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hfin : D.2 ≠ ⊤) (hz : D.2 ≠ 0)
    (hC : ClassifiedExit κ b right s (ExplState.launch s k D θ ⊤)) :
    stPt (ExplState.launch s k D θ ⊤) ≠ stPt s := by
  intro he
  have hlt := point_lt_of_finite_positive hs hr k hreg hgood hfin hz hC
  rw [he] at hlt
  exact lt_irrefl _ hlt

end InteractingSLE.Theorem14.GW1RestartPair
