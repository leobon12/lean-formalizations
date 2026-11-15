/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitRecords

/-! # GW1: the exterior profile and the current record at a finite exit -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol)

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish

def OwnReady (right : Bool) (s : ExplState) : Prop :=
  if right then GW1W.RReady s else GW1W.LReady s

theorem OwnProfile.isRealChart {right : Bool} {s : ExplState} (h : OwnProfile right s) :
    IsRealChart (stChart s) := by
  cases right <;> exact h.1

theorem OwnReady.point_eq {right : Bool} {s : ExplState} (h : OwnReady right s) :
    sideCoord right (stPt s) = outwardRecord right s := by
  cases right
  · exact congrArg Neg.neg h.2
  · exact h.2

theorem OwnReady.not_tip {right : Bool} {s : ExplState} (h : OwnReady right s) :
    stStatus s ≠ .inr (.inl ()) := by
  cases right <;> rcases h.1 with h | h <;> rw [h] <;> intro he <;> cases he

theorem outwardRecord_launch_zero {right : Bool} {s : ExplState} (hs : OwnProfile right s)
    (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (hreg : IsRegularDriver D) (hz : D.2 = 0) :
    outwardRecord right (ExplState.launch s k D θ ⊤) = outwardRecord right s := by
  have hfin : D.2 ≠ ⊤ := by rw [hz]; exact ENNReal.zero_ne_top
  have hT : stopTime ⊤ D = 0 := by simp only [stopTime, hz, min_zero,
    ENNReal.toNNReal_zero, NNReal.coe_zero]
  have hW0 := stopDrv_zero hreg ⊤
  cases right
  · obtain ⟨-, -, -, hrec, -, -⟩ :=
      launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)
    change -stRecL (ExplState.launch s k D θ ⊤) = -stRecL s
    rw [hrec, lRecL_eq_newRec hs.1, neg_neg]
    have he : {x : ℝ | -stRecL s < x ∧
        ¬ ∃ u, IsForwardSol (stopDrv ⊤ D) ((-lProf (stChart s) x : ℝ) : ℂ) 0 u} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx
      exact exists_isForwardSol_zero hW0 (neg_ne_zero.2 (hs.2.2.1 x hx).ne')
    simp only [newRec, hT, he, insert_empty_eq, csSup_singleton]
  · obtain ⟨-, -, hrec, -, -, -⟩ :=
      launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)
    change stRecR (ExplState.launch s k D θ ⊤) = stRecR s
    rw [hrec, lRecR_eq_newRec hs.1]
    have he : {x : ℝ | stRecR s < x ∧
        ¬ ∃ u, IsForwardSol (stopDrv ⊤ D) (rProf (stChart s) x : ℂ) 0 u} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx
      exact exists_isForwardSol_zero hW0 (hs.2.2.1 x hx).ne'
    simp only [newRec, hT, he, insert_empty_eq, csSup_singleton]

theorem own_threshold_of_pos_classified {κ θ : ℝ} {b : ℝ → ℝ} {right : Bool}
    {s : ExplState} {k : ℕ} {D : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hfin : D.2 ≠ ⊤) (hz : D.2 ≠ 0)
    (hC : ClassifiedExit κ b right s (ExplState.launch s k D θ ⊤)) :
    stStatus (ExplState.launch s k D θ ⊤) = stThr (some right) := by
  have hcases := GW1W.launch_status_of_pos (s := s) (k := k) (θ := θ) hfin hz
  rcases hC.1 with hd | ⟨-, ho⟩
  · rcases hcases with he | he | he <;> rw [he] at hd <;> cases hd
  · rcases ho with he | ⟨hn, -⟩
    · exact he
    · rcases hcases with he | he | he <;> rw [he] at hn <;> cases hn

theorem profile_point_of_finite_classified {κ θ : ℝ} {b : ℝ → ℝ} {right : Bool}
    {s : ExplState} (hs : OwnProfile right s) (hr : OwnReady right s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤)
    (hC : ClassifiedExit κ b right s (ExplState.launch s k D θ ⊤)) :
    OwnProfile right (ExplState.launch s k D θ ⊤) ∧
      sideCoord right (stPt (ExplState.launch s k D θ ⊤)) =
        outwardRecord right (ExplState.launch s k D θ ⊤) := by
  by_cases hz : D.2 = 0
  · have hp := (GW1W.launch_zero (k := k) (θ := θ) hz hr.not_tip).2.1
    have hpt : sideCoord right (stPt (ExplState.launch s k D θ ⊤)) =
        outwardRecord right (ExplState.launch s k D θ ⊤) := by
      rw [hp, outwardRecord_launch_zero hs k θ hreg hz]
      exact hr.point_eq
    refine ⟨?_, hpt⟩
    cases right
    · exact (GW1W.lProf_launch_zero hs k θ hreg hz).1
    · exact (GW1W.rProf_launch_zero hs k θ hreg hz).1
  have hthr := own_threshold_of_pos_classified hfin hz hC
  cases right
  · obtain ⟨-, hhit, hpt, -⟩ := GW1W.launch_thr_false hfin hthr
    exact ⟨(GW1W.lProf_launch hs k θ hreg hgood hfin hhit).1, congrArg Neg.neg hpt⟩
  · obtain ⟨-, hhit, hpt, -⟩ := GW1W.launch_thr_true hfin hthr
    exact ⟨(GW1W.rProf_launch hs k θ hreg hgood hfin hhit).1, hpt⟩

end InteractingSLE.Theorem14.GW1WalkExit
