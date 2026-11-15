/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkFreshRecordRun

/-! # A surviving later round selects a point outside the earlier records -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkFreshRecord

open Exist.Staged Exist.StagedLaw GW1WalkFinish WalkSeedFinite WalkLaterSeed
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- A complete connector from either threshold either terminates or selects
a point beyond that side's current record. The preferred side is irrelevant. -/
theorem outside_records_contStep {s : ExplState} {r : Bool}
    (hs : stStatus s = stThr (some r))
    (hp : stPt s = if r then stRecR s else stRecL s) (pref : Bool)
    (hT : ¬ IsTerminal (ExplState.contStep κ b jumps s none pref)) :
    stRecR s < stPt (ExplState.contStep κ b jumps s none pref) ∨
      stPt (ExplState.contStep κ b jumps s none pref) < stRecL s := by
  classical
  cases r
  · change stPt s = stRecL s at hp
    rw [GW1W.contStep_thr_false b jumps s hs pref] at hT ⊢
    split_ifs at hT ⊢ with hC
    · right
      rw [GW1W.stPt_moveAlong, ← hp]
      exact (Finset.mem_filter.1 (Finset.max'_mem _ hC)).2.1
    · exact (hT (GW2aConn.isTerminal_moveToEnd' s false)).elim
  · change stPt s = stRecR s at hp
    rw [GW1W.contStep_thr_true b jumps s hs pref] at hT ⊢
    dsimp only at hT ⊢
    split_ifs at hT ⊢ with hC
    · left
      rw [GW1W.stPt_moveAlong, ← hp]
      exact (Finset.mem_filter.1 (Finset.min'_mem _ hC)).2.1
    · exact (hT (GW2aConn.isTerminal_moveToEnd' s true)).elim

/-- A zero-lifetime actual later launch cannot leave an admissible restart
round: its following continuation kills the state. -/
theorem terminal_after_later_zero (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk0 : 0 < k)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none)
    (hklen : k + 1 < (boundaryWalkSpec b jumps θ right).2.2.length) (hz : (D k).2 = 0) :
    IsTerminal (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 2)) := by
  let w := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps w D
  change IsTerminal (R (k + 2))
  obtain ⟨⟨r, hs, -⟩, ha⟩ := laterLaunch_mark_seed D hk0 hk
  obtain ⟨hst, hpt, hang⟩ := GW1W.launch_zero (s := R k) (k := k) (θ := θ) hz (by
    change stStatus (R k) = GW1W.stArcM r at hs
    rw [hs]; intro h; cases h)
  rw [← GW1W.launch_walk hk] at hst hpt hang
  have hc : R (k + 2) = ExplState.contStep κ b jumps (R (k + 1)) none right :=
    GW1W.run_succ_walk_cont hklen (by have he := (GW1W.even_of_launches_walk hk).1; omega)
  rw [hc]
  right
  exact GW1W.contStep_thr_none_dead b jumps (R (k + 1)) hst
    (by rw [hang, hpt]; exact ha.1) (by rw [hang, hpt]; exact ha.2) right

/-- If the next positive round is still admissible and nonterminal, its
point lies outside both records at the current round. Zero lifetimes are
handled by terminality, rather than excluded as an extra hypothesis. -/
theorem round_outside_records (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hG : LaunchRecordData κ b jumps θ right D) {n : ℕ}
    (hn : n ≤ (jumpSet b jumps).card) (hn0 : 0 < n)
    (hNext : ¬ SeedBlocked κ b θ
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * (n + 1)))) :
    let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
    stRecR (R (2 * n)) < stPt (R (2 * (n + 1))) ∨
      stPt (R (2 * (n + 1))) < stRecL (R (2 * n)) := by
  let w := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps w D
  have hCur : ¬ SeedBlocked κ b θ (R (2 * n)) := fun hs =>
    hNext (seedBlocked_round_succ D hn hn0 hs)
  have hNotT : ¬ IsTerminal (R (2 * (n + 1))) := fun ht => hNext (Or.inl ht)
  have hc : R (2 * (n + 1)) = ExplState.contStep κ b jumps (R (2 * n + 1)) none right := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    exact GW1W.run_succ_walk_cont (by rw [boundaryWalk_length]; omega) (by omega)
  have hf : R (2 * n + 1) = ExplState.flowStep κ b false (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ :=
    GW1W.run_succ_walk_flow (by rw [boundaryWalk_length]; omega) (by omega)
  obtain ⟨r, hs, -⟩ := (terminal_or_mark_at_round (κ := κ) (θ := θ) (right := right) D
    (by omega : n ≤ (jumpSet b jumps).card + 1) hn0).resolve_left (fun ht => hCur (Or.inl ht))
  have ha : ExplState.IsAdmissibleSeed κ (ExplState.heights κ b (R (2 * n))).1
      (ExplState.heights κ b (R (2 * n))).2 θ := by
    by_contra hbad
    exact hCur (Or.inr hbad)
  have hl : (R (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
    rw [hf, flowStep_eq_byStatus]
    apply (launches_flowByStatus_ne_none_iff false _ _ (launches_run_of_le w D le_rfl) _ θ ⊤).2
    change stStatus (R (2 * n)) = GW1W.stArcM r at hs
    rw [hs]
    exact ⟨rfl, ha⟩
  have he := GW1W.launch_walk hl
  change R (2 * n + 1) = _ at he
  have hPost : ¬ IsTerminal (R (2 * n + 1)) := fun ht =>
    hNotT (isTerminal_run_of_le w D ht (2 * (n + 1)) (by omega)).1
  have hfin : (D (2 * n)).2 ≠ ⊤ := by
    intro ht
    apply hPost
    rw [he]
    exact isTerminal_launch_of_top _ _ _ _ _ (by rw [ht]; rfl)
  have hz : (D (2 * n)).2 ≠ 0 := by
    intro hz
    have ht := terminal_after_later_zero D (by omega : 0 < 2 * n) hl
      (by rw [boundaryWalk_length]; omega) hz
    change IsTerminal (R (2 * n + 2)) at ht
    rw [show 2 * n + 2 = 2 * (n + 1) by omega] at ht
    exact hNotT ht
  have hout : stRecR (R (2 * n + 1)) < stPt (R (2 * (n + 1))) ∨
      stPt (R (2 * (n + 1))) < stRecL (R (2 * n + 1)) := by
    rcases GW1W.launch_status_of_pos (s := R (2 * n)) (k := 2 * n) (θ := θ) hfin hz with hR | hL | hD
    · have hp := (GW1W.launch_thr_true hfin hR).2.2.1
      rw [← he] at hR hp
      rw [hc]
      exact outside_records_contStep hR hp right (by rwa [← hc])
    · have hp := (GW1W.launch_thr_false hfin hL).2.2.1
      rw [← he] at hL hp
      rw [hc]
      exact outside_records_contStep hL hp right (by rwa [← hc])
    · exact (hPost (Or.inr (by rwa [he]))).elim
  have hg := recordsGrow_run D hG (m := 2 * n) (n := 2 * n + 1) (by omega)
  exact hout.imp (fun h => hg.2.trans_lt h) (fun h => h.trans_le hg.1)

end InteractingSLE.Theorem14.WalkFreshRecord
