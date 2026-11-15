/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LfStart

/-!
# SB2(2): the actual side of the arc start, including the angle and the low outward height

Packet PROVE-SB2-LIFTSET (round 6). Completes the actual-side fields of `ArcStartData` at the first stage carrying `R`
(`SB2LfStart`):

* `stAngle_moveAlong'`, `stAngle_moveToEnd'`, `stAngle_setDead'`; **`stAngle_run_walk`**: after the first instruction
  the current angle of a walk is the walk's angle (`angle` field);
* **`launched_of_thrTrue`**: a right threshold right after a flow instruction comes from a launch (a connector never
  leaves a right threshold in place);
* **`low_at_threshold`**: at an outward right threshold the original height just right of the current point is low —
  from GW1's stage data (`WalkStageData`: a classified exit that is not done has a low outward height,
  `BadOutwardHeight`) at `thr (some true)`, and from `OutwardThreshold` itself at `thr none`;
* **`arcStart_actual`**: with GW1's stage data, `AllowedSt` and `PtRec` at the connector stage, the fields `move`,
  `angle`, `pt`, `recLe`, the gap (or `R` is the restart mark), and `low` given the gap (`rightLim_add_le_of_gap`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- A move keeps the angle. -/
theorem stAngle_moveAlong' (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    stAngle (ExplState.moveAlong s r x m) = stAngle s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

/-- A move to the end keeps the angle. -/
theorem stAngle_moveToEnd' (s : ExplState) (r : Bool) : stAngle (ExplState.moveToEnd s r) = stAngle s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

/-- Marking dead keeps the angle. -/
theorem stAngle_setDead' (s : ExplState) : stAngle (setDead s) = stAngle s := rfl

/-- **The angle along a walk run**: after the first instruction the current angle is the walk's angle. -/
theorem stAngle_run_walk {right : Bool} :
    ∀ n, 1 ≤ n → stAngle (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) = θ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have hlen : 0 < (boundaryWalkSpec b jumps θ right).2.2.length := by
      simp only [boundaryWalkSpec, List.length_flatten, List.map_replicate, List.length_cons, List.length_nil,
        List.sum_replicate, smul_eq_mul]
      omega
    rw [GW1W.run_succ_walk_flow (κ := κ) (D := D) hlen (by norm_num), GW1Conn.run_zero]
    show stAngle (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤) = θ
    by_cases htop : (D 0).2 = ⊤
    · exact (launch_eq_of_top _ 0 (D 0) θ ⊤ (by rw [htop, min_self])).2.1
    · exact (launch_eq_of_ne_top _ 0 (D 0) θ ⊤ (by rw [min_eq_right le_top]; exact htop)).2.1
  | succ n hn ih =>
    set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n with hs
    by_cases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none
    · rw [GW1W.launch_walk hl]
      by_cases htop : (D n).2 = ⊤
      · exact (launch_eq_of_top s n (D n) θ ⊤ (by rw [htop, min_self])).2.1
      · exact (launch_eq_of_ne_top s n (D n) θ ⊤ (by rw [min_eq_right le_top]; exact htop)).2.1
    · push Not at hl
      by_cases hlen : n < (boundaryWalkSpec b jumps θ right).2.2.length
      · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
        · have heq := GW1W.run_succ_walk_flow (κ := κ) (D := D) hlen hev
          have hnl := hl
          rw [heq] at hnl
          rw [heq, GW1W.flowStep_eq_self_of_noLaunch _ _ _ _ _ hnl]
          exact ih
        · rw [GW1W.run_succ_walk_cont (κ := κ) (D := D) hlen hodd]
          rcases GW1WalkChain.contStep_none_cases (κ := κ) b jumps s right with e | e | ⟨r, x, -, e⟩ | ⟨r, e⟩
          · rw [e]; exact ih
          · rw [e, stAngle_setDead']; exact ih
          · rw [e, stAngle_moveAlong']; exact ih
          · rw [e, stAngle_moveToEnd']; exact ih
      · rw [show ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1) = s by
          rw [run_succ, GW1Conn.getElem?_boundaryWalkSpec, ite_eq_right hlen]]
        exact ih


/-- **A right threshold right after a flow instruction comes from a launch** (a connector never leaves a right
threshold in place). -/
theorem launched_of_thrTrue {n : ℕ} (hev : n % 2 = 0) (hlen : n < (boundaryWalkSpec b jumps θ true).2.2.length)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) = stThr (some true)) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none := by
  intro hl
  have heq := GW1W.run_succ_walk_flow (κ := κ) (D := D) hlen hev
  have hnl := hl
  rw [heq] at hnl
  rw [heq, GW1W.flowStep_eq_self_of_noLaunch _ _ _ _ _ hnl] at hst
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = .inl () := by
      simp [ExplState.run, ExplState.init]
    rw [this] at hst; cases hst
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m < (boundaryWalkSpec b jumps θ true).2.2.length := by omega
    rw [GW1W.run_succ_walk_cont (κ := κ) (D := D) hm (by omega)] at hst
    set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D m with hs
    rcases GW1WalkChain.contStep_none_cases (κ := κ) b jumps s true with e | e | ⟨r, x, -, e⟩ | ⟨r, e⟩
    · rw [e] at hst
      have e' := contStep_thr_true' (κ := κ) b jumps s hst
      rw [e] at e'
      split_ifs at e' with hC
      · have := congrArg (fun t : ExplState => t.2.1.length) e'
        simp only [moveAlong_arcs_true, List.length_append, List.length_singleton] at this
        omega
      · have := congrArg (fun t : ExplState => t.2.1.length) e'
        simp only [moveToEnd_arcs_true, List.length_append, List.length_singleton] at this
        omega
    · rw [e, stStatus_setDead] at hst; cases hst
    · rw [e, stStatus_moveAlong'] at hst; cases hst
    · rw [e, stStatus_moveToEnd''] at hst; cases hst

/-- **The low outward height at the threshold** (GW1's stage data: a classified exit that is not done has a low
outward height; at `thr none` the outward threshold carries it). -/
theorem low_at_threshold (hS : GW1WalkExit.WalkStageData κ b jumps θ true D) {o : ℕ} (ho : o % 2 = 0)
    (hlen : o < (boundaryWalkSpec b jumps θ true).2.2.length)
    (hthr : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) = stThr (some true) ∨
      (stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) = stThr none ∧
        rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))) +
          stAngle (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) * QuantumZipper.chiC κ ≤
          -sleLambda κ)) :
    rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))) +
      θ * QuantumZipper.chiC κ ≤ -sleLambda κ := by
  have hθ := stAngle_run_walk (κ := κ) (b := b) (jumps := jumps) (θ := θ) (D := D) (right := true) (o + 1)
    (by omega)
  have hlow' : rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))) +
      stAngle (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) * QuantumZipper.chiC κ ≤
      -sleLambda κ := by
    rcases hthr with h | ⟨-, hlow⟩
    · have hl := launched_of_thrTrue ho hlen h
      have hex := (hS o hl).2.2.2.2 (by rw [h]; intro e; cases e)
      simpa [GW1WalkExit.BadOutwardHeight] using hex
    · exact hlow
  rwa [hθ] at hlow'


/-- **The actual side of an arc start at the first stage adding `R`**: with GW1's stage data, `AllowedSt` and `PtRec`
at the connector stage `o + 1`, the fields `move`, `angle`, `pt`, `recLe` of `ArcStartData` hold, every restart mark
is beyond `R` or `R` is the mark, and given the gap the outward height at `R` is low (`low`). -/
theorem arcStart_actual (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hS : GW1WalkExit.WalkStageData κ b jumps θ true D) {o : ℕ} {R : ℝ} (ho : o % 2 = 0)
    (hlen : o + 1 < (boundaryWalkSpec b jumps θ true).2.2.length)
    (hA : AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)))
    (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)))
    (hn : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)))
    (hn1 : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1 + 1))) :
    (ExplState.contStep κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) none true =
      if hC : (restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))).Nonempty then
        ExplState.moveAlong (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) true
          ((restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) true) ∧
    stAngle (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) = θ ∧
    stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) ≤ R ∧
    stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) ≤ R ∧
    ((∀ y ∈ restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)), R < y) ∨
      R ∈ restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))) ∧
    ((∀ y ∈ restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)), R < y) →
      rightLim b R + θ * QuantumZipper.chiC κ ≤ -sleLambda κ) := by
  obtain ⟨hmove, hptR, hrec, hgap⟩ := arc_fields_of_first_stage hlen (by omega) hA hpt hn hn1
  have hθ := stAngle_run_walk (κ := κ) (b := b) (jumps := jumps) (θ := θ) (D := D) (right := true) (o + 1)
    (by omega)
  refine ⟨hmove, hθ, hptR, hrec, hgap, fun hg => ?_⟩
  -- the walk is at an outward right threshold (a mark, done or dead adds nothing)
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1) with hs
  have heq : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1 + 1) =
      ExplState.contStep κ b jumps s none true := GW1W.run_succ_walk_cont hlen (by omega)
  rw [heq] at hn1
  have hthr : stStatus s = stThr (some true) ∨
      (stStatus s = stThr none ∧ rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ) := by
    rcases hA with h | h | h | h | ⟨h, hlow⟩
    · rw [contStep_of_arcM h] at hn1; exact absurd hn1 hn
    · rw [contStep_of_done' h] at hn1; exact absurd hn1 hn
    · rw [statePhysicalSet_congr (contStep_pieces b jumps s none true) (contStep_of_dead h true).2.2.2.2] at hn1
      exact absurd hn1 hn
    · exact Or.inl h
    · exact Or.inr ⟨h, by simpa using hlow⟩
  have hlow := low_at_threshold hS ho (by omega) hthr
  exact rightLim_add_le_of_gap hb hθ hptR hlow hg

end InteractingSLE.Theorem14.SB.Lk
