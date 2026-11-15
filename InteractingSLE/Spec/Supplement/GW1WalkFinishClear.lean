/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkFinishRun

/-!
# GW1: connector clearance from the D.4 real-record bound

The only geometric input is the outward bound on retained real contacts at a finite
ordinary exit. All connector cases, including terminal rays and steps past completion,
are handled using the frozen run semantics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1WalkFinish

open Exist Exist.Staged Exist.StagedLaw GW1WalkChain
open PiecewiseConstantBoundaryData (jumpSet)

/-- The connector clauses for a single actual transition. -/
def StepConnectorClearance (root : ℝ) (s t : ExplState) : Prop :=
  (∀ r x, t = ExplState.moveAlong s r x true →
    ConnectorClearance root s (((↑) : ℝ → ℂ) ''
      (if r then Icc (stPt s) x else Icc x (stPt s)))) ∧
  (∀ r, t = ExplState.moveToEnd s r →
    ConnectorClearance root s (range (realRay r (stPt s))))

theorem stepConnectorClearance_of_arcs_eq {root : ℝ} {s t : ExplState}
    (h : t.2.1 = s.2.1) : StepConnectorClearance root s t := by
  constructor
  · intro r x he
    have hl := congrArg List.length h
    rw [he] at hl
    have heq : (ExplState.moveAlong s r x true).2.1.length = s.2.1.length + 1 := by
      cases s
      simp only [ExplState.moveAlong, List.length_append, List.length_singleton]
    rw [heq] at hl
    omega
  · intro r he
    have hl := congrArg List.length h
    rw [he] at hl
    have heq : (ExplState.moveToEnd s r).2.1.length = s.2.1.length + 1 := by
      cases s
      simp only [ExplState.moveToEnd, List.length_append, List.length_singleton]
    rw [heq] at hl
    omega

theorem stepConnectorClearance_moveAlong {root : ℝ} {s : ExplState} {right : Bool}
    (h : RealPrefixBound right root s) (w : ℝ) :
    StepConnectorClearance root s (ExplState.moveAlong s right w true) := by
  constructor
  · intro r x he
    have ha := congrArg (fun t : ExplState => t.2.1) he
    have heq : (if right then Icc (stPt s) w else Icc w (stPt s)) =
        (if r then Icc (stPt s) x else Icc x (stPt s)) := by
      cases s
      exact List.singleton_injective (List.append_cancel_left ha)
    rw [← heq]
    exact connectorClearance_interval_of_realPrefixBound h w
  · intro r he
    have hs := congrArg stStatus he
    cases s
    cases hs

theorem stepConnectorClearance_moveToEnd {root : ℝ} {s : ExplState} {right : Bool}
    (h : RealPrefixBound right root s) :
    StepConnectorClearance root s (ExplState.moveToEnd s right) := by
  constructor
  · intro r x he
    have hs := congrArg stStatus he
    cases s
    cases hs
  · intro r he
    have ha := congrArg (fun t : ExplState => t.2.1) he
    have heq : (if right then Ici (stPt s) else Iic (stPt s)) =
        (if r then Ici (stPt s) else Iic (stPt s)) := by
      cases s
      exact List.singleton_injective (List.append_cancel_left ha)
    rw [range_realRay, ← heq, ← range_realRay]
    exact connectorClearance_ray_of_realPrefixBound h

theorem stepConnectorClearance_contStep {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {root : ℝ} {s : ExplState} {right : Bool}
    (h : OutwardThreshold κ b right s) (hB : RealPrefixBound right root s) :
    StepConnectorClearance root s (ExplState.contStep κ b jumps s none right) := by
  classical
  cases right
  · have heq : ExplState.contStep κ b jumps s none false =
        if hC : (GW1W.restartSetL κ b jumps s).Nonempty then
          ExplState.moveAlong s false ((GW1W.restartSetL κ b jumps s).max' hC) true
        else ExplState.moveToEnd s false := by
      rcases h with h | ⟨h, hR, hL⟩
      · exact GW1W.contStep_thr_false b jumps s h false
      · exact GW1W.contStep_thr_none_left b jumps s h hR hL
    rw [heq]
    split_ifs
    · exact stepConnectorClearance_moveAlong hB _
    · exact stepConnectorClearance_moveToEnd hB
  · have heq : ExplState.contStep κ b jumps s none true =
        if hC : (GW1W.restartSet κ b jumps s).Nonempty then
          ExplState.moveAlong s true ((GW1W.restartSet κ b jumps s).min' hC) true
        else ExplState.moveToEnd s true := by
      rcases h with h | ⟨h, hR⟩
      · exact GW1W.contStep_thr_true' b jumps s h
      · exact GW1W.contStep_thr_none_right b jumps s h hR
    rw [heq]
    split_ifs
    · exact stepConnectorClearance_moveAlong hB _
    · exact stepConnectorClearance_moveToEnd hB

/-- Clearance for the entire run from the local exit classification and D.4's bound
on retained real contacts. No clearance or completion premise occurs in these inputs. -/
theorem walkConnectorClearance_of_exitRecordBound {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {θ : ℝ} {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hExit : ∀ n ≤ (jumpSet b jumps).card,
      let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      stStatus (R (2 * n)) ≠ stDone →
        ForwardExit κ b right (R (2 * n)) (R (2 * n + 1)))
    (hB : ∀ n ≤ (jumpSet b jumps).card,
      let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      OutwardThreshold κ b right (R (2 * n + 1)) → RealPrefixBound right 0 (R (2 * n + 1))) :
    WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D := by
  let spec := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps spec D
  intro k
  change StepConnectorClearance 0 (R k) (R (k + 1))
  by_cases hk : k < spec.2.2.length
  swap
  · apply stepConnectorClearance_of_arcs_eq
    have he : R (k + 1) = R k := by
      dsimp only [R]
      rw [run_succ, List.getElem?_eq_none (by omega)]
    rw [he]
  rcases Nat.mod_two_eq_zero_or_one k with hev | hodd
  · apply stepConnectorClearance_of_arcs_eq
    have hf : R (k + 1) = ExplState.flowStep κ b false (R k) k (D k) θ ⊤ :=
      GW1W.run_succ_walk_flow hk hev
    rw [hf]
    rcases GW1W.flowStep_false_cases (κ := κ) (b := b) (R k) k (D k) θ ⊤ with he | he
    · rw [he]
    · rw [he]
      obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := R k
      unfold ExplState.launch
      dsimp only
      split_ifs <;> try rfl
      all_goals (rcases status with _ | _ | _ | _ | _ | _ <;> rfl)
  · let n := k / 2
    have hkn : k = 2 * n + 1 := by omega
    have hn : n ≤ (jumpSet b jumps).card := by
      rw [boundaryWalk_length] at hk
      omega
    have hc : R (k + 1) = ExplState.contStep κ b jumps (R k) none right :=
      GW1W.run_succ_walk_cont hk hodd
    rw [hc]
    by_cases hd : stStatus (R (2 * n)) = stDone
    · have he : R (2 * n + 1) = R (2 * n) := done_run_succ spec D hd
      rw [contStep_of_done (show stStatus (R k) = stDone by rw [hkn, he]; exact hd)]
      exact stepConnectorClearance_of_arcs_eq rfl
    · rcases hExit n hn hd with hd | ⟨-, hthr⟩
      · rw [contStep_of_done (show stStatus (R k) = stDone by rw [hkn]; exact hd)]
        exact stepConnectorClearance_of_arcs_eq rfl
      · rw [hkn]
        exact stepConnectorClearance_contStep hthr (hB n hn hthr)

end InteractingSLE.Theorem14.GW1WalkFinish
