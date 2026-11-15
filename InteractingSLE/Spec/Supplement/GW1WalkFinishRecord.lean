/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkFinishClear

/-!
# GW1: propagating the real-record bound

It suffices to bound the real contacts of each new ordinary piece. The old raw curve
and every earlier connector are handled by induction, without an assumption bounding
their union. This isolates the local real-contact geometry needed from R53 D.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1WalkFinish

open Exist Exist.Staged Exist.StagedLaw GW1WalkChain GW1Bookkeep
open PiecewiseConstantBoundaryData (jumpSet)

theorem realPrefixBound_moveAlong {right : Bool} {root : ℝ} {s : ExplState} {w : ℝ}
    (h : RealPrefixBound right root s)
    (hdir : sideCoord right (stPt s) ≤ sideCoord right w) :
    RealPrefixBound right root (ExplState.moveAlong s right w true) := by
  intro x hx
  rw [statePhysicalSet_moveAlong] at hx
  rw [GW1W.stPt_moveAlong]
  rcases hx with hx | ⟨y, hy, hyx⟩
  · exact (h x hx).trans hdir
  · have heq : y = x := Complex.ofReal_injective hyx
    subst y
    cases right
    · exact neg_le_neg (mem_Icc.1 hy).1
    · exact (mem_Icc.1 hy).2

/-- A classified outward threshold selects an outward interval or the outward ray. -/
theorem contStep_outward_cases {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {right : Bool} {s : ExplState} (h : OutwardThreshold κ b right s) :
    (∃ w, sideCoord right (stPt s) < sideCoord right w ∧
      ExplState.contStep κ b jumps s none right = ExplState.moveAlong s right w true) ∨
    ExplState.contStep κ b jumps s none right = ExplState.moveToEnd s right := by
  classical
  cases right
  · have heq : ExplState.contStep κ b jumps s none false =
        if hC : (GW1W.restartSetL κ b jumps s).Nonempty then
          ExplState.moveAlong s false ((GW1W.restartSetL κ b jumps s).max' hC) true
        else ExplState.moveToEnd s false := by
      rcases h with h | ⟨h, hR, hL⟩
      · exact GW1W.contStep_thr_false b jumps s h false
      · exact GW1W.contStep_thr_none_left b jumps s h hR hL
    split_ifs at heq with hC
    · exact Or.inl ⟨_, neg_lt_neg (Finset.mem_filter.1
        ((GW1W.restartSetL κ b jumps s).max'_mem hC)).2.1, heq⟩
    · exact Or.inr heq
  · have heq : ExplState.contStep κ b jumps s none true =
        if hC : (GW1W.restartSet κ b jumps s).Nonempty then
          ExplState.moveAlong s true ((GW1W.restartSet κ b jumps s).min' hC) true
        else ExplState.moveToEnd s true := by
      rcases h with h | ⟨h, hR⟩
      · exact GW1W.contStep_thr_true' b jumps s h
      · exact GW1W.contStep_thr_none_right b jumps s h hR
    split_ifs at heq with hC
    · exact Or.inl ⟨_, (Finset.mem_filter.1
        ((GW1W.restartSet κ b jumps s).min'_mem hC)).2.1, heq⟩
    · exact Or.inr heq

/-- The real contacts of the new piece, as opposed to the entire retained history. -/
def PieceRealRecordBound (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ k c θ', let spec := boundaryWalkSpec b jumps θ right
    let R := ExplState.run κ b jumps spec D
    (R (k + 1)).2.2.2.1 k = some (c, θ') → stStatus (R (k + 1)) ≠ stDone →
      ∀ x : ℝ, (x : ℂ) ∈ c.tipSet
        (fun r => (D k).1 (min (r : ℝ≥0∞) (min (instrTime spec k) (D k).2)).toNNReal)
        (min (instrTime spec k) (D k).2) → sideCoord right x ≤ sideCoord right (stPt (R (k + 1)))

/-- Induction propagates a per-piece real-contact bound to the complete retained set
at every finite exit. Terminal rays need no bound because they complete the walk. -/
theorem exitRecordBound_of_pieceRealRecordBound {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {θ : ℝ} {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hExit : ∀ n ≤ (jumpSet b jumps).card,
      let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      stStatus (R (2 * n)) ≠ stDone →
        ForwardExit κ b right (R (2 * n)) (R (2 * n + 1)))
    (hP : PieceRealRecordBound κ b jumps θ right D) :
    ∀ n ≤ (jumpSet b jumps).card,
      let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      OutwardThreshold κ b right (R (2 * n + 1)) → RealPrefixBound right 0 (R (2 * n + 1)) := by
  let spec := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps spec D
  have hcont (n : ℕ) (hn : n ≤ (jumpSet b jumps).card) :
      R (2 * n + 1 + 1) = ExplState.contStep κ b jumps (R (2 * n + 1)) none right := by
    apply GW1W.run_succ_walk_cont
    · rw [boundaryWalk_length]; omega
    · omega
  have hflow (n : ℕ) (hn : n ≤ (jumpSet b jumps).card) :
      R (2 * n + 1) = ExplState.flowStep κ b false (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ := by
    apply GW1W.run_succ_walk_flow
    · rw [boundaryWalk_length]; omega
    · omega
  have hbound (n : ℕ) (hn : n ≤ (jumpSet b jumps).card)
      (hOld : RealPrefixBound right 0 (R (2 * n)))
      (hle : sideCoord right (stPt (R (2 * n))) ≤ sideCoord right (stPt (R (2 * n + 1))))
      (hnot : stStatus (R (2 * n + 1)) ≠ stDone) : RealPrefixBound right 0 (R (2 * n + 1)) := by
    rcases GW1W.flowStep_false_cases (κ := κ) (b := b)
      (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ with he | he
    · rw [hflow n hn, he]
      exact hOld
    · have hr : R (2 * n + 1) = ExplState.launch (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ :=
        (hflow n hn).trans he
      have hl : (R (2 * n + 1)).2.2.2.1 (2 * n) = some (stChart (R (2 * n)), θ) := by
        rw [hr, launches_launch, Function.update_self]
      have ht : instrTime (boundaryWalkSpec b jumps θ right) (2 * n) = ⊤ := by
        unfold instrTime
        rw [GW1Conn.getElem?_boundaryWalkSpec, ite_eq_left (by rw [boundaryWalk_length]; omega),
          ite_eq_left (by omega)]
      intro x hx
      have hx' : (x : ℂ) ∈ statePhysicalSet 0 (R (2 * n)) ∪
          (stChart (R (2 * n))).tipSet
            (fun r => (D (2 * n)).1 (min (r : ℝ≥0∞) (D (2 * n)).2).toNNReal)
            (D (2 * n)).2 := by
        simpa only [hr, statePhysicalSet_launch, min_eq_right le_top] using hx
      rcases hx' with hx' | hx'
      · exact (hOld x hx').trans hle
      · apply hP (2 * n) _ θ hl hnot x
        simpa only [ht, min_eq_right le_top] using hx'
  have hEven : ∀ n ≤ (jumpSet b jumps).card + 1,
      stStatus (R (2 * n)) ≠ stDone → RealPrefixBound right 0 (R (2 * n)) := by
    intro n
    induction n with
    | zero => intro _ _; exact realPrefixBound_init right 0
    | succ n ih =>
      intro hn hnot
      have hn' : n ≤ (jumpSet b jumps).card := by omega
      have hr : R (2 * (n + 1)) =
          ExplState.contStep κ b jumps (R (2 * n + 1)) none right := by
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
        exact hcont n hn'
      have hn0 : stStatus (R (2 * n)) ≠ stDone := by
        intro hd
        have h1 : R (2 * n + 1) = R (2 * n) := done_run_succ spec D hd
        apply hnot
        rw [hr, h1, contStep_of_done hd]
        exact hd
      rcases hExit n hn' hn0 with hd | ⟨hle, hthr⟩
      · exact False.elim (hnot (by rw [hr, contStep_of_done hd]; exact hd))
      · have hnt : stStatus (R (2 * n + 1)) ≠ stDone := by
          intro hd
          exact hnot (by rw [hr, contStep_of_done hd]; exact hd)
        have hb := hbound n hn' (ih (by omega) hn0) hle hnt
        rcases contStep_outward_cases (jumps := jumps) hthr with ⟨w, hw, he⟩ | he
        · rw [hr, he]
          exact realPrefixBound_moveAlong hb hw.le
        · apply False.elim
          apply hnot
          rw [hr, he]
          cases R (2 * n + 1)
          rfl
  intro n hn
  dsimp only
  intro hthr
  change RealPrefixBound right 0 (R (2 * n + 1))
  have hnt : stStatus (R (2 * n + 1)) ≠ stDone := by
    cases right <;> rcases hthr with h | ⟨h, -⟩ <;> rw [h] <;> intro he <;> cases he
  have hn0 : stStatus (R (2 * n)) ≠ stDone := by
    intro hd
    have he : R (2 * n + 1) = R (2 * n) := done_run_succ spec D hd
    exact hnt (by rw [he]; exact hd)
  have hle := (hExit n hn hn0).resolve_left hnt
  exact hbound n hn (hEven n (by omega) hn0) hle.1 hnt

theorem walkConnectorClearance_of_pieceRealRecordBound {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {θ : ℝ} {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hExit : ∀ n ≤ (jumpSet b jumps).card,
      let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      stStatus (R (2 * n)) ≠ stDone →
        ForwardExit κ b right (R (2 * n)) (R (2 * n + 1)))
    (hP : PieceRealRecordBound κ b jumps θ right D) :
    WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D :=
  walkConnectorClearance_of_exitRecordBound D hExit
    (exitRecordBound_of_pieceRealRecordBound D hExit hP)

end InteractingSLE.Theorem14.GW1WalkFinish
